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
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value)}};
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
lean_object* v___y_246_; lean_object* v_fileName_255_; lean_object* v_fileMap_256_; lean_object* v_options_257_; lean_object* v_currRecDepth_258_; lean_object* v_maxRecDepth_259_; lean_object* v_ref_260_; lean_object* v_currNamespace_261_; lean_object* v_openDecls_262_; lean_object* v_initHeartbeats_263_; lean_object* v_maxHeartbeats_264_; lean_object* v_quotContext_265_; lean_object* v_currMacroScope_266_; uint8_t v_diag_267_; lean_object* v_cancelTk_x3f_268_; uint8_t v_suppressElabErrors_269_; lean_object* v_inheritedTraceOptions_270_; uint8_t v___x_271_; 
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
v___x_271_ = lean_nat_dec_eq(v_currRecDepth_258_, v_maxRecDepth_259_);
if (v___x_271_ == 0)
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
else
{
lean_object* v___x_276_; 
lean_dec_ref(v_x_240_);
lean_inc(v_ref_260_);
v___x_276_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_260_);
v___y_246_ = v___x_276_;
goto v___jp_245_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_277_, v___y_278_, v___y_279_, v___y_280_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_283_, lean_object* v_x_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_apply_1(v_x_284_, lean_box(0));
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_290_, lean_object* v_x_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(v_00_u03b1_290_, v_x_291_, v___y_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_296_, lean_object* v_x_297_){
_start:
{
if (lean_obj_tag(v_x_297_) == 0)
{
lean_object* v___x_298_; 
v___x_298_ = lean_box(0);
return v___x_298_;
}
else
{
lean_object* v_key_299_; lean_object* v_value_300_; lean_object* v_tail_301_; uint8_t v___x_302_; 
v_key_299_ = lean_ctor_get(v_x_297_, 0);
v_value_300_ = lean_ctor_get(v_x_297_, 1);
v_tail_301_ = lean_ctor_get(v_x_297_, 2);
v___x_302_ = l_Lean_ExprStructEq_beq(v_key_299_, v_a_296_);
if (v___x_302_ == 0)
{
v_x_297_ = v_tail_301_;
goto _start;
}
else
{
lean_object* v___x_304_; 
lean_inc(v_value_300_);
v___x_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_304_, 0, v_value_300_);
return v___x_304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_305_, lean_object* v_x_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_305_, v_x_306_);
lean_dec(v_x_306_);
lean_dec_ref(v_a_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(lean_object* v_m_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_buckets_310_; lean_object* v___x_311_; uint64_t v___x_312_; uint64_t v___x_313_; uint64_t v___x_314_; uint64_t v_fold_315_; uint64_t v___x_316_; uint64_t v___x_317_; uint64_t v___x_318_; size_t v___x_319_; size_t v___x_320_; size_t v___x_321_; size_t v___x_322_; size_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_buckets_310_ = lean_ctor_get(v_m_308_, 1);
v___x_311_ = lean_array_get_size(v_buckets_310_);
v___x_312_ = l_Lean_ExprStructEq_hash(v_a_309_);
v___x_313_ = 32ULL;
v___x_314_ = lean_uint64_shift_right(v___x_312_, v___x_313_);
v_fold_315_ = lean_uint64_xor(v___x_312_, v___x_314_);
v___x_316_ = 16ULL;
v___x_317_ = lean_uint64_shift_right(v_fold_315_, v___x_316_);
v___x_318_ = lean_uint64_xor(v_fold_315_, v___x_317_);
v___x_319_ = lean_uint64_to_usize(v___x_318_);
v___x_320_ = lean_usize_of_nat(v___x_311_);
v___x_321_ = ((size_t)1ULL);
v___x_322_ = lean_usize_sub(v___x_320_, v___x_321_);
v___x_323_ = lean_usize_land(v___x_319_, v___x_322_);
v___x_324_ = lean_array_uget_borrowed(v_buckets_310_, v___x_323_);
v___x_325_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_309_, v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_326_, v_a_327_);
lean_dec_ref(v_a_327_);
lean_dec_ref(v_m_326_);
return v_res_328_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_329_; lean_object* v_dummy_330_; 
v___x_329_ = lean_box(0);
v_dummy_330_ = l_Lean_Expr_sort___override(v___x_329_);
return v_dummy_330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(lean_object* v_pre_331_, lean_object* v_post_332_, size_t v_sz_333_, size_t v_i_334_, lean_object* v_bs_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
uint8_t v___x_340_; 
v___x_340_ = lean_usize_dec_lt(v_i_334_, v_sz_333_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
lean_dec_ref(v_post_332_);
lean_dec_ref(v_pre_331_);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v_bs_335_);
return v___x_341_;
}
else
{
lean_object* v_v_342_; lean_object* v___x_343_; 
v_v_342_ = lean_array_uget_borrowed(v_bs_335_, v_i_334_);
lean_inc(v_v_342_);
lean_inc_ref(v_post_332_);
lean_inc_ref(v_pre_331_);
v___x_343_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_331_, v_post_332_, v_v_342_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_345_; lean_object* v_bs_x27_346_; size_t v___x_347_; size_t v___x_348_; lean_object* v___x_349_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_344_);
lean_dec_ref(v___x_343_);
v___x_345_ = lean_unsigned_to_nat(0u);
v_bs_x27_346_ = lean_array_uset(v_bs_335_, v_i_334_, v___x_345_);
v___x_347_ = ((size_t)1ULL);
v___x_348_ = lean_usize_add(v_i_334_, v___x_347_);
v___x_349_ = lean_array_uset(v_bs_x27_346_, v_i_334_, v_a_344_);
v_i_334_ = v___x_348_;
v_bs_335_ = v___x_349_;
goto _start;
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_dec_ref(v_bs_335_);
lean_dec_ref(v_post_332_);
lean_dec_ref(v_pre_331_);
v_a_351_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_343_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_343_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(lean_object* v_pre_359_, lean_object* v_post_360_, lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v_x_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
if (lean_obj_tag(v_x_361_) == 5)
{
lean_object* v_fn_368_; lean_object* v_arg_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_fn_368_ = lean_ctor_get(v_x_361_, 0);
lean_inc_ref(v_fn_368_);
v_arg_369_ = lean_ctor_get(v_x_361_, 1);
lean_inc_ref(v_arg_369_);
lean_dec_ref(v_x_361_);
v___x_370_ = lean_array_set(v_x_362_, v_x_363_, v_arg_369_);
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_nat_sub(v_x_363_, v___x_371_);
lean_dec(v_x_363_);
v_x_361_ = v_fn_368_;
v_x_362_ = v___x_370_;
v_x_363_ = v___x_372_;
goto _start;
}
else
{
lean_object* v___x_374_; 
lean_dec(v_x_363_);
lean_inc_ref(v_post_360_);
lean_inc_ref(v_pre_359_);
v___x_374_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_359_, v_post_360_, v_x_361_, v___y_364_, v___y_365_, v___y_366_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; size_t v_sz_376_; size_t v___x_377_; lean_object* v___x_378_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref(v___x_374_);
v_sz_376_ = lean_array_size(v_x_362_);
v___x_377_ = ((size_t)0ULL);
lean_inc_ref(v_post_360_);
lean_inc_ref(v_pre_359_);
v___x_378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_359_, v_post_360_, v_sz_376_, v___x_377_, v_x_362_, v___y_364_, v___y_365_, v___y_366_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
lean_dec_ref(v___x_378_);
v___x_380_ = l_Lean_mkAppN(v_a_375_, v_a_379_);
lean_dec(v_a_379_);
v___x_381_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_359_, v_post_360_, v___x_380_, v___y_364_, v___y_365_, v___y_366_);
return v___x_381_;
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_dec(v_a_375_);
lean_dec_ref(v_post_360_);
lean_dec_ref(v_pre_359_);
v_a_382_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_378_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_378_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
else
{
lean_dec_ref(v_x_362_);
lean_dec_ref(v_post_360_);
lean_dec_ref(v_pre_359_);
return v___x_374_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(lean_object* v_pre_390_, lean_object* v_e_391_, lean_object* v_post_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; uint8_t v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; uint8_t v___y_405_; lean_object* v___y_415_; uint8_t v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; uint8_t v___y_420_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; uint8_t v___y_431_; lean_object* v___y_432_; uint8_t v___y_433_; lean_object* v___x_440_; 
lean_inc_ref(v_pre_390_);
lean_inc(v___y_395_);
lean_inc_ref(v___y_394_);
lean_inc_ref(v_e_391_);
v___x_440_ = lean_apply_4(v_pre_390_, v_e_391_, v___y_394_, v___y_395_, lean_box(0));
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_530_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_530_ == 0)
{
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_530_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_530_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___y_446_; 
switch(lean_obj_tag(v_a_441_))
{
case 0:
{
lean_object* v_e_520_; lean_object* v___x_522_; 
lean_dec_ref(v_post_392_);
lean_dec_ref(v_e_391_);
lean_dec_ref(v_pre_390_);
v_e_520_ = lean_ctor_get(v_a_441_, 0);
lean_inc_ref(v_e_520_);
lean_dec_ref(v_a_441_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v_e_520_);
v___x_522_ = v___x_443_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_e_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
case 1:
{
lean_object* v_e_524_; lean_object* v___x_525_; 
lean_del_object(v___x_443_);
lean_dec_ref(v_e_391_);
v_e_524_ = lean_ctor_get(v_a_441_, 0);
lean_inc_ref(v_e_524_);
lean_dec_ref(v_a_441_);
lean_inc_ref(v_post_392_);
lean_inc_ref(v_pre_390_);
v___x_525_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_390_, v_post_392_, v_e_524_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_527_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref(v___x_525_);
v___x_527_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v_a_526_, v___y_393_, v___y_394_, v___y_395_);
return v___x_527_;
}
else
{
lean_dec_ref(v_post_392_);
lean_dec_ref(v_pre_390_);
return v___x_525_;
}
}
default: 
{
lean_object* v_e_x3f_528_; 
lean_del_object(v___x_443_);
v_e_x3f_528_ = lean_ctor_get(v_a_441_, 0);
lean_inc(v_e_x3f_528_);
lean_dec_ref(v_a_441_);
if (lean_obj_tag(v_e_x3f_528_) == 0)
{
v___y_446_ = v_e_391_;
goto v___jp_445_;
}
else
{
lean_object* v_val_529_; 
lean_dec_ref(v_e_391_);
v_val_529_ = lean_ctor_get(v_e_x3f_528_, 0);
lean_inc(v_val_529_);
lean_dec_ref(v_e_x3f_528_);
v___y_446_ = v_val_529_;
goto v___jp_445_;
}
}
}
v___jp_445_:
{
switch(lean_obj_tag(v___y_446_))
{
case 7:
{
lean_object* v_binderName_447_; lean_object* v_binderType_448_; lean_object* v_body_449_; uint8_t v_binderInfo_450_; lean_object* v___x_451_; 
v_binderName_447_ = lean_ctor_get(v___y_446_, 0);
lean_inc(v_binderName_447_);
v_binderType_448_ = lean_ctor_get(v___y_446_, 1);
v_body_449_ = lean_ctor_get(v___y_446_, 2);
v_binderInfo_450_ = lean_ctor_get_uint8(v___y_446_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_448_);
lean_inc_ref(v_post_392_);
lean_inc_ref(v_pre_390_);
v___x_451_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_390_, v_post_392_, v_binderType_448_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_453_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_452_);
lean_dec_ref(v___x_451_);
lean_inc_ref(v_body_449_);
lean_inc_ref(v_post_392_);
lean_inc_ref(v_pre_390_);
v___x_453_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_390_, v_post_392_, v_body_449_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; size_t v___x_455_; size_t v___x_456_; uint8_t v___x_457_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
lean_dec_ref(v___x_453_);
v___x_455_ = lean_ptr_addr(v_binderType_448_);
v___x_456_ = lean_ptr_addr(v_a_452_);
v___x_457_ = lean_usize_dec_eq(v___x_455_, v___x_456_);
if (v___x_457_ == 0)
{
v___y_428_ = v_a_454_;
v___y_429_ = v_a_452_;
v___y_430_ = v___y_446_;
v___y_431_ = v_binderInfo_450_;
v___y_432_ = v_binderName_447_;
v___y_433_ = v___x_457_;
goto v___jp_427_;
}
else
{
size_t v___x_458_; size_t v___x_459_; uint8_t v___x_460_; 
v___x_458_ = lean_ptr_addr(v_body_449_);
v___x_459_ = lean_ptr_addr(v_a_454_);
v___x_460_ = lean_usize_dec_eq(v___x_458_, v___x_459_);
v___y_428_ = v_a_454_;
v___y_429_ = v_a_452_;
v___y_430_ = v___y_446_;
v___y_431_ = v_binderInfo_450_;
v___y_432_ = v_binderName_447_;
v___y_433_ = v___x_460_;
goto v___jp_427_;
}
}
else
{
lean_dec(v_a_452_);
lean_dec(v_binderName_447_);
lean_dec_ref(v___y_446_);
lean_dec_ref(v_post_392_);
lean_dec_ref(v_pre_390_);
return v___x_453_;
}
}
else
{
lean_dec(v_binderName_447_);
lean_dec_ref(v___y_446_);
lean_dec_ref(v_post_392_);
lean_dec_ref(v_pre_390_);
return v___x_451_;
}
}
case 6:
{
lean_object* v_binderName_461_; lean_object* v_binderType_462_; lean_object* v_body_463_; uint8_t v_binderInfo_464_; lean_object* v___x_465_; 
v_binderName_461_ = lean_ctor_get(v___y_446_, 0);
lean_inc(v_binderName_461_);
v_binderType_462_ = lean_ctor_get(v___y_446_, 1);
v_body_463_ = lean_ctor_get(v___y_446_, 2);
v_binderInfo_464_ = lean_ctor_get_uint8(v___y_446_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_462_);
lean_inc_ref(v_post_392_);
lean_inc_ref(v_pre_390_);
v___x_465_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_390_, v_post_392_, v_binderType_462_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_467_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_466_);
lean_dec_ref(v___x_465_);
lean_inc_ref(v_body_463_);
lean_inc_ref(v_post_392_);
lean_inc_ref(v_pre_390_);
v___x_467_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_390_, v_post_392_, v_body_463_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; size_t v___x_469_; size_t v___x_470_; uint8_t v___x_471_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref(v___x_467_);
v___x_469_ = lean_ptr_addr(v_binderType_462_);
v___x_470_ = lean_ptr_addr(v_a_466_);
v___x_471_ = lean_usize_dec_eq(v___x_469_, v___x_470_);
if (v___x_471_ == 0)
{
v___y_415_ = v_binderName_461_;
v___y_416_ = v_binderInfo_464_;
v___y_417_ = v_a_468_;
v___y_418_ = v_a_466_;
v___y_419_ = v___y_446_;
v___y_420_ = v___x_471_;
goto v___jp_414_;
}
else
{
size_t v___x_472_; size_t v___x_473_; uint8_t v___x_474_; 
v___x_472_ = lean_ptr_addr(v_body_463_);
v___x_473_ = lean_ptr_addr(v_a_468_);
v___x_474_ = lean_usize_dec_eq(v___x_472_, v___x_473_);
v___y_415_ = v_binderName_461_;
v___y_416_ = v_binderInfo_464_;
v___y_417_ = v_a_468_;
v___y_418_ = v_a_466_;
v___y_419_ = v___y_446_;
v___y_420_ = v___x_474_;
goto v___jp_414_;
}
}
else
{
lean_dec(v_a_466_);
lean_dec_ref(v___y_446_);
lean_dec(v_binderName_461_);
lean_dec_ref(v_post_392_);
lean_dec_ref(v_pre_390_);
return v___x_467_;
}
}
else
{
lean_dec_ref(v___y_446_);
lean_dec(v_binderName_461_);
lean_dec_ref(v_post_392_);
lean_dec_ref(v_pre_390_);
return v___x_465_;
}
}
case 8:
{
lean_object* v_declName_475_; lean_object* v_type_476_; lean_object* v_value_477_; lean_object* v_body_478_; uint8_t v_nondep_479_; lean_object* v___x_480_; 
v_declName_475_ = lean_ctor_get(v___y_446_, 0);
lean_inc(v_declName_475_);
v_type_476_ = lean_ctor_get(v___y_446_, 1);
v_value_477_ = lean_ctor_get(v___y_446_, 2);
v_body_478_ = lean_ctor_get(v___y_446_, 3);
lean_inc_ref(v_body_478_);
v_nondep_479_ = lean_ctor_get_uint8(v___y_446_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_476_);
lean_inc_ref(v_post_392_);
lean_inc_ref(v_pre_390_);
v___x_480_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_390_, v_post_392_, v_type_476_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_482_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_481_);
lean_dec_ref(v___x_480_);
lean_inc_ref(v_value_477_);
lean_inc_ref(v_post_392_);
lean_inc_ref(v_pre_390_);
v___x_482_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_390_, v_post_392_, v_value_477_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_484_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref(v___x_482_);
lean_inc_ref(v_body_478_);
lean_inc_ref(v_post_392_);
lean_inc_ref(v_pre_390_);
v___x_484_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_390_, v_post_392_, v_body_478_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; size_t v___x_486_; size_t v___x_487_; uint8_t v___x_488_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref(v___x_484_);
v___x_486_ = lean_ptr_addr(v_type_476_);
v___x_487_ = lean_ptr_addr(v_a_481_);
v___x_488_ = lean_usize_dec_eq(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
v___y_398_ = v_a_481_;
v___y_399_ = v_body_478_;
v___y_400_ = v_a_483_;
v___y_401_ = v___y_446_;
v___y_402_ = v_nondep_479_;
v___y_403_ = v_a_485_;
v___y_404_ = v_declName_475_;
v___y_405_ = v___x_488_;
goto v___jp_397_;
}
else
{
size_t v___x_489_; size_t v___x_490_; uint8_t v___x_491_; 
v___x_489_ = lean_ptr_addr(v_value_477_);
v___x_490_ = lean_ptr_addr(v_a_483_);
v___x_491_ = lean_usize_dec_eq(v___x_489_, v___x_490_);
v___y_398_ = v_a_481_;
v___y_399_ = v_body_478_;
v___y_400_ = v_a_483_;
v___y_401_ = v___y_446_;
v___y_402_ = v_nondep_479_;
v___y_403_ = v_a_485_;
v___y_404_ = v_declName_475_;
v___y_405_ = v___x_491_;
goto v___jp_397_;
}
}
else
{
lean_dec(v_a_483_);
lean_dec(v_a_481_);
lean_dec_ref(v_body_478_);
lean_dec_ref(v___y_446_);
lean_dec(v_declName_475_);
lean_dec_ref(v_post_392_);
lean_dec_ref(v_pre_390_);
return v___x_484_;
}
}
else
{
lean_dec(v_a_481_);
lean_dec_ref(v_body_478_);
lean_dec_ref(v___y_446_);
lean_dec(v_declName_475_);
lean_dec_ref(v_post_392_);
lean_dec_ref(v_pre_390_);
return v___x_482_;
}
}
else
{
lean_dec_ref(v_body_478_);
lean_dec(v_declName_475_);
lean_dec_ref(v___y_446_);
lean_dec_ref(v_post_392_);
lean_dec_ref(v_pre_390_);
return v___x_480_;
}
}
case 5:
{
lean_object* v_dummy_492_; lean_object* v_nargs_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v_dummy_492_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_493_ = l_Lean_Expr_getAppNumArgs(v___y_446_);
lean_inc(v_nargs_493_);
v___x_494_ = lean_mk_array(v_nargs_493_, v_dummy_492_);
v___x_495_ = lean_unsigned_to_nat(1u);
v___x_496_ = lean_nat_sub(v_nargs_493_, v___x_495_);
lean_dec(v_nargs_493_);
v___x_497_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_390_, v_post_392_, v___y_446_, v___x_494_, v___x_496_, v___y_393_, v___y_394_, v___y_395_);
return v___x_497_;
}
case 10:
{
lean_object* v_data_498_; lean_object* v_expr_499_; lean_object* v___x_500_; 
v_data_498_ = lean_ctor_get(v___y_446_, 0);
v_expr_499_ = lean_ctor_get(v___y_446_, 1);
lean_inc_ref(v_expr_499_);
lean_inc_ref(v_post_392_);
lean_inc_ref(v_pre_390_);
v___x_500_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_390_, v_post_392_, v_expr_499_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; size_t v___x_502_; size_t v___x_503_; uint8_t v___x_504_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref(v___x_500_);
v___x_502_ = lean_ptr_addr(v_expr_499_);
v___x_503_ = lean_ptr_addr(v_a_501_);
v___x_504_ = lean_usize_dec_eq(v___x_502_, v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; 
lean_inc(v_data_498_);
lean_dec_ref(v___y_446_);
v___x_505_ = l_Lean_Expr_mdata___override(v_data_498_, v_a_501_);
v___x_506_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___x_505_, v___y_393_, v___y_394_, v___y_395_);
return v___x_506_;
}
else
{
lean_object* v___x_507_; 
lean_dec(v_a_501_);
v___x_507_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___y_446_, v___y_393_, v___y_394_, v___y_395_);
return v___x_507_;
}
}
else
{
lean_dec_ref(v___y_446_);
lean_dec_ref(v_post_392_);
lean_dec_ref(v_pre_390_);
return v___x_500_;
}
}
case 11:
{
lean_object* v_typeName_508_; lean_object* v_idx_509_; lean_object* v_struct_510_; lean_object* v___x_511_; 
v_typeName_508_ = lean_ctor_get(v___y_446_, 0);
v_idx_509_ = lean_ctor_get(v___y_446_, 1);
v_struct_510_ = lean_ctor_get(v___y_446_, 2);
lean_inc_ref(v_struct_510_);
lean_inc_ref(v_post_392_);
lean_inc_ref(v_pre_390_);
v___x_511_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_390_, v_post_392_, v_struct_510_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; size_t v___x_513_; size_t v___x_514_; uint8_t v___x_515_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref(v___x_511_);
v___x_513_ = lean_ptr_addr(v_struct_510_);
v___x_514_ = lean_ptr_addr(v_a_512_);
v___x_515_ = lean_usize_dec_eq(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; 
lean_inc(v_idx_509_);
lean_inc(v_typeName_508_);
lean_dec_ref(v___y_446_);
v___x_516_ = l_Lean_Expr_proj___override(v_typeName_508_, v_idx_509_, v_a_512_);
v___x_517_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___x_516_, v___y_393_, v___y_394_, v___y_395_);
return v___x_517_;
}
else
{
lean_object* v___x_518_; 
lean_dec(v_a_512_);
v___x_518_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___y_446_, v___y_393_, v___y_394_, v___y_395_);
return v___x_518_;
}
}
else
{
lean_dec_ref(v___y_446_);
lean_dec_ref(v_post_392_);
lean_dec_ref(v_pre_390_);
return v___x_511_;
}
}
default: 
{
lean_object* v___x_519_; 
v___x_519_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___y_446_, v___y_393_, v___y_394_, v___y_395_);
return v___x_519_;
}
}
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec_ref(v_post_392_);
lean_dec_ref(v_e_391_);
lean_dec_ref(v_pre_390_);
v_a_531_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_440_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_440_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
v___jp_397_:
{
if (v___y_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec_ref(v___y_401_);
lean_dec_ref(v___y_399_);
v___x_406_ = l_Lean_Expr_letE___override(v___y_404_, v___y_398_, v___y_400_, v___y_403_, v___y_402_);
v___x_407_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___x_406_, v___y_393_, v___y_394_, v___y_395_);
return v___x_407_;
}
else
{
size_t v___x_408_; size_t v___x_409_; uint8_t v___x_410_; 
v___x_408_ = lean_ptr_addr(v___y_399_);
lean_dec_ref(v___y_399_);
v___x_409_ = lean_ptr_addr(v___y_403_);
v___x_410_ = lean_usize_dec_eq(v___x_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec_ref(v___y_401_);
v___x_411_ = l_Lean_Expr_letE___override(v___y_404_, v___y_398_, v___y_400_, v___y_403_, v___y_402_);
v___x_412_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___x_411_, v___y_393_, v___y_394_, v___y_395_);
return v___x_412_;
}
else
{
lean_object* v___x_413_; 
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec_ref(v___y_400_);
lean_dec_ref(v___y_398_);
v___x_413_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___y_401_, v___y_393_, v___y_394_, v___y_395_);
return v___x_413_;
}
}
}
v___jp_414_:
{
if (v___y_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec_ref(v___y_419_);
v___x_421_ = l_Lean_Expr_lam___override(v___y_415_, v___y_418_, v___y_417_, v___y_416_);
v___x_422_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___x_421_, v___y_393_, v___y_394_, v___y_395_);
return v___x_422_;
}
else
{
uint8_t v___x_423_; 
v___x_423_ = l_Lean_instBEqBinderInfo_beq(v___y_416_, v___y_416_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec_ref(v___y_419_);
v___x_424_ = l_Lean_Expr_lam___override(v___y_415_, v___y_418_, v___y_417_, v___y_416_);
v___x_425_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___x_424_, v___y_393_, v___y_394_, v___y_395_);
return v___x_425_;
}
else
{
lean_object* v___x_426_; 
lean_dec_ref(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_415_);
v___x_426_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___y_419_, v___y_393_, v___y_394_, v___y_395_);
return v___x_426_;
}
}
}
v___jp_427_:
{
if (v___y_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec_ref(v___y_430_);
v___x_434_ = l_Lean_Expr_forallE___override(v___y_432_, v___y_429_, v___y_428_, v___y_431_);
v___x_435_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___x_434_, v___y_393_, v___y_394_, v___y_395_);
return v___x_435_;
}
else
{
uint8_t v___x_436_; 
v___x_436_ = l_Lean_instBEqBinderInfo_beq(v___y_431_, v___y_431_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec_ref(v___y_430_);
v___x_437_ = l_Lean_Expr_forallE___override(v___y_432_, v___y_429_, v___y_428_, v___y_431_);
v___x_438_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___x_437_, v___y_393_, v___y_394_, v___y_395_);
return v___x_438_;
}
else
{
lean_object* v___x_439_; 
lean_dec(v___y_432_);
lean_dec_ref(v___y_429_);
lean_dec_ref(v___y_428_);
v___x_439_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___y_430_, v___y_393_, v___y_394_, v___y_395_);
return v___x_439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed(lean_object* v_pre_539_, lean_object* v_e_540_, lean_object* v_post_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(v_pre_539_, v_e_540_, v_post_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(lean_object* v_pre_547_, lean_object* v_post_548_, lean_object* v_e_549_, lean_object* v_a_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_inc(v_a_550_);
v___x_554_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_554_, 0, lean_box(0));
lean_closure_set(v___x_554_, 1, lean_box(0));
lean_closure_set(v___x_554_, 2, v_a_550_);
v___x_555_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___x_554_, v___y_551_, v___y_552_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_586_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_586_ == 0)
{
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_586_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_586_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; 
v___x_560_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_a_556_, v_e_549_);
lean_dec(v_a_556_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v___f_561_; lean_object* v___x_562_; 
lean_del_object(v___x_558_);
lean_inc_ref(v_e_549_);
v___f_561_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed), 7, 3);
lean_closure_set(v___f_561_, 0, v_pre_547_);
lean_closure_set(v___f_561_, 1, v_e_549_);
lean_closure_set(v___f_561_, 2, v_post_548_);
v___x_562_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v___f_561_, v_a_550_, v___y_551_, v___y_552_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___f_564_; lean_object* v___x_565_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc_n(v_a_563_, 2);
lean_dec_ref(v___x_562_);
lean_inc(v_a_550_);
v___f_564_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_564_, 0, v_a_550_);
lean_closure_set(v___f_564_, 1, v_e_549_);
lean_closure_set(v___f_564_, 2, v_a_563_);
v___x_565_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___f_564_, v___y_551_, v___y_552_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_572_ == 0)
{
lean_object* v_unused_573_; 
v_unused_573_ = lean_ctor_get(v___x_565_, 0);
lean_dec(v_unused_573_);
v___x_567_ = v___x_565_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_dec(v___x_565_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v_a_563_);
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_563_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_dec(v_a_563_);
v_a_574_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_565_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_565_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
else
{
lean_dec_ref(v_e_549_);
return v___x_562_;
}
}
else
{
lean_object* v_val_582_; lean_object* v___x_584_; 
lean_dec_ref(v_e_549_);
lean_dec_ref(v_post_548_);
lean_dec_ref(v_pre_547_);
v_val_582_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_val_582_);
lean_dec_ref(v___x_560_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v_val_582_);
v___x_584_ = v___x_558_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_val_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_dec_ref(v_e_549_);
lean_dec_ref(v_post_548_);
lean_dec_ref(v_pre_547_);
v_a_587_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_555_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_555_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(lean_object* v_pre_595_, lean_object* v_post_596_, lean_object* v_e_597_, lean_object* v_a_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v___x_602_; 
lean_inc_ref(v_post_596_);
lean_inc(v___y_600_);
lean_inc_ref(v___y_599_);
lean_inc_ref(v_e_597_);
v___x_602_ = lean_apply_4(v_post_596_, v_e_597_, v___y_599_, v___y_600_, lean_box(0));
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_621_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_621_ == 0)
{
v___x_605_ = v___x_602_;
v_isShared_606_ = v_isSharedCheck_621_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_621_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
switch(lean_obj_tag(v_a_603_))
{
case 0:
{
lean_object* v_e_607_; lean_object* v___x_609_; 
lean_dec_ref(v_e_597_);
lean_dec_ref(v_post_596_);
lean_dec_ref(v_pre_595_);
v_e_607_ = lean_ctor_get(v_a_603_, 0);
lean_inc_ref(v_e_607_);
lean_dec_ref(v_a_603_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v_e_607_);
v___x_609_ = v___x_605_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_e_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
case 1:
{
lean_object* v_e_611_; lean_object* v___x_612_; 
lean_del_object(v___x_605_);
lean_dec_ref(v_e_597_);
v_e_611_ = lean_ctor_get(v_a_603_, 0);
lean_inc_ref(v_e_611_);
lean_dec_ref(v_a_603_);
v___x_612_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_595_, v_post_596_, v_e_611_, v_a_598_, v___y_599_, v___y_600_);
return v___x_612_;
}
default: 
{
lean_object* v_e_x3f_613_; 
lean_dec_ref(v_post_596_);
lean_dec_ref(v_pre_595_);
v_e_x3f_613_ = lean_ctor_get(v_a_603_, 0);
lean_inc(v_e_x3f_613_);
lean_dec_ref(v_a_603_);
if (lean_obj_tag(v_e_x3f_613_) == 0)
{
lean_object* v___x_615_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v_e_597_);
v___x_615_ = v___x_605_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_e_597_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
else
{
lean_object* v_val_617_; lean_object* v___x_619_; 
lean_dec_ref(v_e_597_);
v_val_617_ = lean_ctor_get(v_e_x3f_613_, 0);
lean_inc(v_val_617_);
lean_dec_ref(v_e_x3f_613_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v_val_617_);
v___x_619_ = v___x_605_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_val_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec_ref(v_e_597_);
lean_dec_ref(v_post_596_);
lean_dec_ref(v_pre_595_);
v_a_622_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_602_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_602_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_630_, lean_object* v_post_631_, lean_object* v_e_632_, lean_object* v_a_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_630_, v_post_631_, v_e_632_, v_a_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v_a_633_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_638_, lean_object* v_post_639_, lean_object* v_sz_640_, lean_object* v_i_641_, lean_object* v_bs_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
size_t v_sz_boxed_647_; size_t v_i_boxed_648_; lean_object* v_res_649_; 
v_sz_boxed_647_ = lean_unbox_usize(v_sz_640_);
lean_dec(v_sz_640_);
v_i_boxed_648_ = lean_unbox_usize(v_i_641_);
lean_dec(v_i_641_);
v_res_649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_638_, v_post_639_, v_sz_boxed_647_, v_i_boxed_648_, v_bs_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_650_, lean_object* v_post_651_, lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_650_, v_post_651_, v_x_652_, v_x_653_, v_x_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___boxed(lean_object* v_pre_660_, lean_object* v_post_661_, lean_object* v_e_662_, lean_object* v_a_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_660_, v_post_661_, v_e_662_, v_a_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v_a_663_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_object* v_00_u03b1_668_, lean_object* v_x_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_apply_1(v_x_669_, lean_box(0));
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0___boxed(lean_object* v_00_u03b1_675_, lean_object* v_x_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(v_00_u03b1_675_, v_x_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
return v_res_680_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = lean_box(0);
v___x_682_ = lean_unsigned_to_nat(16u);
v___x_683_ = lean_mk_array(v___x_682_, v___x_681_);
return v___x_683_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_684_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0);
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v___x_684_);
return v___x_686_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1);
v___x_688_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_688_, 0, lean_box(0));
lean_closure_set(v___x_688_, 1, lean_box(0));
lean_closure_set(v___x_688_, 2, v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(lean_object* v_input_689_, lean_object* v_pre_690_, lean_object* v_post_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v_a_697_; lean_object* v___x_698_; 
v___x_695_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2);
v___x_696_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_695_, v___y_692_, v___y_693_);
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref(v___x_696_);
v___x_698_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_690_, v_post_691_, v_input_689_, v_a_697_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref(v___x_698_);
v___x_700_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_700_, 0, lean_box(0));
lean_closure_set(v___x_700_, 1, lean_box(0));
lean_closure_set(v___x_700_, 2, v_a_697_);
v___x_701_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_700_, v___y_692_, v___y_693_);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; 
v_unused_709_ = lean_ctor_get(v___x_701_, 0);
lean_dec(v_unused_709_);
v___x_703_ = v___x_701_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_dec(v___x_701_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v_a_699_);
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_699_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
else
{
lean_dec(v_a_697_);
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___boxed(lean_object* v_input_710_, lean_object* v_pre_711_, lean_object* v_post_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_input_710_, v_pre_711_, v_post_712_, v___y_713_, v___y_714_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam(lean_object* v_type_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v___f_723_; lean_object* v___f_724_; lean_object* v___x_725_; 
v___f_723_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__0));
v___f_724_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__1));
v___x_725_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_type_719_, v___f_723_, v___f_724_, v_a_720_, v_a_721_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___boxed(lean_object* v_type_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_Meta_elimOptParam(v_type_726_, v_a_727_, v_a_728_);
lean_dec(v_a_728_);
lean_dec_ref(v_a_727_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_731_, lean_object* v_m_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_732_, v_a_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_735_, lean_object* v_m_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_00_u03b2_735_, v_m_736_, v_a_737_);
lean_dec_ref(v_a_737_);
lean_dec_ref(v_m_736_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_739_, lean_object* v_ref_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_740_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_745_, lean_object* v_ref_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_745_, v_ref_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_751_, lean_object* v_x_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_752_, v___y_753_, v___y_754_, v___y_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_758_, lean_object* v_x_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(v_00_u03b1_758_, v_x_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_765_, lean_object* v_m_766_, lean_object* v_a_767_, lean_object* v_b_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v_m_766_, v_a_767_, v_b_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_770_, lean_object* v_a_771_, lean_object* v_x_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_771_, v_x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_774_, lean_object* v_a_775_, lean_object* v_x_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_774_, v_a_775_, v_x_776_);
lean_dec(v_x_776_);
lean_dec_ref(v_a_775_);
return v_res_777_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9(lean_object* v_00_u03b2_778_, lean_object* v_a_779_, lean_object* v_x_780_){
_start:
{
uint8_t v___x_781_; 
v___x_781_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___redArg(v_a_779_, v_x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___boxed(lean_object* v_00_u03b2_782_, lean_object* v_a_783_, lean_object* v_x_784_){
_start:
{
uint8_t v_res_785_; lean_object* v_r_786_; 
v_res_785_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9(v_00_u03b2_782_, v_a_783_, v_x_784_);
lean_dec(v_x_784_);
lean_dec_ref(v_a_783_);
v_r_786_ = lean_box(v_res_785_);
return v_r_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_787_, lean_object* v_data_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_data_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_790_, lean_object* v_a_791_, lean_object* v_b_792_, lean_object* v_x_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_a_791_, v_b_792_, v_x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object* v_00_u03b2_795_, lean_object* v_i_796_, lean_object* v_source_797_, lean_object* v_target_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v_i_796_, v_source_797_, v_target_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_800_, lean_object* v_x_801_, lean_object* v_x_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_x_801_, v_x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(uint8_t v_skipIfPropOrEq_804_, lean_object* v_as_805_, size_t v_sz_806_, size_t v_i_807_, lean_object* v_b_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_a_815_; uint8_t v___x_819_; 
v___x_819_ = lean_usize_dec_lt(v_i_807_, v_sz_806_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; 
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v_b_808_);
return v___x_820_;
}
else
{
lean_object* v_snd_821_; lean_object* v_fst_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_900_; 
v_snd_821_ = lean_ctor_get(v_b_808_, 1);
v_fst_822_ = lean_ctor_get(v_b_808_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v_b_808_);
if (v_isSharedCheck_900_ == 0)
{
v___x_824_ = v_b_808_;
v_isShared_825_ = v_isSharedCheck_900_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_snd_821_);
lean_inc(v_fst_822_);
lean_dec(v_b_808_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_900_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_array_826_; lean_object* v_start_827_; lean_object* v_stop_828_; uint8_t v___x_829_; 
v_array_826_ = lean_ctor_get(v_snd_821_, 0);
v_start_827_ = lean_ctor_get(v_snd_821_, 1);
v_stop_828_ = lean_ctor_get(v_snd_821_, 2);
v___x_829_ = lean_nat_dec_lt(v_start_827_, v_stop_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_831_; 
if (v_isShared_825_ == 0)
{
v___x_831_ = v___x_824_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_fst_822_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_snd_821_);
v___x_831_ = v_reuseFailAlloc_833_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_832_; 
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
else
{
lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_896_; 
lean_inc(v_stop_828_);
lean_inc(v_start_827_);
lean_inc_ref(v_array_826_);
v_isSharedCheck_896_ = !lean_is_exclusive(v_snd_821_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; lean_object* v_unused_898_; lean_object* v_unused_899_; 
v_unused_897_ = lean_ctor_get(v_snd_821_, 2);
lean_dec(v_unused_897_);
v_unused_898_ = lean_ctor_get(v_snd_821_, 1);
lean_dec(v_unused_898_);
v_unused_899_ = lean_ctor_get(v_snd_821_, 0);
lean_dec(v_unused_899_);
v___x_835_ = v_snd_821_;
v_isShared_836_ = v_isSharedCheck_896_;
goto v_resetjp_834_;
}
else
{
lean_dec(v_snd_821_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_896_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v_a_837_; lean_object* v___x_838_; 
v_a_837_ = lean_array_uget_borrowed(v_as_805_, v_i_807_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
lean_inc(v_a_837_);
v___x_838_ = lean_infer_type(v_a_837_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref(v___x_838_);
v___x_840_ = lean_array_fget(v_array_826_, v_start_827_);
v___x_841_ = lean_unsigned_to_nat(1u);
v___x_842_ = lean_nat_add(v_start_827_, v___x_841_);
lean_dec(v_start_827_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v___x_842_);
v___x_844_ = v___x_835_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_array_826_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_stop_828_);
v___x_844_ = v_reuseFailAlloc_887_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
if (v_skipIfPropOrEq_804_ == 0)
{
lean_object* v___x_845_; 
lean_dec(v_a_839_);
lean_inc(v_a_837_);
v___x_845_ = l_Lean_Meta_mkEqHEq(v_a_837_, v___x_840_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref(v___x_845_);
v___x_847_ = lean_array_push(v_fst_822_, v_a_846_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 1, v___x_844_);
lean_ctor_set(v___x_824_, 0, v___x_847_);
v___x_849_ = v___x_824_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v___x_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
v_a_815_ = v___x_849_;
goto v___jp_814_;
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec_ref(v___x_844_);
lean_del_object(v___x_824_);
lean_dec(v_fst_822_);
v_a_851_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_845_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_845_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
else
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Meta_isProp(v_a_839_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; uint8_t v___x_865_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref(v___x_859_);
v___x_865_ = lean_unbox(v_a_860_);
lean_dec(v_a_860_);
if (v___x_865_ == 0)
{
uint8_t v___x_866_; 
v___x_866_ = lean_expr_eqv(v_a_837_, v___x_840_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; 
lean_del_object(v___x_824_);
lean_inc(v_a_837_);
v___x_867_ = l_Lean_Meta_mkEqHEq(v_a_837_, v___x_840_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref(v___x_867_);
v___x_869_ = lean_array_push(v_fst_822_, v_a_868_);
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v___x_844_);
v_a_815_ = v___x_870_;
goto v___jp_814_;
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_dec_ref(v___x_844_);
lean_dec(v_fst_822_);
v_a_871_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_867_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_867_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
else
{
lean_dec(v___x_840_);
goto v___jp_861_;
}
}
else
{
lean_dec(v___x_840_);
goto v___jp_861_;
}
v___jp_861_:
{
lean_object* v___x_863_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 1, v___x_844_);
v___x_863_ = v___x_824_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_fst_822_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v___x_844_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
v_a_815_ = v___x_863_;
goto v___jp_814_;
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_dec_ref(v___x_844_);
lean_dec(v___x_840_);
lean_del_object(v___x_824_);
lean_dec(v_fst_822_);
v_a_879_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_859_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_859_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_del_object(v___x_835_);
lean_dec(v_stop_828_);
lean_dec(v_start_827_);
lean_dec_ref(v_array_826_);
lean_del_object(v___x_824_);
lean_dec(v_fst_822_);
v_a_888_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_838_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_838_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
}
}
v___jp_814_:
{
size_t v___x_816_; size_t v___x_817_; 
v___x_816_ = ((size_t)1ULL);
v___x_817_ = lean_usize_add(v_i_807_, v___x_816_);
v_i_807_ = v___x_817_;
v_b_808_ = v_a_815_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0___boxed(lean_object* v_skipIfPropOrEq_901_, lean_object* v_as_902_, lean_object* v_sz_903_, lean_object* v_i_904_, lean_object* v_b_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_911_; size_t v_sz_boxed_912_; size_t v_i_boxed_913_; lean_object* v_res_914_; 
v_skipIfPropOrEq_boxed_911_ = lean_unbox(v_skipIfPropOrEq_901_);
v_sz_boxed_912_ = lean_unbox_usize(v_sz_903_);
lean_dec(v_sz_903_);
v_i_boxed_913_ = lean_unbox_usize(v_i_904_);
lean_dec(v_i_904_);
v_res_914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_boxed_911_, v_as_902_, v_sz_boxed_912_, v_i_boxed_913_, v_b_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec_ref(v_as_902_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(lean_object* v_args1_917_, lean_object* v_args2_918_, uint8_t v_skipIfPropOrEq_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_925_; lean_object* v_eqs_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; size_t v_sz_930_; size_t v___x_931_; lean_object* v___x_932_; 
v___x_925_ = lean_unsigned_to_nat(0u);
v_eqs_926_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_927_ = lean_array_get_size(v_args2_918_);
v___x_928_ = l_Array_toSubarray___redArg(v_args2_918_, v___x_925_, v___x_927_);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v_eqs_926_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v_sz_930_ = lean_array_size(v_args1_917_);
v___x_931_ = ((size_t)0ULL);
v___x_932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_919_, v_args1_917_, v_sz_930_, v___x_931_, v___x_929_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_941_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_941_ == 0)
{
v___x_935_ = v___x_932_;
v_isShared_936_ = v_isSharedCheck_941_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_941_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v_fst_937_; lean_object* v___x_939_; 
v_fst_937_ = lean_ctor_get(v_a_933_, 0);
lean_inc(v_fst_937_);
lean_dec(v_a_933_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v_fst_937_);
v___x_939_ = v___x_935_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_fst_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
v_a_942_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_932_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_932_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___boxed(lean_object* v_args1_950_, lean_object* v_args2_951_, lean_object* v_skipIfPropOrEq_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_958_; lean_object* v_res_959_; 
v_skipIfPropOrEq_boxed_958_ = lean_unbox(v_skipIfPropOrEq_952_);
v_res_959_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_950_, v_args2_951_, v_skipIfPropOrEq_boxed_958_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec_ref(v_args1_950_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(lean_object* v_k_960_, lean_object* v_b_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; 
lean_inc(v___y_965_);
lean_inc_ref(v___y_964_);
lean_inc(v___y_963_);
lean_inc_ref(v___y_962_);
v___x_967_ = lean_apply_6(v_k_960_, v_b_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, lean_box(0));
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed(lean_object* v_k_968_, lean_object* v_b_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(v_k_968_, v_b_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(lean_object* v_name_976_, uint8_t v_bi_977_, lean_object* v_type_978_, lean_object* v_k_979_, uint8_t v_kind_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___f_986_; lean_object* v___x_987_; 
v___f_986_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_986_, 0, v_k_979_);
v___x_987_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_976_, v_bi_977_, v_type_978_, v___f_986_, v_kind_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
v_a_996_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_987_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_987_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___boxed(lean_object* v_name_1004_, lean_object* v_bi_1005_, lean_object* v_type_1006_, lean_object* v_k_1007_, lean_object* v_kind_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
uint8_t v_bi_boxed_1014_; uint8_t v_kind_boxed_1015_; lean_object* v_res_1016_; 
v_bi_boxed_1014_ = lean_unbox(v_bi_1005_);
v_kind_boxed_1015_ = lean_unbox(v_kind_1008_);
v_res_1016_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1004_, v_bi_boxed_1014_, v_type_1006_, v_k_1007_, v_kind_boxed_1015_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(lean_object* v_00_u03b1_1017_, lean_object* v_name_1018_, uint8_t v_bi_1019_, lean_object* v_type_1020_, lean_object* v_k_1021_, uint8_t v_kind_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1018_, v_bi_1019_, v_type_1020_, v_k_1021_, v_kind_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___boxed(lean_object* v_00_u03b1_1029_, lean_object* v_name_1030_, lean_object* v_bi_1031_, lean_object* v_type_1032_, lean_object* v_k_1033_, lean_object* v_kind_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
uint8_t v_bi_boxed_1040_; uint8_t v_kind_boxed_1041_; lean_object* v_res_1042_; 
v_bi_boxed_1040_ = lean_unbox(v_bi_1031_);
v_kind_boxed_1041_ = lean_unbox(v_kind_1034_);
v_res_1042_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(v_00_u03b1_1029_, v_name_1030_, v_bi_boxed_1040_, v_type_1032_, v_k_1033_, v_kind_boxed_1041_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(lean_object* v_msgData_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v___x_1049_; lean_object* v_env_1050_; lean_object* v___x_1051_; lean_object* v_mctx_1052_; lean_object* v_lctx_1053_; lean_object* v_options_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1049_ = lean_st_ref_get(v___y_1047_);
v_env_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc_ref(v_env_1050_);
lean_dec(v___x_1049_);
v___x_1051_ = lean_st_ref_get(v___y_1045_);
v_mctx_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc_ref(v_mctx_1052_);
lean_dec(v___x_1051_);
v_lctx_1053_ = lean_ctor_get(v___y_1044_, 2);
v_options_1054_ = lean_ctor_get(v___y_1046_, 2);
lean_inc_ref(v_options_1054_);
lean_inc_ref(v_lctx_1053_);
v___x_1055_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1055_, 0, v_env_1050_);
lean_ctor_set(v___x_1055_, 1, v_mctx_1052_);
lean_ctor_set(v___x_1055_, 2, v_lctx_1053_);
lean_ctor_set(v___x_1055_, 3, v_options_1054_);
v___x_1056_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
lean_ctor_set(v___x_1056_, 1, v_msgData_1043_);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1___boxed(lean_object* v_msgData_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msgData_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(lean_object* v_msg_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_ref_1071_; lean_object* v___x_1072_; lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1081_; 
v_ref_1071_ = lean_ctor_get(v___y_1068_, 5);
v___x_1072_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
lean_inc(v_ref_1071_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_ref_1071_);
lean_ctor_set(v___x_1077_, 1, v_a_1073_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set_tag(v___x_1075_, 1);
lean_ctor_set(v___x_1075_, 0, v___x_1077_);
v___x_1079_ = v___x_1075_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg___boxed(lean_object* v_msg_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_1089_, lean_object* v_body_1090_, lean_object* v_args2_1091_, lean_object* v_args2New_1092_, lean_object* v_ctorVal_1093_, lean_object* v_useEq_1094_, lean_object* v_args1_1095_, lean_object* v_resultType_1096_, lean_object* v_k_1097_, lean_object* v_arg2_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
uint8_t v_useEq_boxed_1104_; lean_object* v_res_1105_; 
v_useEq_boxed_1104_ = lean_unbox(v_useEq_1094_);
v_res_1105_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(v_i_1089_, v_body_1090_, v_args2_1091_, v_args2New_1092_, v_ctorVal_1093_, v_useEq_boxed_1104_, v_args1_1095_, v_resultType_1096_, v_k_1097_, v_arg2_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec_ref(v_body_1090_);
lean_dec(v_i_1089_);
return v_res_1105_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0));
v___x_1108_ = l_Lean_stringToMessageData(v___x_1107_);
return v___x_1108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2));
v___x_1111_ = l_Lean_stringToMessageData(v___x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(lean_object* v_ctorVal_1112_, uint8_t v_useEq_1113_, lean_object* v_args1_1114_, lean_object* v_resultType_1115_, lean_object* v_k_1116_, lean_object* v_i_1117_, lean_object* v_type_1118_, lean_object* v_args2_1119_, lean_object* v_args2New_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = lean_array_get_size(v_args1_1114_);
v___x_1127_ = lean_nat_dec_lt(v_i_1117_, v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; 
lean_dec_ref(v_type_1118_);
lean_dec(v_i_1117_);
lean_dec_ref(v_resultType_1115_);
lean_dec_ref(v_args1_1114_);
lean_dec_ref(v_ctorVal_1112_);
lean_inc(v_a_1124_);
lean_inc_ref(v_a_1123_);
lean_inc(v_a_1122_);
lean_inc_ref(v_a_1121_);
v___x_1128_ = lean_apply_7(v_k_1116_, v_args2_1119_, v_args2New_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, lean_box(0));
return v___x_1128_;
}
else
{
lean_object* v___x_1129_; 
lean_inc(v_a_1124_);
lean_inc_ref(v_a_1123_);
lean_inc(v_a_1122_);
lean_inc_ref(v_a_1121_);
v___x_1129_ = lean_whnf(v_type_1118_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref(v___x_1129_);
if (lean_obj_tag(v_a_1130_) == 7)
{
lean_object* v_binderName_1131_; lean_object* v_binderType_1132_; lean_object* v_body_1133_; lean_object* v_lctx_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v_binderName_1131_ = lean_ctor_get(v_a_1130_, 0);
lean_inc(v_binderName_1131_);
v_binderType_1132_ = lean_ctor_get(v_a_1130_, 1);
lean_inc_ref(v_binderType_1132_);
v_body_1133_ = lean_ctor_get(v_a_1130_, 2);
lean_inc_ref(v_body_1133_);
lean_dec_ref(v_a_1130_);
v_lctx_1134_ = lean_ctor_get(v_a_1121_, 2);
v___x_1135_ = lean_array_fget_borrowed(v_args1_1114_, v_i_1117_);
lean_inc(v___x_1135_);
lean_inc_ref(v_lctx_1134_);
v___x_1136_ = l_Lean_Meta_occursOrInType(v_lctx_1134_, v___x_1135_, v_resultType_1115_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; lean_object* v___f_1138_; uint8_t v___y_1140_; 
v___x_1137_ = lean_box(v_useEq_1113_);
v___f_1138_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1138_, 0, v_i_1117_);
lean_closure_set(v___f_1138_, 1, v_body_1133_);
lean_closure_set(v___f_1138_, 2, v_args2_1119_);
lean_closure_set(v___f_1138_, 3, v_args2New_1120_);
lean_closure_set(v___f_1138_, 4, v_ctorVal_1112_);
lean_closure_set(v___f_1138_, 5, v___x_1137_);
lean_closure_set(v___f_1138_, 6, v_args1_1114_);
lean_closure_set(v___f_1138_, 7, v_resultType_1115_);
lean_closure_set(v___f_1138_, 8, v_k_1116_);
if (v_useEq_1113_ == 0)
{
uint8_t v___x_1143_; 
v___x_1143_ = 1;
v___y_1140_ = v___x_1143_;
goto v___jp_1139_;
}
else
{
uint8_t v___x_1144_; 
v___x_1144_ = 0;
v___y_1140_ = v___x_1144_;
goto v___jp_1139_;
}
v___jp_1139_:
{
uint8_t v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = 0;
v___x_1142_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_1131_, v___y_1140_, v_binderType_1132_, v___f_1138_, v___x_1141_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
return v___x_1142_;
}
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_dec_ref(v_binderType_1132_);
lean_dec(v_binderName_1131_);
v___x_1145_ = lean_unsigned_to_nat(1u);
v___x_1146_ = lean_nat_add(v_i_1117_, v___x_1145_);
lean_dec(v_i_1117_);
v___x_1147_ = lean_expr_instantiate1(v_body_1133_, v___x_1135_);
lean_dec_ref(v_body_1133_);
lean_inc(v___x_1135_);
v___x_1148_ = lean_array_push(v_args2_1119_, v___x_1135_);
v_i_1117_ = v___x_1146_;
v_type_1118_ = v___x_1147_;
v_args2_1119_ = v___x_1148_;
goto _start;
}
}
else
{
lean_object* v_toConstantVal_1150_; lean_object* v_name_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_dec(v_a_1130_);
lean_dec_ref(v_args2New_1120_);
lean_dec_ref(v_args2_1119_);
lean_dec(v_i_1117_);
lean_dec_ref(v_k_1116_);
lean_dec_ref(v_resultType_1115_);
lean_dec_ref(v_args1_1114_);
v_toConstantVal_1150_ = lean_ctor_get(v_ctorVal_1112_, 0);
lean_inc_ref(v_toConstantVal_1150_);
lean_dec_ref(v_ctorVal_1112_);
v_name_1151_ = lean_ctor_get(v_toConstantVal_1150_, 0);
lean_inc(v_name_1151_);
lean_dec_ref(v_toConstantVal_1150_);
v___x_1152_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_1153_ = l_Lean_MessageData_ofName(v_name_1151_);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1156_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
return v___x_1157_;
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec_ref(v_args2New_1120_);
lean_dec_ref(v_args2_1119_);
lean_dec(v_i_1117_);
lean_dec_ref(v_k_1116_);
lean_dec_ref(v_resultType_1115_);
lean_dec_ref(v_args1_1114_);
lean_dec_ref(v_ctorVal_1112_);
v_a_1158_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1129_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1129_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(lean_object* v_i_1166_, lean_object* v_body_1167_, lean_object* v_args2_1168_, lean_object* v_args2New_1169_, lean_object* v_ctorVal_1170_, uint8_t v_useEq_1171_, lean_object* v_args1_1172_, lean_object* v_resultType_1173_, lean_object* v_k_1174_, lean_object* v_arg2_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1181_ = lean_unsigned_to_nat(1u);
v___x_1182_ = lean_nat_add(v_i_1166_, v___x_1181_);
v___x_1183_ = lean_expr_instantiate1(v_body_1167_, v_arg2_1175_);
lean_inc_ref(v_arg2_1175_);
v___x_1184_ = lean_array_push(v_args2_1168_, v_arg2_1175_);
v___x_1185_ = lean_array_push(v_args2New_1169_, v_arg2_1175_);
v___x_1186_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1170_, v_useEq_1171_, v_args1_1172_, v_resultType_1173_, v_k_1174_, v___x_1182_, v___x_1183_, v___x_1184_, v___x_1185_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed(lean_object* v_ctorVal_1187_, lean_object* v_useEq_1188_, lean_object* v_args1_1189_, lean_object* v_resultType_1190_, lean_object* v_k_1191_, lean_object* v_i_1192_, lean_object* v_type_1193_, lean_object* v_args2_1194_, lean_object* v_args2New_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_){
_start:
{
uint8_t v_useEq_boxed_1201_; lean_object* v_res_1202_; 
v_useEq_boxed_1201_ = lean_unbox(v_useEq_1188_);
v_res_1202_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1187_, v_useEq_boxed_1201_, v_args1_1189_, v_resultType_1190_, v_k_1191_, v_i_1192_, v_type_1193_, v_args2_1194_, v_args2New_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(lean_object* v_00_u03b1_1203_, lean_object* v_msg_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___boxed(lean_object* v_00_u03b1_1211_, lean_object* v_msg_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(v_00_u03b1_1211_, v_msg_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter___redArg(lean_object* v_____x_1219_, lean_object* v_h__1_1220_, lean_object* v_h__2_1221_){
_start:
{
if (lean_obj_tag(v_____x_1219_) == 7)
{
lean_object* v_binderName_1222_; lean_object* v_binderType_1223_; lean_object* v_body_1224_; uint8_t v_binderInfo_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_dec(v_h__2_1221_);
v_binderName_1222_ = lean_ctor_get(v_____x_1219_, 0);
lean_inc(v_binderName_1222_);
v_binderType_1223_ = lean_ctor_get(v_____x_1219_, 1);
lean_inc_ref(v_binderType_1223_);
v_body_1224_ = lean_ctor_get(v_____x_1219_, 2);
lean_inc_ref(v_body_1224_);
v_binderInfo_1225_ = lean_ctor_get_uint8(v_____x_1219_, sizeof(void*)*3 + 8);
lean_dec_ref(v_____x_1219_);
v___x_1226_ = lean_box(v_binderInfo_1225_);
v___x_1227_ = lean_apply_4(v_h__1_1220_, v_binderName_1222_, v_binderType_1223_, v_body_1224_, v___x_1226_);
return v___x_1227_;
}
else
{
lean_object* v___x_1228_; 
lean_dec(v_h__1_1220_);
v___x_1228_ = lean_apply_2(v_h__2_1221_, v_____x_1219_, lean_box(0));
return v___x_1228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter(lean_object* v_motive_1229_, lean_object* v_____x_1230_, lean_object* v_h__1_1231_, lean_object* v_h__2_1232_){
_start:
{
if (lean_obj_tag(v_____x_1230_) == 7)
{
lean_object* v_binderName_1233_; lean_object* v_binderType_1234_; lean_object* v_body_1235_; uint8_t v_binderInfo_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec(v_h__2_1232_);
v_binderName_1233_ = lean_ctor_get(v_____x_1230_, 0);
lean_inc(v_binderName_1233_);
v_binderType_1234_ = lean_ctor_get(v_____x_1230_, 1);
lean_inc_ref(v_binderType_1234_);
v_body_1235_ = lean_ctor_get(v_____x_1230_, 2);
lean_inc_ref(v_body_1235_);
v_binderInfo_1236_ = lean_ctor_get_uint8(v_____x_1230_, sizeof(void*)*3 + 8);
lean_dec_ref(v_____x_1230_);
v___x_1237_ = lean_box(v_binderInfo_1236_);
v___x_1238_ = lean_apply_4(v_h__1_1231_, v_binderName_1233_, v_binderType_1234_, v_body_1235_, v___x_1237_);
return v___x_1238_;
}
else
{
lean_object* v___x_1239_; 
lean_dec(v_h__1_1231_);
v___x_1239_ = lean_apply_2(v_h__2_1232_, v_____x_1230_, lean_box(0));
return v___x_1239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(lean_object* v_k_1240_, lean_object* v_b_1241_, lean_object* v_c_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v___x_1248_; 
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
v___x_1248_ = lean_apply_7(v_k_1240_, v_b_1241_, v_c_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, lean_box(0));
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed(lean_object* v_k_1249_, lean_object* v_b_1250_, lean_object* v_c_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(v_k_1249_, v_b_1250_, v_c_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(lean_object* v_type_1258_, lean_object* v_k_1259_, uint8_t v_cleanupAnnotations_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___f_1266_; uint8_t v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___f_1266_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1266_, 0, v_k_1259_);
v___x_1267_ = 0;
v___x_1268_ = lean_box(0);
v___x_1269_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1267_, v___x_1268_, v_type_1258_, v___f_1266_, v_cleanupAnnotations_1260_, v___x_1267_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1269_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1269_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
v_a_1278_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1269_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1269_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___boxed(lean_object* v_type_1286_, lean_object* v_k_1287_, lean_object* v_cleanupAnnotations_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1294_; lean_object* v_res_1295_; 
v_cleanupAnnotations_boxed_1294_ = lean_unbox(v_cleanupAnnotations_1288_);
v_res_1295_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1286_, v_k_1287_, v_cleanupAnnotations_boxed_1294_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(lean_object* v_00_u03b1_1296_, lean_object* v_type_1297_, lean_object* v_k_1298_, uint8_t v_cleanupAnnotations_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1297_, v_k_1298_, v_cleanupAnnotations_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___boxed(lean_object* v_00_u03b1_1306_, lean_object* v_type_1307_, lean_object* v_k_1308_, lean_object* v_cleanupAnnotations_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1315_; lean_object* v_res_1316_; 
v_cleanupAnnotations_boxed_1315_ = lean_unbox(v_cleanupAnnotations_1309_);
v_res_1316_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(v_00_u03b1_1306_, v_type_1307_, v_k_1308_, v_cleanupAnnotations_boxed_1315_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(lean_object* v_type_1317_, lean_object* v_maxFVars_x3f_1318_, lean_object* v_k_1319_, uint8_t v_cleanupAnnotations_1320_, uint8_t v_whnfType_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___f_1327_; lean_object* v___x_1328_; 
v___f_1327_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1327_, 0, v_k_1319_);
v___x_1328_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1317_, v_maxFVars_x3f_1318_, v___f_1327_, v_cleanupAnnotations_1320_, v_whnfType_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
v_a_1337_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1328_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1328_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg___boxed(lean_object* v_type_1345_, lean_object* v_maxFVars_x3f_1346_, lean_object* v_k_1347_, lean_object* v_cleanupAnnotations_1348_, lean_object* v_whnfType_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1355_; uint8_t v_whnfType_boxed_1356_; lean_object* v_res_1357_; 
v_cleanupAnnotations_boxed_1355_ = lean_unbox(v_cleanupAnnotations_1348_);
v_whnfType_boxed_1356_ = lean_unbox(v_whnfType_1349_);
v_res_1357_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1345_, v_maxFVars_x3f_1346_, v_k_1347_, v_cleanupAnnotations_boxed_1355_, v_whnfType_boxed_1356_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(lean_object* v_00_u03b1_1358_, lean_object* v_type_1359_, lean_object* v_maxFVars_x3f_1360_, lean_object* v_k_1361_, uint8_t v_cleanupAnnotations_1362_, uint8_t v_whnfType_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1359_, v_maxFVars_x3f_1360_, v_k_1361_, v_cleanupAnnotations_1362_, v_whnfType_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___boxed(lean_object* v_00_u03b1_1370_, lean_object* v_type_1371_, lean_object* v_maxFVars_x3f_1372_, lean_object* v_k_1373_, lean_object* v_cleanupAnnotations_1374_, lean_object* v_whnfType_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1381_; uint8_t v_whnfType_boxed_1382_; lean_object* v_res_1383_; 
v_cleanupAnnotations_boxed_1381_ = lean_unbox(v_cleanupAnnotations_1374_);
v_whnfType_boxed_1382_ = lean_unbox(v_whnfType_1375_);
v_res_1383_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(v_00_u03b1_1370_, v_type_1371_, v_maxFVars_x3f_1372_, v_k_1373_, v_cleanupAnnotations_boxed_1381_, v_whnfType_boxed_1382_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(lean_object* v_name_1384_, lean_object* v_us_1385_, lean_object* v_params_1386_, lean_object* v_args1_1387_, uint8_t v_useEq_1388_, lean_object* v_args2_1389_, lean_object* v_args2New_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1396_ = l_Lean_mkConst(v_name_1384_, v_us_1385_);
v___x_1397_ = l_Lean_mkAppN(v___x_1396_, v_params_1386_);
lean_inc_ref(v___x_1397_);
v___x_1398_ = l_Lean_mkAppN(v___x_1397_, v_args1_1387_);
v___x_1399_ = l_Lean_mkAppN(v___x_1397_, v_args2_1389_);
v___x_1400_ = l_Lean_Meta_mkEq(v___x_1398_, v___x_1399_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; uint8_t v___x_1402_; lean_object* v_result_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___x_1449_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref(v___x_1400_);
v___x_1402_ = 1;
v___x_1449_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_1387_, v_args2_1389_, v___x_1402_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1481_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1481_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1481_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; 
v___x_1454_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_1450_);
if (lean_obj_tag(v___x_1454_) == 1)
{
lean_del_object(v___x_1452_);
if (v_useEq_1388_ == 0)
{
lean_object* v_val_1455_; lean_object* v___x_1456_; 
v_val_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_val_1455_);
lean_dec_ref(v___x_1454_);
v___x_1456_ = l_Lean_mkArrow(v_a_1401_, v_val_1455_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref(v___x_1456_);
v_result_1404_ = v_a_1457_;
v___y_1405_ = v___y_1391_;
v___y_1406_ = v___y_1392_;
v___y_1407_ = v___y_1393_;
v___y_1408_ = v___y_1394_;
goto v___jp_1403_;
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
v_a_1458_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1456_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1456_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
else
{
lean_object* v_val_1466_; lean_object* v___x_1467_; 
v_val_1466_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_val_1466_);
lean_dec_ref(v___x_1454_);
v___x_1467_ = l_Lean_Meta_mkEq(v_a_1401_, v_val_1466_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_a_1468_);
lean_dec_ref(v___x_1467_);
v_result_1404_ = v_a_1468_;
v___y_1405_ = v___y_1391_;
v___y_1406_ = v___y_1392_;
v___y_1407_ = v___y_1393_;
v___y_1408_ = v___y_1394_;
goto v___jp_1403_;
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
v_a_1469_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1467_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1467_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1479_; 
lean_dec(v___x_1454_);
lean_dec(v_a_1401_);
v___x_1477_ = lean_box(0);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1477_);
v___x_1479_ = v___x_1452_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1477_);
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
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec(v_a_1401_);
v_a_1482_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1449_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1449_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
v___jp_1403_:
{
uint8_t v___x_1409_; uint8_t v___x_1410_; lean_object* v___x_1411_; 
v___x_1409_ = 0;
v___x_1410_ = 1;
v___x_1411_ = l_Lean_Meta_mkForallFVars(v_args2New_1390_, v_result_1404_, v___x_1409_, v___x_1402_, v___x_1402_, v___x_1410_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1413_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref(v___x_1411_);
v___x_1413_ = l_Lean_Meta_mkForallFVars(v_args1_1387_, v_a_1412_, v___x_1409_, v___x_1402_, v___x_1402_, v___x_1410_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1415_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref(v___x_1413_);
v___x_1415_ = l_Lean_Meta_mkForallFVars(v_params_1386_, v_a_1414_, v___x_1409_, v___x_1402_, v___x_1402_, v___x_1410_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1424_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1420_, 0, v_a_1416_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1420_);
v___x_1422_ = v___x_1418_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
v_a_1425_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1415_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1415_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
v_a_1433_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1413_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1413_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
v_a_1441_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1411_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1411_);
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
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec_ref(v_args2_1389_);
v_a_1490_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1400_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1400_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed(lean_object* v_name_1498_, lean_object* v_us_1499_, lean_object* v_params_1500_, lean_object* v_args1_1501_, lean_object* v_useEq_1502_, lean_object* v_args2_1503_, lean_object* v_args2New_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
uint8_t v_useEq_boxed_1510_; lean_object* v_res_1511_; 
v_useEq_boxed_1510_ = lean_unbox(v_useEq_1502_);
v_res_1511_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(v_name_1498_, v_us_1499_, v_params_1500_, v_args1_1501_, v_useEq_boxed_1510_, v_args2_1503_, v_args2New_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec_ref(v_args2New_1504_);
lean_dec_ref(v_args1_1501_);
lean_dec_ref(v_params_1500_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(size_t v_sz_1512_, size_t v_i_1513_, lean_object* v_bs_1514_){
_start:
{
uint8_t v___x_1515_; 
v___x_1515_ = lean_usize_dec_lt(v_i_1513_, v_sz_1512_);
if (v___x_1515_ == 0)
{
return v_bs_1514_;
}
else
{
lean_object* v_v_1516_; lean_object* v___x_1517_; lean_object* v_bs_x27_1518_; lean_object* v___x_1519_; uint8_t v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; size_t v___x_1523_; size_t v___x_1524_; lean_object* v___x_1525_; 
v_v_1516_ = lean_array_uget(v_bs_1514_, v_i_1513_);
v___x_1517_ = lean_unsigned_to_nat(0u);
v_bs_x27_1518_ = lean_array_uset(v_bs_1514_, v_i_1513_, v___x_1517_);
v___x_1519_ = l_Lean_Expr_fvarId_x21(v_v_1516_);
lean_dec(v_v_1516_);
v___x_1520_ = 1;
v___x_1521_ = lean_box(v___x_1520_);
v___x_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1519_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
v___x_1523_ = ((size_t)1ULL);
v___x_1524_ = lean_usize_add(v_i_1513_, v___x_1523_);
v___x_1525_ = lean_array_uset(v_bs_x27_1518_, v_i_1513_, v___x_1522_);
v_i_1513_ = v___x_1524_;
v_bs_1514_ = v___x_1525_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1___boxed(lean_object* v_sz_1527_, lean_object* v_i_1528_, lean_object* v_bs_1529_){
_start:
{
size_t v_sz_boxed_1530_; size_t v_i_boxed_1531_; lean_object* v_res_1532_; 
v_sz_boxed_1530_ = lean_unbox_usize(v_sz_1527_);
lean_dec(v_sz_1527_);
v_i_boxed_1531_ = lean_unbox_usize(v_i_1528_);
lean_dec(v_i_1528_);
v_res_1532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_boxed_1530_, v_i_boxed_1531_, v_bs_1529_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(lean_object* v_bs_1533_, lean_object* v_k_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1533_, v_k_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
v_a_1549_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1540_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1540_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_bs_1557_, lean_object* v_k_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1557_, v_k_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec_ref(v_bs_1557_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(lean_object* v_bs_1565_, lean_object* v_k_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
size_t v_sz_1572_; size_t v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v_sz_1572_ = lean_array_size(v_bs_1565_);
v___x_1573_ = ((size_t)0ULL);
v___x_1574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_1572_, v___x_1573_, v_bs_1565_);
v___x_1575_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v___x_1574_, v_k_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec_ref(v___x_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg___boxed(lean_object* v_bs_1576_, lean_object* v_k_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1576_, v_k_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(lean_object* v_name_1584_, lean_object* v_us_1585_, lean_object* v_params_1586_, uint8_t v_useEq_1587_, lean_object* v_ctorVal_1588_, lean_object* v_type_1589_, lean_object* v_args1_1590_, lean_object* v_resultType_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; lean_object* v___f_1598_; 
v___x_1597_ = lean_box(v_useEq_1587_);
lean_inc_ref(v_args1_1590_);
lean_inc_ref(v_params_1586_);
v___f_1598_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1598_, 0, v_name_1584_);
lean_closure_set(v___f_1598_, 1, v_us_1585_);
lean_closure_set(v___f_1598_, 2, v_params_1586_);
lean_closure_set(v___f_1598_, 3, v_args1_1590_);
lean_closure_set(v___f_1598_, 4, v___x_1597_);
if (v_useEq_1587_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1599_ = l_Array_append___redArg(v_params_1586_, v_args1_1590_);
v___x_1600_ = lean_unsigned_to_nat(0u);
v___x_1601_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1602_ = lean_box(v_useEq_1587_);
v___x_1603_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed), 14, 9);
lean_closure_set(v___x_1603_, 0, v_ctorVal_1588_);
lean_closure_set(v___x_1603_, 1, v___x_1602_);
lean_closure_set(v___x_1603_, 2, v_args1_1590_);
lean_closure_set(v___x_1603_, 3, v_resultType_1591_);
lean_closure_set(v___x_1603_, 4, v___f_1598_);
lean_closure_set(v___x_1603_, 5, v___x_1600_);
lean_closure_set(v___x_1603_, 6, v_type_1589_);
lean_closure_set(v___x_1603_, 7, v___x_1601_);
lean_closure_set(v___x_1603_, 8, v___x_1601_);
v___x_1604_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v___x_1599_, v___x_1603_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
return v___x_1604_;
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
lean_dec_ref(v_params_1586_);
v___x_1605_ = lean_unsigned_to_nat(0u);
v___x_1606_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1607_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1588_, v_useEq_1587_, v_args1_1590_, v_resultType_1591_, v___f_1598_, v___x_1605_, v_type_1589_, v___x_1606_, v___x_1606_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
return v___x_1607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed(lean_object* v_name_1608_, lean_object* v_us_1609_, lean_object* v_params_1610_, lean_object* v_useEq_1611_, lean_object* v_ctorVal_1612_, lean_object* v_type_1613_, lean_object* v_args1_1614_, lean_object* v_resultType_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
uint8_t v_useEq_boxed_1621_; lean_object* v_res_1622_; 
v_useEq_boxed_1621_ = lean_unbox(v_useEq_1611_);
v_res_1622_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(v_name_1608_, v_us_1609_, v_params_1610_, v_useEq_boxed_1621_, v_ctorVal_1612_, v_type_1613_, v_args1_1614_, v_resultType_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(lean_object* v_name_1623_, lean_object* v_us_1624_, uint8_t v_useEq_1625_, lean_object* v_ctorVal_1626_, lean_object* v_params_1627_, lean_object* v_type_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v___x_1634_; lean_object* v___f_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; 
v___x_1634_ = lean_box(v_useEq_1625_);
lean_inc_ref(v_type_1628_);
v___f_1635_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1635_, 0, v_name_1623_);
lean_closure_set(v___f_1635_, 1, v_us_1624_);
lean_closure_set(v___f_1635_, 2, v_params_1627_);
lean_closure_set(v___f_1635_, 3, v___x_1634_);
lean_closure_set(v___f_1635_, 4, v_ctorVal_1626_);
lean_closure_set(v___f_1635_, 5, v_type_1628_);
v___x_1636_ = 0;
v___x_1637_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1628_, v___f_1635_, v___x_1636_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed(lean_object* v_name_1638_, lean_object* v_us_1639_, lean_object* v_useEq_1640_, lean_object* v_ctorVal_1641_, lean_object* v_params_1642_, lean_object* v_type_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
uint8_t v_useEq_boxed_1649_; lean_object* v_res_1650_; 
v_useEq_boxed_1649_ = lean_unbox(v_useEq_1640_);
v_res_1650_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(v_name_1638_, v_us_1639_, v_useEq_boxed_1649_, v_ctorVal_1641_, v_params_1642_, v_type_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
if (lean_obj_tag(v_a_1651_) == 0)
{
lean_object* v___x_1653_; 
v___x_1653_ = l_List_reverse___redArg(v_a_1652_);
return v___x_1653_;
}
else
{
lean_object* v_head_1654_; lean_object* v_tail_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1664_; 
v_head_1654_ = lean_ctor_get(v_a_1651_, 0);
v_tail_1655_ = lean_ctor_get(v_a_1651_, 1);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_a_1651_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1657_ = v_a_1651_;
v_isShared_1658_ = v_isSharedCheck_1664_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_tail_1655_);
lean_inc(v_head_1654_);
lean_dec(v_a_1651_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1664_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1659_ = l_Lean_mkLevelParam(v_head_1654_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 1, v_a_1652_);
lean_ctor_set(v___x_1657_, 0, v___x_1659_);
v___x_1661_ = v___x_1657_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_a_1652_);
v___x_1661_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
v_a_1651_ = v_tail_1655_;
v_a_1652_ = v___x_1661_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(lean_object* v_ctorVal_1665_, uint8_t v_useEq_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v_toConstantVal_1672_; lean_object* v_numParams_1673_; lean_object* v_name_1674_; lean_object* v_levelParams_1675_; lean_object* v_type_1676_; lean_object* v___x_1677_; 
v_toConstantVal_1672_ = lean_ctor_get(v_ctorVal_1665_, 0);
v_numParams_1673_ = lean_ctor_get(v_ctorVal_1665_, 3);
lean_inc(v_numParams_1673_);
v_name_1674_ = lean_ctor_get(v_toConstantVal_1672_, 0);
lean_inc(v_name_1674_);
v_levelParams_1675_ = lean_ctor_get(v_toConstantVal_1672_, 1);
v_type_1676_ = lean_ctor_get(v_toConstantVal_1672_, 2);
lean_inc_ref(v_type_1676_);
v___x_1677_ = l_Lean_Meta_elimOptParam(v_type_1676_, v_a_1669_, v_a_1670_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1679_; lean_object* v_us_1680_; lean_object* v___x_1681_; lean_object* v___f_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; lean_object* v___x_1685_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_a_1678_);
lean_dec_ref(v___x_1677_);
v___x_1679_ = lean_box(0);
lean_inc(v_levelParams_1675_);
v_us_1680_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_1675_, v___x_1679_);
v___x_1681_ = lean_box(v_useEq_1666_);
v___f_1682_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1682_, 0, v_name_1674_);
lean_closure_set(v___f_1682_, 1, v_us_1680_);
lean_closure_set(v___f_1682_, 2, v___x_1681_);
lean_closure_set(v___f_1682_, 3, v_ctorVal_1665_);
v___x_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1683_, 0, v_numParams_1673_);
v___x_1684_ = 0;
v___x_1685_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_a_1678_, v___x_1683_, v___f_1682_, v___x_1684_, v___x_1684_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
return v___x_1685_;
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_name_1674_);
lean_dec(v_numParams_1673_);
lean_dec_ref(v_ctorVal_1665_);
v_a_1686_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1677_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1677_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___boxed(lean_object* v_ctorVal_1694_, lean_object* v_useEq_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
uint8_t v_useEq_boxed_1701_; lean_object* v_res_1702_; 
v_useEq_boxed_1701_ = lean_unbox(v_useEq_1695_);
v_res_1702_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1694_, v_useEq_boxed_1701_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(lean_object* v_00_u03b1_1703_, lean_object* v_bs_1704_, lean_object* v_k_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1704_, v_k_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1712_, lean_object* v_bs_1713_, lean_object* v_k_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(v_00_u03b1_1712_, v_bs_1713_, v_k_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec_ref(v_bs_1713_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(lean_object* v_00_u03b1_1721_, lean_object* v_bs_1722_, lean_object* v_k_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1722_, v_k_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___boxed(lean_object* v_00_u03b1_1730_, lean_object* v_bs_1731_, lean_object* v_k_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(v_00_u03b1_1730_, v_bs_1731_, v_k_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(lean_object* v_ctorVal_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
uint8_t v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = 0;
v___x_1746_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1739_, v___x_1745_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f___boxed(lean_object* v_ctorVal_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
lean_dec(v_a_1751_);
lean_dec_ref(v_a_1750_);
lean_dec(v_a_1749_);
lean_dec_ref(v_a_1748_);
return v_res_1753_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1(void){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0));
v___x_1756_ = l_Lean_stringToMessageData(v___x_1755_);
return v___x_1756_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2));
v___x_1759_ = l_Lean_stringToMessageData(v___x_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(lean_object* v_ctorName_1760_){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1761_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1);
v___x_1762_ = l_Lean_MessageData_ofName(v_ctorName_1760_);
v___x_1763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3);
v___x_1765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1763_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(lean_object* v_ctorName_1766_, lean_object* v_mvarId_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1773_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_ctorName_1766_);
v___x_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1774_, 0, v_mvarId_1767_);
v___x_1775_ = l_Lean_indentD(v___x_1774_);
v___x_1776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1773_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1776_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg___boxed(lean_object* v_ctorName_1778_, lean_object* v_mvarId_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1778_, v_mvarId_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(lean_object* v_00_u03b1_1786_, lean_object* v_ctorName_1787_, lean_object* v_mvarId_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1787_, v_mvarId_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___boxed(lean_object* v_00_u03b1_1795_, lean_object* v_ctorName_1796_, lean_object* v_mvarId_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(v_00_u03b1_1795_, v_ctorName_1796_, v_mvarId_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(lean_object* v_ctorName_1804_, lean_object* v_as_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
if (lean_obj_tag(v_as_1805_) == 0)
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
lean_dec(v_ctorName_1804_);
v___x_1811_ = lean_box(0);
v___x_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
return v___x_1812_;
}
else
{
lean_object* v_head_1813_; lean_object* v_tail_1814_; lean_object* v___x_1815_; 
v_head_1813_ = lean_ctor_get(v_as_1805_, 0);
lean_inc_n(v_head_1813_, 2);
v_tail_1814_ = lean_ctor_get(v_as_1805_, 1);
lean_inc(v_tail_1814_);
lean_dec_ref(v_as_1805_);
v___x_1815_ = l_Lean_MVarId_assumptionCore(v_head_1813_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; uint8_t v___x_1817_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_a_1816_);
lean_dec_ref(v___x_1815_);
v___x_1817_ = lean_unbox(v_a_1816_);
lean_dec(v_a_1816_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; 
lean_dec(v_tail_1814_);
v___x_1818_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1804_, v_head_1813_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
return v___x_1818_;
}
else
{
lean_dec(v_head_1813_);
v_as_1805_ = v_tail_1814_;
goto _start;
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec(v_tail_1814_);
lean_dec(v_head_1813_);
lean_dec(v_ctorName_1804_);
v_a_1820_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1815_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1815_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0___boxed(lean_object* v_ctorName_1828_, lean_object* v_as_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1828_, v_as_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(lean_object* v_mvarId_1836_, lean_object* v_ctorName_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_MVarId_splitAndCore(v_mvarId_1836_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1845_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref(v___x_1843_);
v___x_1845_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1837_, v_a_1844_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
return v___x_1845_;
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_dec(v_ctorName_1837_);
v_a_1846_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1843_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1843_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption___boxed(lean_object* v_mvarId_1854_, lean_object* v_ctorName_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_1854_, v_ctorName_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(lean_object* v_msg_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___f_1869_; lean_object* v___x_1014__overap_1870_; lean_object* v___x_1871_; 
v___f_1869_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0));
v___x_1014__overap_1870_ = lean_panic_fn_borrowed(v___f_1869_, v_msg_1863_);
lean_inc(v___y_1867_);
lean_inc_ref(v___y_1866_);
lean_inc(v___y_1865_);
lean_inc_ref(v___y_1864_);
v___x_1871_ = lean_apply_5(v___x_1014__overap_1870_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, lean_box(0));
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___boxed(lean_object* v_msg_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v_msg_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
return v_res_1878_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1879_; double v___x_1880_; 
v___x_1879_ = lean_unsigned_to_nat(0u);
v___x_1880_ = lean_float_of_nat(v___x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(lean_object* v_cls_1884_, lean_object* v_msg_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_ref_1891_; lean_object* v___x_1892_; lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1937_; 
v_ref_1891_ = lean_ctor_get(v___y_1888_, 5);
v___x_1892_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1937_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1937_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; lean_object* v_traceState_1898_; lean_object* v_env_1899_; lean_object* v_nextMacroScope_1900_; lean_object* v_ngen_1901_; lean_object* v_auxDeclNGen_1902_; lean_object* v_cache_1903_; lean_object* v_messages_1904_; lean_object* v_infoState_1905_; lean_object* v_snapshotTasks_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1936_; 
v___x_1897_ = lean_st_ref_take(v___y_1889_);
v_traceState_1898_ = lean_ctor_get(v___x_1897_, 4);
v_env_1899_ = lean_ctor_get(v___x_1897_, 0);
v_nextMacroScope_1900_ = lean_ctor_get(v___x_1897_, 1);
v_ngen_1901_ = lean_ctor_get(v___x_1897_, 2);
v_auxDeclNGen_1902_ = lean_ctor_get(v___x_1897_, 3);
v_cache_1903_ = lean_ctor_get(v___x_1897_, 5);
v_messages_1904_ = lean_ctor_get(v___x_1897_, 6);
v_infoState_1905_ = lean_ctor_get(v___x_1897_, 7);
v_snapshotTasks_1906_ = lean_ctor_get(v___x_1897_, 8);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1908_ = v___x_1897_;
v_isShared_1909_ = v_isSharedCheck_1936_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_snapshotTasks_1906_);
lean_inc(v_infoState_1905_);
lean_inc(v_messages_1904_);
lean_inc(v_cache_1903_);
lean_inc(v_traceState_1898_);
lean_inc(v_auxDeclNGen_1902_);
lean_inc(v_ngen_1901_);
lean_inc(v_nextMacroScope_1900_);
lean_inc(v_env_1899_);
lean_dec(v___x_1897_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1936_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
uint64_t v_tid_1910_; lean_object* v_traces_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1935_; 
v_tid_1910_ = lean_ctor_get_uint64(v_traceState_1898_, sizeof(void*)*1);
v_traces_1911_ = lean_ctor_get(v_traceState_1898_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v_traceState_1898_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1913_ = v_traceState_1898_;
v_isShared_1914_ = v_isSharedCheck_1935_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_traces_1911_);
lean_dec(v_traceState_1898_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1935_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1915_; double v___x_1916_; uint8_t v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1915_ = lean_box(0);
v___x_1916_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
v___x_1917_ = 0;
v___x_1918_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_1919_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1919_, 0, v_cls_1884_);
lean_ctor_set(v___x_1919_, 1, v___x_1915_);
lean_ctor_set(v___x_1919_, 2, v___x_1918_);
lean_ctor_set_float(v___x_1919_, sizeof(void*)*3, v___x_1916_);
lean_ctor_set_float(v___x_1919_, sizeof(void*)*3 + 8, v___x_1916_);
lean_ctor_set_uint8(v___x_1919_, sizeof(void*)*3 + 16, v___x_1917_);
v___x_1920_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__2));
v___x_1921_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1919_);
lean_ctor_set(v___x_1921_, 1, v_a_1893_);
lean_ctor_set(v___x_1921_, 2, v___x_1920_);
lean_inc(v_ref_1891_);
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v_ref_1891_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = l_Lean_PersistentArray_push___redArg(v_traces_1911_, v___x_1922_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 0, v___x_1923_);
v___x_1925_ = v___x_1913_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1923_);
lean_ctor_set_uint64(v_reuseFailAlloc_1934_, sizeof(void*)*1, v_tid_1910_);
v___x_1925_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
lean_object* v___x_1927_; 
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 4, v___x_1925_);
v___x_1927_ = v___x_1908_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_env_1899_);
lean_ctor_set(v_reuseFailAlloc_1933_, 1, v_nextMacroScope_1900_);
lean_ctor_set(v_reuseFailAlloc_1933_, 2, v_ngen_1901_);
lean_ctor_set(v_reuseFailAlloc_1933_, 3, v_auxDeclNGen_1902_);
lean_ctor_set(v_reuseFailAlloc_1933_, 4, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1933_, 5, v_cache_1903_);
lean_ctor_set(v_reuseFailAlloc_1933_, 6, v_messages_1904_);
lean_ctor_set(v_reuseFailAlloc_1933_, 7, v_infoState_1905_);
lean_ctor_set(v_reuseFailAlloc_1933_, 8, v_snapshotTasks_1906_);
v___x_1927_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1928_ = lean_st_ref_set(v___y_1889_, v___x_1927_);
v___x_1929_ = lean_box(0);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v___x_1929_);
v___x_1931_ = v___x_1895_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___boxed(lean_object* v_cls_1938_, lean_object* v_msg_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_1938_, v_msg_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
return v_res_1945_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3(void){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1949_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_1950_ = lean_unsigned_to_nat(30u);
v___x_1951_ = lean_unsigned_to_nat(96u);
v___x_1952_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1));
v___x_1953_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0));
v___x_1954_ = l_mkPanicMessageWithDecl(v___x_1953_, v___x_1952_, v___x_1951_, v___x_1950_, v___x_1949_);
return v___x_1954_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9(void){
_start:
{
lean_object* v_cls_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v_cls_1963_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_1964_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8));
v___x_1965_ = l_Lean_Name_append(v___x_1964_, v_cls_1963_);
return v___x_1965_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10));
v___x_1968_ = l_Lean_stringToMessageData(v___x_1967_);
return v___x_1968_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13(void){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12));
v___x_1971_ = l_Lean_stringToMessageData(v___x_1970_);
return v___x_1971_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15(void){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__14));
v___x_1974_ = l_Lean_stringToMessageData(v___x_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(lean_object* v_ctorName_1975_, lean_object* v_mvarId_1976_, lean_object* v_h_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v_options_2003_; uint8_t v_hasTrace_2004_; 
v_options_2003_ = lean_ctor_get(v_a_1980_, 2);
v_hasTrace_2004_ = lean_ctor_get_uint8(v_options_2003_, sizeof(void*)*1);
if (v_hasTrace_2004_ == 0)
{
v___y_1984_ = v_a_1978_;
v___y_1985_ = v_a_1979_;
v___y_1986_ = v_a_1980_;
v___y_1987_ = v_a_1981_;
goto v___jp_1983_;
}
else
{
lean_object* v_inheritedTraceOptions_2005_; lean_object* v_cls_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v_inheritedTraceOptions_2005_ = lean_ctor_get(v_a_1980_, 13);
v_cls_2006_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2007_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2008_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2005_, v_options_2003_, v___x_2007_);
if (v___x_2008_ == 0)
{
v___y_1984_ = v_a_1978_;
v___y_1985_ = v_a_1979_;
v___y_1986_ = v_a_1980_;
v___y_1987_ = v_a_1981_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2009_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11);
lean_inc(v_ctorName_1975_);
v___x_2010_ = l_Lean_MessageData_ofName(v_ctorName_1975_);
v___x_2011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2009_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13);
v___x_2013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2011_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
lean_inc(v_h_1977_);
v___x_2014_ = l_Lean_mkFVar(v_h_1977_);
v___x_2015_ = l_Lean_MessageData_ofExpr(v___x_2014_);
v___x_2016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2013_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
v___x_2017_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15);
v___x_2018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2016_);
lean_ctor_set(v___x_2018_, 1, v___x_2017_);
lean_inc(v_mvarId_1976_);
v___x_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2019_, 0, v_mvarId_1976_);
v___x_2020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2018_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
v___x_2021_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2006_, v___x_2020_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_dec_ref(v___x_2021_);
v___y_1984_ = v_a_1978_;
v___y_1985_ = v_a_1979_;
v___y_1986_ = v_a_1980_;
v___y_1987_ = v_a_1981_;
goto v___jp_1983_;
}
else
{
lean_dec(v_h_1977_);
lean_dec(v_mvarId_1976_);
lean_dec(v_ctorName_1975_);
return v___x_2021_;
}
}
}
v___jp_1983_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = lean_box(0);
v___x_1989_ = l_Lean_Meta_injection(v_mvarId_1976_, v_h_1977_, v___x_1988_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1990_);
lean_dec_ref(v___x_1989_);
if (lean_obj_tag(v_a_1990_) == 0)
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
lean_dec(v_ctorName_1975_);
v___x_1991_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3);
v___x_1992_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v___x_1991_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
return v___x_1992_;
}
else
{
lean_object* v_mvarId_1993_; lean_object* v___x_1994_; 
v_mvarId_1993_ = lean_ctor_get(v_a_1990_, 0);
lean_inc(v_mvarId_1993_);
lean_dec_ref(v_a_1990_);
v___x_1994_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_1993_, v_ctorName_1975_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
return v___x_1994_;
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec(v_ctorName_1975_);
v_a_1995_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1989_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1989_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___boxed(lean_object* v_ctorName_2022_, lean_object* v_mvarId_2023_, lean_object* v_h_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2022_, v_mvarId_2023_, v_h_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_);
lean_dec(v_a_2028_);
lean_dec_ref(v_a_2027_);
lean_dec(v_a_2026_);
lean_dec_ref(v_a_2025_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(lean_object* v_type_2031_, lean_object* v_k_2032_, uint8_t v_cleanupAnnotations_2033_, uint8_t v_whnfType_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v___f_2040_; lean_object* v___x_2041_; 
v___f_2040_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2040_, 0, v_k_2032_);
v___x_2041_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2031_, v___f_2040_, v_cleanupAnnotations_2033_, v_whnfType_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
v_a_2050_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2041_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2041_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg___boxed(lean_object* v_type_2058_, lean_object* v_k_2059_, lean_object* v_cleanupAnnotations_2060_, lean_object* v_whnfType_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2067_; uint8_t v_whnfType_boxed_2068_; lean_object* v_res_2069_; 
v_cleanupAnnotations_boxed_2067_ = lean_unbox(v_cleanupAnnotations_2060_);
v_whnfType_boxed_2068_ = lean_unbox(v_whnfType_2061_);
v_res_2069_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2058_, v_k_2059_, v_cleanupAnnotations_boxed_2067_, v_whnfType_boxed_2068_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(lean_object* v_00_u03b1_2070_, lean_object* v_type_2071_, lean_object* v_k_2072_, uint8_t v_cleanupAnnotations_2073_, uint8_t v_whnfType_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2071_, v_k_2072_, v_cleanupAnnotations_2073_, v_whnfType_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___boxed(lean_object* v_00_u03b1_2081_, lean_object* v_type_2082_, lean_object* v_k_2083_, lean_object* v_cleanupAnnotations_2084_, lean_object* v_whnfType_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2091_; uint8_t v_whnfType_boxed_2092_; lean_object* v_res_2093_; 
v_cleanupAnnotations_boxed_2091_ = lean_unbox(v_cleanupAnnotations_2084_);
v_whnfType_boxed_2092_ = lean_unbox(v_whnfType_2085_);
v_res_2093_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(v_00_u03b1_2081_, v_type_2082_, v_k_2083_, v_cleanupAnnotations_boxed_2091_, v_whnfType_boxed_2092_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(lean_object* v___x_2094_, lean_object* v_ctorName_2095_, lean_object* v_xs_2096_, lean_object* v_type_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = lean_box(0);
v___x_2104_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2097_, v___x_2103_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref(v___x_2104_);
v___x_2106_ = l_Lean_Expr_mvarId_x21(v_a_2105_);
v___x_2107_ = lean_array_get_size(v_xs_2096_);
v___x_2108_ = lean_unsigned_to_nat(1u);
v___x_2109_ = lean_nat_sub(v___x_2107_, v___x_2108_);
v___x_2110_ = lean_array_get_borrowed(v___x_2094_, v_xs_2096_, v___x_2109_);
lean_dec(v___x_2109_);
v___x_2111_ = l_Lean_Expr_fvarId_x21(v___x_2110_);
v___x_2112_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2095_, v___x_2106_, v___x_2111_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
if (lean_obj_tag(v___x_2112_) == 0)
{
uint8_t v___x_2113_; uint8_t v___x_2114_; uint8_t v___x_2115_; lean_object* v___x_2116_; 
lean_dec_ref(v___x_2112_);
v___x_2113_ = 0;
v___x_2114_ = 1;
v___x_2115_ = 1;
v___x_2116_ = l_Lean_Meta_mkLambdaFVars(v_xs_2096_, v_a_2105_, v___x_2113_, v___x_2114_, v___x_2113_, v___x_2114_, v___x_2115_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
return v___x_2116_;
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec(v_a_2105_);
v_a_2117_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2112_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2112_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
else
{
lean_dec(v_ctorName_2095_);
return v___x_2104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed(lean_object* v___x_2125_, lean_object* v_ctorName_2126_, lean_object* v_xs_2127_, lean_object* v_type_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(v___x_2125_, v_ctorName_2126_, v_xs_2127_, v_type_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec_ref(v_xs_2127_);
lean_dec_ref(v___x_2125_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(lean_object* v_ctorName_2135_, lean_object* v_targetType_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_){
_start:
{
lean_object* v___x_2142_; lean_object* v___f_2143_; uint8_t v___x_2144_; lean_object* v___x_2145_; 
v___x_2142_ = l_Lean_instInhabitedExpr;
v___f_2143_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2143_, 0, v___x_2142_);
lean_closure_set(v___f_2143_, 1, v_ctorName_2135_);
v___x_2144_ = 0;
v___x_2145_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_2136_, v___f_2143_, v___x_2144_, v___x_2144_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___boxed(lean_object* v_ctorName_2146_, lean_object* v_targetType_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_ctorName_2146_, v_targetType_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_);
lean_dec(v_a_2151_);
lean_dec_ref(v_a_2150_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor(lean_object* v_ctorName_2157_){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1));
v___x_2159_ = l_Lean_Name_append(v_ctorName_2157_, v___x_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(lean_object* v_e_2160_, lean_object* v___y_2161_){
_start:
{
uint8_t v___x_2163_; 
v___x_2163_ = l_Lean_Expr_hasMVar(v_e_2160_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2164_; 
v___x_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2164_, 0, v_e_2160_);
return v___x_2164_;
}
else
{
lean_object* v___x_2165_; lean_object* v_mctx_2166_; lean_object* v___x_2167_; lean_object* v_fst_2168_; lean_object* v_snd_2169_; lean_object* v___x_2170_; lean_object* v_cache_2171_; lean_object* v_zetaDeltaFVarIds_2172_; lean_object* v_postponed_2173_; lean_object* v_diag_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2183_; 
v___x_2165_ = lean_st_ref_get(v___y_2161_);
v_mctx_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc_ref(v_mctx_2166_);
lean_dec(v___x_2165_);
v___x_2167_ = l_Lean_instantiateMVarsCore(v_mctx_2166_, v_e_2160_);
v_fst_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_fst_2168_);
v_snd_2169_ = lean_ctor_get(v___x_2167_, 1);
lean_inc(v_snd_2169_);
lean_dec_ref(v___x_2167_);
v___x_2170_ = lean_st_ref_take(v___y_2161_);
v_cache_2171_ = lean_ctor_get(v___x_2170_, 1);
v_zetaDeltaFVarIds_2172_ = lean_ctor_get(v___x_2170_, 2);
v_postponed_2173_ = lean_ctor_get(v___x_2170_, 3);
v_diag_2174_ = lean_ctor_get(v___x_2170_, 4);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2183_ == 0)
{
lean_object* v_unused_2184_; 
v_unused_2184_ = lean_ctor_get(v___x_2170_, 0);
lean_dec(v_unused_2184_);
v___x_2176_ = v___x_2170_;
v_isShared_2177_ = v_isSharedCheck_2183_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_diag_2174_);
lean_inc(v_postponed_2173_);
lean_inc(v_zetaDeltaFVarIds_2172_);
lean_inc(v_cache_2171_);
lean_dec(v___x_2170_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2183_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v_snd_2169_);
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_snd_2169_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_cache_2171_);
lean_ctor_set(v_reuseFailAlloc_2182_, 2, v_zetaDeltaFVarIds_2172_);
lean_ctor_set(v_reuseFailAlloc_2182_, 3, v_postponed_2173_);
lean_ctor_set(v_reuseFailAlloc_2182_, 4, v_diag_2174_);
v___x_2179_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = lean_st_ref_set(v___y_2161_, v___x_2179_);
v___x_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2181_, 0, v_fst_2168_);
return v___x_2181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___boxed(lean_object* v_e_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2185_, v___y_2186_);
lean_dec(v___y_2186_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(lean_object* v_e_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2189_, v___y_2191_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___boxed(lean_object* v_e_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(v_e_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
return v_res_2202_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = lean_unsigned_to_nat(32u);
v___x_2204_ = lean_mk_empty_array_with_capacity(v___x_2203_);
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
return v___x_2205_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2206_ = ((size_t)5ULL);
v___x_2207_ = lean_unsigned_to_nat(0u);
v___x_2208_ = lean_unsigned_to_nat(32u);
v___x_2209_ = lean_mk_empty_array_with_capacity(v___x_2208_);
v___x_2210_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0);
v___x_2211_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
lean_ctor_set(v___x_2211_, 1, v___x_2209_);
lean_ctor_set(v___x_2211_, 2, v___x_2207_);
lean_ctor_set(v___x_2211_, 3, v___x_2207_);
lean_ctor_set_usize(v___x_2211_, 4, v___x_2206_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(lean_object* v___y_2212_){
_start:
{
lean_object* v___x_2214_; lean_object* v_traceState_2215_; lean_object* v_traces_2216_; lean_object* v___x_2217_; lean_object* v_traceState_2218_; lean_object* v_env_2219_; lean_object* v_nextMacroScope_2220_; lean_object* v_ngen_2221_; lean_object* v_auxDeclNGen_2222_; lean_object* v_cache_2223_; lean_object* v_messages_2224_; lean_object* v_infoState_2225_; lean_object* v_snapshotTasks_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2245_; 
v___x_2214_ = lean_st_ref_get(v___y_2212_);
v_traceState_2215_ = lean_ctor_get(v___x_2214_, 4);
lean_inc_ref(v_traceState_2215_);
lean_dec(v___x_2214_);
v_traces_2216_ = lean_ctor_get(v_traceState_2215_, 0);
lean_inc_ref(v_traces_2216_);
lean_dec_ref(v_traceState_2215_);
v___x_2217_ = lean_st_ref_take(v___y_2212_);
v_traceState_2218_ = lean_ctor_get(v___x_2217_, 4);
v_env_2219_ = lean_ctor_get(v___x_2217_, 0);
v_nextMacroScope_2220_ = lean_ctor_get(v___x_2217_, 1);
v_ngen_2221_ = lean_ctor_get(v___x_2217_, 2);
v_auxDeclNGen_2222_ = lean_ctor_get(v___x_2217_, 3);
v_cache_2223_ = lean_ctor_get(v___x_2217_, 5);
v_messages_2224_ = lean_ctor_get(v___x_2217_, 6);
v_infoState_2225_ = lean_ctor_get(v___x_2217_, 7);
v_snapshotTasks_2226_ = lean_ctor_get(v___x_2217_, 8);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2228_ = v___x_2217_;
v_isShared_2229_ = v_isSharedCheck_2245_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_snapshotTasks_2226_);
lean_inc(v_infoState_2225_);
lean_inc(v_messages_2224_);
lean_inc(v_cache_2223_);
lean_inc(v_traceState_2218_);
lean_inc(v_auxDeclNGen_2222_);
lean_inc(v_ngen_2221_);
lean_inc(v_nextMacroScope_2220_);
lean_inc(v_env_2219_);
lean_dec(v___x_2217_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2245_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
uint64_t v_tid_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2243_; 
v_tid_2230_ = lean_ctor_get_uint64(v_traceState_2218_, sizeof(void*)*1);
v_isSharedCheck_2243_ = !lean_is_exclusive(v_traceState_2218_);
if (v_isSharedCheck_2243_ == 0)
{
lean_object* v_unused_2244_; 
v_unused_2244_ = lean_ctor_get(v_traceState_2218_, 0);
lean_dec(v_unused_2244_);
v___x_2232_ = v_traceState_2218_;
v_isShared_2233_ = v_isSharedCheck_2243_;
goto v_resetjp_2231_;
}
else
{
lean_dec(v_traceState_2218_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2243_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2234_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v___x_2234_);
v___x_2236_ = v___x_2232_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2234_);
lean_ctor_set_uint64(v_reuseFailAlloc_2242_, sizeof(void*)*1, v_tid_2230_);
v___x_2236_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
lean_object* v___x_2238_; 
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 4, v___x_2236_);
v___x_2238_ = v___x_2228_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_env_2219_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_nextMacroScope_2220_);
lean_ctor_set(v_reuseFailAlloc_2241_, 2, v_ngen_2221_);
lean_ctor_set(v_reuseFailAlloc_2241_, 3, v_auxDeclNGen_2222_);
lean_ctor_set(v_reuseFailAlloc_2241_, 4, v___x_2236_);
lean_ctor_set(v_reuseFailAlloc_2241_, 5, v_cache_2223_);
lean_ctor_set(v_reuseFailAlloc_2241_, 6, v_messages_2224_);
lean_ctor_set(v_reuseFailAlloc_2241_, 7, v_infoState_2225_);
lean_ctor_set(v_reuseFailAlloc_2241_, 8, v_snapshotTasks_2226_);
v___x_2238_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = lean_st_ref_set(v___y_2212_, v___x_2238_);
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v_traces_2216_);
return v___x_2240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___boxed(lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2246_);
lean_dec(v___y_2246_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v___x_2254_; 
v___x_2254_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2252_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___boxed(lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
return v_res_2260_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(lean_object* v_opts_2261_, lean_object* v_opt_2262_){
_start:
{
lean_object* v_name_2263_; lean_object* v_defValue_2264_; lean_object* v_map_2265_; lean_object* v___x_2266_; 
v_name_2263_ = lean_ctor_get(v_opt_2262_, 0);
v_defValue_2264_ = lean_ctor_get(v_opt_2262_, 1);
v_map_2265_ = lean_ctor_get(v_opts_2261_, 0);
v___x_2266_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2265_, v_name_2263_);
if (lean_obj_tag(v___x_2266_) == 0)
{
uint8_t v___x_2267_; 
v___x_2267_ = lean_unbox(v_defValue_2264_);
return v___x_2267_;
}
else
{
lean_object* v_val_2268_; 
v_val_2268_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_val_2268_);
lean_dec_ref(v___x_2266_);
if (lean_obj_tag(v_val_2268_) == 1)
{
uint8_t v_v_2269_; 
v_v_2269_ = lean_ctor_get_uint8(v_val_2268_, 0);
lean_dec_ref(v_val_2268_);
return v_v_2269_;
}
else
{
uint8_t v___x_2270_; 
lean_dec(v_val_2268_);
v___x_2270_ = lean_unbox(v_defValue_2264_);
return v___x_2270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___boxed(lean_object* v_opts_2271_, lean_object* v_opt_2272_){
_start:
{
uint8_t v_res_2273_; lean_object* v_r_2274_; 
v_res_2273_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2271_, v_opt_2272_);
lean_dec_ref(v_opt_2272_);
lean_dec_ref(v_opts_2271_);
v_r_2274_ = lean_box(v_res_2273_);
return v_r_2274_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0));
v___x_2277_ = l_Lean_stringToMessageData(v___x_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(lean_object* v_name_2278_, lean_object* v_x_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2285_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1);
v___x_2286_ = l_Lean_MessageData_ofName(v_name_2278_);
v___x_2287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2285_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
v___x_2288_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_2289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2287_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed(lean_object* v_name_2291_, lean_object* v_x_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(v_name_2291_, v_x_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec_ref(v_x_2292_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(lean_object* v_name_2299_, lean_object* v_val_2300_, lean_object* v_name_2301_, lean_object* v_levelParams_2302_, uint8_t v___x_2303_, lean_object* v_____r_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v___x_2310_; 
lean_inc_ref(v_val_2300_);
v___x_2310_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2299_, v_val_2300_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2312_; lean_object* v_a_2313_; lean_object* v___x_2314_; lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2327_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref(v___x_2310_);
v___x_2312_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2300_, v___y_2306_);
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
lean_dec_ref(v___x_2312_);
v___x_2314_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2311_, v___y_2306_);
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2317_ = v___x_2314_;
v_isShared_2318_ = v_isSharedCheck_2327_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2314_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2327_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2324_; 
lean_inc(v_name_2301_);
v___x_2319_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2319_, 0, v_name_2301_);
lean_ctor_set(v___x_2319_, 1, v_levelParams_2302_);
lean_ctor_set(v___x_2319_, 2, v_a_2313_);
v___x_2320_ = lean_box(0);
v___x_2321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2321_, 0, v_name_2301_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2319_);
lean_ctor_set(v___x_2322_, 1, v_a_2315_);
lean_ctor_set(v___x_2322_, 2, v___x_2321_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set_tag(v___x_2317_, 2);
lean_ctor_set(v___x_2317_, 0, v___x_2322_);
v___x_2324_ = v___x_2317_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2322_);
v___x_2324_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_addDecl(v___x_2324_, v___x_2303_, v___y_2307_, v___y_2308_);
return v___x_2325_;
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec(v_levelParams_2302_);
lean_dec(v_name_2301_);
lean_dec_ref(v_val_2300_);
v_a_2328_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2310_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2310_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed(lean_object* v_name_2336_, lean_object* v_val_2337_, lean_object* v_name_2338_, lean_object* v_levelParams_2339_, lean_object* v___x_2340_, lean_object* v_____r_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
uint8_t v___x_12938__boxed_2347_; lean_object* v_res_2348_; 
v___x_12938__boxed_2347_ = lean_unbox(v___x_2340_);
v_res_2348_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2336_, v_val_2337_, v_name_2338_, v_levelParams_2339_, v___x_12938__boxed_2347_, v_____r_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(lean_object* v_name_2349_, lean_object* v_val_2350_, lean_object* v_name_2351_, lean_object* v_levelParams_2352_, lean_object* v_____r_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v___x_2359_; 
lean_inc_ref(v_val_2350_);
v___x_2359_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2349_, v_val_2350_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2361_; lean_object* v_a_2362_; lean_object* v___x_2363_; lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2377_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
lean_dec_ref(v___x_2359_);
v___x_2361_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2350_, v___y_2355_);
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref(v___x_2361_);
v___x_2363_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2360_, v___y_2355_);
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2366_ = v___x_2363_;
v_isShared_2367_ = v_isSharedCheck_2377_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2363_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2377_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2373_; 
lean_inc(v_name_2351_);
v___x_2368_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2368_, 0, v_name_2351_);
lean_ctor_set(v___x_2368_, 1, v_levelParams_2352_);
lean_ctor_set(v___x_2368_, 2, v_a_2362_);
v___x_2369_ = lean_box(0);
v___x_2370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2370_, 0, v_name_2351_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
v___x_2371_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2368_);
lean_ctor_set(v___x_2371_, 1, v_a_2364_);
lean_ctor_set(v___x_2371_, 2, v___x_2370_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set_tag(v___x_2366_, 2);
lean_ctor_set(v___x_2366_, 0, v___x_2371_);
v___x_2373_ = v___x_2366_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
uint8_t v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = 0;
v___x_2375_ = l_Lean_addDecl(v___x_2373_, v___x_2374_, v___y_2356_, v___y_2357_);
return v___x_2375_;
}
}
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
lean_dec(v_levelParams_2352_);
lean_dec(v_name_2351_);
lean_dec_ref(v_val_2350_);
v_a_2378_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2359_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2359_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2___boxed(lean_object* v_name_2386_, lean_object* v_val_2387_, lean_object* v_name_2388_, lean_object* v_levelParams_2389_, lean_object* v_____r_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2386_, v_val_2387_, v_name_2388_, v_levelParams_2389_, v_____r_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
return v_res_2396_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(lean_object* v_e_2397_){
_start:
{
if (lean_obj_tag(v_e_2397_) == 0)
{
uint8_t v___x_2398_; 
v___x_2398_ = 2;
return v___x_2398_;
}
else
{
uint8_t v___x_2399_; 
v___x_2399_ = 0;
return v___x_2399_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3___boxed(lean_object* v_e_2400_){
_start:
{
uint8_t v_res_2401_; lean_object* v_r_2402_; 
v_res_2401_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_e_2400_);
lean_dec_ref(v_e_2400_);
v_r_2402_ = lean_box(v_res_2401_);
return v_r_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(lean_object* v_opts_2403_, lean_object* v_opt_2404_){
_start:
{
lean_object* v_name_2405_; lean_object* v_defValue_2406_; lean_object* v_map_2407_; lean_object* v___x_2408_; 
v_name_2405_ = lean_ctor_get(v_opt_2404_, 0);
v_defValue_2406_ = lean_ctor_get(v_opt_2404_, 1);
v_map_2407_ = lean_ctor_get(v_opts_2403_, 0);
v___x_2408_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2407_, v_name_2405_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_inc(v_defValue_2406_);
return v_defValue_2406_;
}
else
{
lean_object* v_val_2409_; 
v_val_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_val_2409_);
lean_dec_ref(v___x_2408_);
if (lean_obj_tag(v_val_2409_) == 3)
{
lean_object* v_v_2410_; 
v_v_2410_ = lean_ctor_get(v_val_2409_, 0);
lean_inc(v_v_2410_);
lean_dec_ref(v_val_2409_);
return v_v_2410_;
}
else
{
lean_dec(v_val_2409_);
lean_inc(v_defValue_2406_);
return v_defValue_2406_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6___boxed(lean_object* v_opts_2411_, lean_object* v_opt_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2411_, v_opt_2412_);
lean_dec_ref(v_opt_2412_);
lean_dec_ref(v_opts_2411_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(lean_object* v_x_2414_){
_start:
{
if (lean_obj_tag(v_x_2414_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
v_a_2416_ = lean_ctor_get(v_x_2414_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v_x_2414_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v_x_2414_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v_x_2414_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
lean_ctor_set_tag(v___x_2418_, 1);
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
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
v_a_2424_ = lean_ctor_get(v_x_2414_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_x_2414_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v_x_2414_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v_x_2414_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
lean_ctor_set_tag(v___x_2426_, 0);
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg___boxed(lean_object* v_x_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_x_2432_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(size_t v_sz_2435_, size_t v_i_2436_, lean_object* v_bs_2437_){
_start:
{
uint8_t v___x_2438_; 
v___x_2438_ = lean_usize_dec_lt(v_i_2436_, v_sz_2435_);
if (v___x_2438_ == 0)
{
return v_bs_2437_;
}
else
{
lean_object* v_v_2439_; lean_object* v_msg_2440_; lean_object* v___x_2441_; lean_object* v_bs_x27_2442_; size_t v___x_2443_; size_t v___x_2444_; lean_object* v___x_2445_; 
v_v_2439_ = lean_array_uget_borrowed(v_bs_2437_, v_i_2436_);
v_msg_2440_ = lean_ctor_get(v_v_2439_, 1);
lean_inc_ref(v_msg_2440_);
v___x_2441_ = lean_unsigned_to_nat(0u);
v_bs_x27_2442_ = lean_array_uset(v_bs_2437_, v_i_2436_, v___x_2441_);
v___x_2443_ = ((size_t)1ULL);
v___x_2444_ = lean_usize_add(v_i_2436_, v___x_2443_);
v___x_2445_ = lean_array_uset(v_bs_x27_2442_, v_i_2436_, v_msg_2440_);
v_i_2436_ = v___x_2444_;
v_bs_2437_ = v___x_2445_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_2447_, lean_object* v_i_2448_, lean_object* v_bs_2449_){
_start:
{
size_t v_sz_boxed_2450_; size_t v_i_boxed_2451_; lean_object* v_res_2452_; 
v_sz_boxed_2450_ = lean_unbox_usize(v_sz_2447_);
lean_dec(v_sz_2447_);
v_i_boxed_2451_ = lean_unbox_usize(v_i_2448_);
lean_dec(v_i_2448_);
v_res_2452_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(v_sz_boxed_2450_, v_i_boxed_2451_, v_bs_2449_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(lean_object* v_oldTraces_2453_, lean_object* v_data_2454_, lean_object* v_ref_2455_, lean_object* v_msg_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v_fileName_2462_; lean_object* v_fileMap_2463_; lean_object* v_options_2464_; lean_object* v_currRecDepth_2465_; lean_object* v_maxRecDepth_2466_; lean_object* v_ref_2467_; lean_object* v_currNamespace_2468_; lean_object* v_openDecls_2469_; lean_object* v_initHeartbeats_2470_; lean_object* v_maxHeartbeats_2471_; lean_object* v_quotContext_2472_; lean_object* v_currMacroScope_2473_; uint8_t v_diag_2474_; lean_object* v_cancelTk_x3f_2475_; uint8_t v_suppressElabErrors_2476_; lean_object* v_inheritedTraceOptions_2477_; lean_object* v___x_2478_; lean_object* v_traceState_2479_; lean_object* v_traces_2480_; lean_object* v_ref_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; size_t v_sz_2484_; size_t v___x_2485_; lean_object* v___x_2486_; lean_object* v_msg_2487_; lean_object* v___x_2488_; lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2526_; 
v_fileName_2462_ = lean_ctor_get(v___y_2459_, 0);
v_fileMap_2463_ = lean_ctor_get(v___y_2459_, 1);
v_options_2464_ = lean_ctor_get(v___y_2459_, 2);
v_currRecDepth_2465_ = lean_ctor_get(v___y_2459_, 3);
v_maxRecDepth_2466_ = lean_ctor_get(v___y_2459_, 4);
v_ref_2467_ = lean_ctor_get(v___y_2459_, 5);
v_currNamespace_2468_ = lean_ctor_get(v___y_2459_, 6);
v_openDecls_2469_ = lean_ctor_get(v___y_2459_, 7);
v_initHeartbeats_2470_ = lean_ctor_get(v___y_2459_, 8);
v_maxHeartbeats_2471_ = lean_ctor_get(v___y_2459_, 9);
v_quotContext_2472_ = lean_ctor_get(v___y_2459_, 10);
v_currMacroScope_2473_ = lean_ctor_get(v___y_2459_, 11);
v_diag_2474_ = lean_ctor_get_uint8(v___y_2459_, sizeof(void*)*14);
v_cancelTk_x3f_2475_ = lean_ctor_get(v___y_2459_, 12);
v_suppressElabErrors_2476_ = lean_ctor_get_uint8(v___y_2459_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2477_ = lean_ctor_get(v___y_2459_, 13);
v___x_2478_ = lean_st_ref_get(v___y_2460_);
v_traceState_2479_ = lean_ctor_get(v___x_2478_, 4);
lean_inc_ref(v_traceState_2479_);
lean_dec(v___x_2478_);
v_traces_2480_ = lean_ctor_get(v_traceState_2479_, 0);
lean_inc_ref(v_traces_2480_);
lean_dec_ref(v_traceState_2479_);
v_ref_2481_ = l_Lean_replaceRef(v_ref_2455_, v_ref_2467_);
lean_inc_ref(v_inheritedTraceOptions_2477_);
lean_inc(v_cancelTk_x3f_2475_);
lean_inc(v_currMacroScope_2473_);
lean_inc(v_quotContext_2472_);
lean_inc(v_maxHeartbeats_2471_);
lean_inc(v_initHeartbeats_2470_);
lean_inc(v_openDecls_2469_);
lean_inc(v_currNamespace_2468_);
lean_inc(v_maxRecDepth_2466_);
lean_inc(v_currRecDepth_2465_);
lean_inc_ref(v_options_2464_);
lean_inc_ref(v_fileMap_2463_);
lean_inc_ref(v_fileName_2462_);
v___x_2482_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2482_, 0, v_fileName_2462_);
lean_ctor_set(v___x_2482_, 1, v_fileMap_2463_);
lean_ctor_set(v___x_2482_, 2, v_options_2464_);
lean_ctor_set(v___x_2482_, 3, v_currRecDepth_2465_);
lean_ctor_set(v___x_2482_, 4, v_maxRecDepth_2466_);
lean_ctor_set(v___x_2482_, 5, v_ref_2481_);
lean_ctor_set(v___x_2482_, 6, v_currNamespace_2468_);
lean_ctor_set(v___x_2482_, 7, v_openDecls_2469_);
lean_ctor_set(v___x_2482_, 8, v_initHeartbeats_2470_);
lean_ctor_set(v___x_2482_, 9, v_maxHeartbeats_2471_);
lean_ctor_set(v___x_2482_, 10, v_quotContext_2472_);
lean_ctor_set(v___x_2482_, 11, v_currMacroScope_2473_);
lean_ctor_set(v___x_2482_, 12, v_cancelTk_x3f_2475_);
lean_ctor_set(v___x_2482_, 13, v_inheritedTraceOptions_2477_);
lean_ctor_set_uint8(v___x_2482_, sizeof(void*)*14, v_diag_2474_);
lean_ctor_set_uint8(v___x_2482_, sizeof(void*)*14 + 1, v_suppressElabErrors_2476_);
v___x_2483_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2480_);
lean_dec_ref(v_traces_2480_);
v_sz_2484_ = lean_array_size(v___x_2483_);
v___x_2485_ = ((size_t)0ULL);
v___x_2486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(v_sz_2484_, v___x_2485_, v___x_2483_);
v_msg_2487_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2487_, 0, v_data_2454_);
lean_ctor_set(v_msg_2487_, 1, v_msg_2456_);
lean_ctor_set(v_msg_2487_, 2, v___x_2486_);
v___x_2488_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_2487_, v___y_2457_, v___y_2458_, v___x_2482_, v___y_2460_);
lean_dec_ref(v___x_2482_);
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2491_ = v___x_2488_;
v_isShared_2492_ = v_isSharedCheck_2526_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2488_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2526_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2493_; lean_object* v_traceState_2494_; lean_object* v_env_2495_; lean_object* v_nextMacroScope_2496_; lean_object* v_ngen_2497_; lean_object* v_auxDeclNGen_2498_; lean_object* v_cache_2499_; lean_object* v_messages_2500_; lean_object* v_infoState_2501_; lean_object* v_snapshotTasks_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2525_; 
v___x_2493_ = lean_st_ref_take(v___y_2460_);
v_traceState_2494_ = lean_ctor_get(v___x_2493_, 4);
v_env_2495_ = lean_ctor_get(v___x_2493_, 0);
v_nextMacroScope_2496_ = lean_ctor_get(v___x_2493_, 1);
v_ngen_2497_ = lean_ctor_get(v___x_2493_, 2);
v_auxDeclNGen_2498_ = lean_ctor_get(v___x_2493_, 3);
v_cache_2499_ = lean_ctor_get(v___x_2493_, 5);
v_messages_2500_ = lean_ctor_get(v___x_2493_, 6);
v_infoState_2501_ = lean_ctor_get(v___x_2493_, 7);
v_snapshotTasks_2502_ = lean_ctor_get(v___x_2493_, 8);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2504_ = v___x_2493_;
v_isShared_2505_ = v_isSharedCheck_2525_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_snapshotTasks_2502_);
lean_inc(v_infoState_2501_);
lean_inc(v_messages_2500_);
lean_inc(v_cache_2499_);
lean_inc(v_traceState_2494_);
lean_inc(v_auxDeclNGen_2498_);
lean_inc(v_ngen_2497_);
lean_inc(v_nextMacroScope_2496_);
lean_inc(v_env_2495_);
lean_dec(v___x_2493_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2525_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
uint64_t v_tid_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2523_; 
v_tid_2506_ = lean_ctor_get_uint64(v_traceState_2494_, sizeof(void*)*1);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_traceState_2494_);
if (v_isSharedCheck_2523_ == 0)
{
lean_object* v_unused_2524_; 
v_unused_2524_ = lean_ctor_get(v_traceState_2494_, 0);
lean_dec(v_unused_2524_);
v___x_2508_ = v_traceState_2494_;
v_isShared_2509_ = v_isSharedCheck_2523_;
goto v_resetjp_2507_;
}
else
{
lean_dec(v_traceState_2494_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2523_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2513_; 
v___x_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2510_, 0, v_ref_2455_);
lean_ctor_set(v___x_2510_, 1, v_a_2489_);
v___x_2511_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2453_, v___x_2510_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 0, v___x_2511_);
v___x_2513_ = v___x_2508_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2511_);
lean_ctor_set_uint64(v_reuseFailAlloc_2522_, sizeof(void*)*1, v_tid_2506_);
v___x_2513_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
lean_object* v___x_2515_; 
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 4, v___x_2513_);
v___x_2515_ = v___x_2504_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_env_2495_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_nextMacroScope_2496_);
lean_ctor_set(v_reuseFailAlloc_2521_, 2, v_ngen_2497_);
lean_ctor_set(v_reuseFailAlloc_2521_, 3, v_auxDeclNGen_2498_);
lean_ctor_set(v_reuseFailAlloc_2521_, 4, v___x_2513_);
lean_ctor_set(v_reuseFailAlloc_2521_, 5, v_cache_2499_);
lean_ctor_set(v_reuseFailAlloc_2521_, 6, v_messages_2500_);
lean_ctor_set(v_reuseFailAlloc_2521_, 7, v_infoState_2501_);
lean_ctor_set(v_reuseFailAlloc_2521_, 8, v_snapshotTasks_2502_);
v___x_2515_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2516_ = lean_st_ref_set(v___y_2460_, v___x_2515_);
v___x_2517_ = lean_box(0);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 0, v___x_2517_);
v___x_2519_ = v___x_2491_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2517_);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___boxed(lean_object* v_oldTraces_2527_, lean_object* v_data_2528_, lean_object* v_ref_2529_, lean_object* v_msg_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_oldTraces_2527_, v_data_2528_, v_ref_2529_, v_msg_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
return v_res_2536_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0));
v___x_2539_ = l_Lean_stringToMessageData(v___x_2538_);
return v___x_2539_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2));
v___x_2542_ = l_Lean_stringToMessageData(v___x_2541_);
return v___x_2542_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2543_; double v___x_2544_; 
v___x_2543_ = lean_unsigned_to_nat(1000u);
v___x_2544_ = lean_float_of_nat(v___x_2543_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(lean_object* v_cls_2545_, uint8_t v_collapsed_2546_, lean_object* v_tag_2547_, lean_object* v_opts_2548_, uint8_t v_clsEnabled_2549_, lean_object* v_oldTraces_2550_, lean_object* v_msg_2551_, lean_object* v_resStartStop_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v_fst_2558_; lean_object* v_snd_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2649_; 
v_fst_2558_ = lean_ctor_get(v_resStartStop_2552_, 0);
v_snd_2559_ = lean_ctor_get(v_resStartStop_2552_, 1);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_resStartStop_2552_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2561_ = v_resStartStop_2552_;
v_isShared_2562_ = v_isSharedCheck_2649_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_snd_2559_);
lean_inc(v_fst_2558_);
lean_dec(v_resStartStop_2552_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2649_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v_data_2566_; lean_object* v_fst_2569_; lean_object* v_snd_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2648_; 
v_fst_2569_ = lean_ctor_get(v_snd_2559_, 0);
v_snd_2570_ = lean_ctor_get(v_snd_2559_, 1);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_snd_2559_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2572_ = v_snd_2559_;
v_isShared_2573_ = v_isSharedCheck_2648_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_snd_2570_);
lean_inc(v_fst_2569_);
lean_dec(v_snd_2559_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2648_;
goto v_resetjp_2571_;
}
v___jp_2563_:
{
lean_object* v___x_2567_; 
lean_inc(v___y_2565_);
v___x_2567_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_oldTraces_2550_, v_data_2566_, v___y_2565_, v___y_2564_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v___x_2568_; 
lean_dec_ref(v___x_2567_);
v___x_2568_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_fst_2558_);
return v___x_2568_;
}
else
{
lean_dec(v_fst_2558_);
return v___x_2567_;
}
}
v_resetjp_2571_:
{
lean_object* v___x_2574_; uint8_t v___x_2575_; lean_object* v___y_2577_; lean_object* v_a_2578_; uint8_t v___y_2602_; double v___y_2633_; 
v___x_2574_ = l_Lean_trace_profiler;
v___x_2575_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2548_, v___x_2574_);
if (v___x_2575_ == 0)
{
v___y_2602_ = v___x_2575_;
goto v___jp_2601_;
}
else
{
lean_object* v___x_2638_; uint8_t v___x_2639_; 
v___x_2638_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2639_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2548_, v___x_2638_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; lean_object* v___x_2641_; double v___x_2642_; double v___x_2643_; double v___x_2644_; 
v___x_2640_ = l_Lean_trace_profiler_threshold;
v___x_2641_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2548_, v___x_2640_);
v___x_2642_ = lean_float_of_nat(v___x_2641_);
v___x_2643_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4);
v___x_2644_ = lean_float_div(v___x_2642_, v___x_2643_);
v___y_2633_ = v___x_2644_;
goto v___jp_2632_;
}
else
{
lean_object* v___x_2645_; lean_object* v___x_2646_; double v___x_2647_; 
v___x_2645_ = l_Lean_trace_profiler_threshold;
v___x_2646_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2548_, v___x_2645_);
v___x_2647_ = lean_float_of_nat(v___x_2646_);
v___y_2633_ = v___x_2647_;
goto v___jp_2632_;
}
}
v___jp_2576_:
{
uint8_t v_result_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2584_; 
v_result_2579_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_fst_2558_);
v___x_2580_ = l_Lean_TraceResult_toEmoji(v_result_2579_);
v___x_2581_ = l_Lean_stringToMessageData(v___x_2580_);
v___x_2582_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1);
if (v_isShared_2573_ == 0)
{
lean_ctor_set_tag(v___x_2572_, 7);
lean_ctor_set(v___x_2572_, 1, v___x_2582_);
lean_ctor_set(v___x_2572_, 0, v___x_2581_);
v___x_2584_ = v___x_2572_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2581_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v___x_2582_);
v___x_2584_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
lean_object* v_m_2586_; 
if (v_isShared_2562_ == 0)
{
lean_ctor_set_tag(v___x_2561_, 7);
lean_ctor_set(v___x_2561_, 1, v_a_2578_);
lean_ctor_set(v___x_2561_, 0, v___x_2584_);
v_m_2586_ = v___x_2561_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v_a_2578_);
v_m_2586_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; double v___x_2589_; lean_object* v_data_2590_; 
v___x_2587_ = lean_box(v_result_2579_);
v___x_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
v___x_2589_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
lean_inc_ref(v_tag_2547_);
lean_inc_ref(v___x_2588_);
lean_inc(v_cls_2545_);
v_data_2590_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2590_, 0, v_cls_2545_);
lean_ctor_set(v_data_2590_, 1, v___x_2588_);
lean_ctor_set(v_data_2590_, 2, v_tag_2547_);
lean_ctor_set_float(v_data_2590_, sizeof(void*)*3, v___x_2589_);
lean_ctor_set_float(v_data_2590_, sizeof(void*)*3 + 8, v___x_2589_);
lean_ctor_set_uint8(v_data_2590_, sizeof(void*)*3 + 16, v_collapsed_2546_);
if (v___x_2575_ == 0)
{
lean_dec_ref(v___x_2588_);
lean_dec(v_snd_2570_);
lean_dec(v_fst_2569_);
lean_dec_ref(v_tag_2547_);
lean_dec(v_cls_2545_);
v___y_2564_ = v_m_2586_;
v___y_2565_ = v___y_2577_;
v_data_2566_ = v_data_2590_;
goto v___jp_2563_;
}
else
{
lean_object* v_data_2591_; double v___x_2592_; double v___x_2593_; 
lean_dec_ref(v_data_2590_);
v_data_2591_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2591_, 0, v_cls_2545_);
lean_ctor_set(v_data_2591_, 1, v___x_2588_);
lean_ctor_set(v_data_2591_, 2, v_tag_2547_);
v___x_2592_ = lean_unbox_float(v_fst_2569_);
lean_dec(v_fst_2569_);
lean_ctor_set_float(v_data_2591_, sizeof(void*)*3, v___x_2592_);
v___x_2593_ = lean_unbox_float(v_snd_2570_);
lean_dec(v_snd_2570_);
lean_ctor_set_float(v_data_2591_, sizeof(void*)*3 + 8, v___x_2593_);
lean_ctor_set_uint8(v_data_2591_, sizeof(void*)*3 + 16, v_collapsed_2546_);
v___y_2564_ = v_m_2586_;
v___y_2565_ = v___y_2577_;
v_data_2566_ = v_data_2591_;
goto v___jp_2563_;
}
}
}
}
v___jp_2596_:
{
lean_object* v_ref_2597_; lean_object* v___x_2598_; 
v_ref_2597_ = lean_ctor_get(v___y_2555_, 5);
lean_inc(v___y_2556_);
lean_inc_ref(v___y_2555_);
lean_inc(v___y_2554_);
lean_inc_ref(v___y_2553_);
lean_inc(v_fst_2558_);
v___x_2598_ = lean_apply_6(v_msg_2551_, v_fst_2558_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, lean_box(0));
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2599_);
lean_dec_ref(v___x_2598_);
v___y_2577_ = v_ref_2597_;
v_a_2578_ = v_a_2599_;
goto v___jp_2576_;
}
else
{
lean_object* v___x_2600_; 
lean_dec_ref(v___x_2598_);
v___x_2600_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3);
v___y_2577_ = v_ref_2597_;
v_a_2578_ = v___x_2600_;
goto v___jp_2576_;
}
}
v___jp_2601_:
{
if (v_clsEnabled_2549_ == 0)
{
if (v___y_2602_ == 0)
{
lean_object* v___x_2603_; lean_object* v_traceState_2604_; lean_object* v_env_2605_; lean_object* v_nextMacroScope_2606_; lean_object* v_ngen_2607_; lean_object* v_auxDeclNGen_2608_; lean_object* v_cache_2609_; lean_object* v_messages_2610_; lean_object* v_infoState_2611_; lean_object* v_snapshotTasks_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2631_; 
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_fst_2569_);
lean_del_object(v___x_2561_);
lean_dec_ref(v_msg_2551_);
lean_dec_ref(v_tag_2547_);
lean_dec(v_cls_2545_);
v___x_2603_ = lean_st_ref_take(v___y_2556_);
v_traceState_2604_ = lean_ctor_get(v___x_2603_, 4);
v_env_2605_ = lean_ctor_get(v___x_2603_, 0);
v_nextMacroScope_2606_ = lean_ctor_get(v___x_2603_, 1);
v_ngen_2607_ = lean_ctor_get(v___x_2603_, 2);
v_auxDeclNGen_2608_ = lean_ctor_get(v___x_2603_, 3);
v_cache_2609_ = lean_ctor_get(v___x_2603_, 5);
v_messages_2610_ = lean_ctor_get(v___x_2603_, 6);
v_infoState_2611_ = lean_ctor_get(v___x_2603_, 7);
v_snapshotTasks_2612_ = lean_ctor_get(v___x_2603_, 8);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2614_ = v___x_2603_;
v_isShared_2615_ = v_isSharedCheck_2631_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_snapshotTasks_2612_);
lean_inc(v_infoState_2611_);
lean_inc(v_messages_2610_);
lean_inc(v_cache_2609_);
lean_inc(v_traceState_2604_);
lean_inc(v_auxDeclNGen_2608_);
lean_inc(v_ngen_2607_);
lean_inc(v_nextMacroScope_2606_);
lean_inc(v_env_2605_);
lean_dec(v___x_2603_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2631_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
uint64_t v_tid_2616_; lean_object* v_traces_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2630_; 
v_tid_2616_ = lean_ctor_get_uint64(v_traceState_2604_, sizeof(void*)*1);
v_traces_2617_ = lean_ctor_get(v_traceState_2604_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v_traceState_2604_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2619_ = v_traceState_2604_;
v_isShared_2620_ = v_isSharedCheck_2630_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_traces_2617_);
lean_dec(v_traceState_2604_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2630_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2621_; lean_object* v___x_2623_; 
v___x_2621_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2550_, v_traces_2617_);
lean_dec_ref(v_traces_2617_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v___x_2621_);
v___x_2623_ = v___x_2619_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2621_);
lean_ctor_set_uint64(v_reuseFailAlloc_2629_, sizeof(void*)*1, v_tid_2616_);
v___x_2623_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
lean_object* v___x_2625_; 
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 4, v___x_2623_);
v___x_2625_ = v___x_2614_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_env_2605_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v_nextMacroScope_2606_);
lean_ctor_set(v_reuseFailAlloc_2628_, 2, v_ngen_2607_);
lean_ctor_set(v_reuseFailAlloc_2628_, 3, v_auxDeclNGen_2608_);
lean_ctor_set(v_reuseFailAlloc_2628_, 4, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2628_, 5, v_cache_2609_);
lean_ctor_set(v_reuseFailAlloc_2628_, 6, v_messages_2610_);
lean_ctor_set(v_reuseFailAlloc_2628_, 7, v_infoState_2611_);
lean_ctor_set(v_reuseFailAlloc_2628_, 8, v_snapshotTasks_2612_);
v___x_2625_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2626_ = lean_st_ref_set(v___y_2556_, v___x_2625_);
v___x_2627_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_fst_2558_);
return v___x_2627_;
}
}
}
}
}
else
{
goto v___jp_2596_;
}
}
else
{
goto v___jp_2596_;
}
}
v___jp_2632_:
{
double v___x_2634_; double v___x_2635_; double v___x_2636_; uint8_t v___x_2637_; 
v___x_2634_ = lean_unbox_float(v_snd_2570_);
v___x_2635_ = lean_unbox_float(v_fst_2569_);
v___x_2636_ = lean_float_sub(v___x_2634_, v___x_2635_);
v___x_2637_ = lean_float_decLt(v___y_2633_, v___x_2636_);
v___y_2602_ = v___x_2637_;
goto v___jp_2601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___boxed(lean_object* v_cls_2650_, lean_object* v_collapsed_2651_, lean_object* v_tag_2652_, lean_object* v_opts_2653_, lean_object* v_clsEnabled_2654_, lean_object* v_oldTraces_2655_, lean_object* v_msg_2656_, lean_object* v_resStartStop_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
uint8_t v_collapsed_boxed_2663_; uint8_t v_clsEnabled_boxed_2664_; lean_object* v_res_2665_; 
v_collapsed_boxed_2663_ = lean_unbox(v_collapsed_2651_);
v_clsEnabled_boxed_2664_ = lean_unbox(v_clsEnabled_2654_);
v_res_2665_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2650_, v_collapsed_boxed_2663_, v_tag_2652_, v_opts_2653_, v_clsEnabled_boxed_2664_, v_oldTraces_2655_, v_msg_2656_, v_resStartStop_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec_ref(v_opts_2653_);
return v_res_2665_;
}
}
static double _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0(void){
_start:
{
lean_object* v___x_2666_; double v___x_2667_; 
v___x_2666_ = lean_unsigned_to_nat(1000000000u);
v___x_2667_ = lean_float_of_nat(v___x_2666_);
return v___x_2667_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2(void){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1));
v___x_2670_ = l_Lean_stringToMessageData(v___x_2669_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object* v_ctorVal_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
lean_object* v_toConstantVal_2677_; lean_object* v_options_2678_; lean_object* v_name_2679_; lean_object* v_levelParams_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2891_; 
v_toConstantVal_2677_ = lean_ctor_get(v_ctorVal_2671_, 0);
lean_inc_ref(v_toConstantVal_2677_);
v_options_2678_ = lean_ctor_get(v_a_2674_, 2);
v_name_2679_ = lean_ctor_get(v_toConstantVal_2677_, 0);
v_levelParams_2680_ = lean_ctor_get(v_toConstantVal_2677_, 1);
v_isSharedCheck_2891_ = !lean_is_exclusive(v_toConstantVal_2677_);
if (v_isSharedCheck_2891_ == 0)
{
lean_object* v_unused_2892_; 
v_unused_2892_ = lean_ctor_get(v_toConstantVal_2677_, 2);
lean_dec(v_unused_2892_);
v___x_2682_ = v_toConstantVal_2677_;
v_isShared_2683_ = v_isSharedCheck_2891_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_levelParams_2680_);
lean_inc(v_name_2679_);
lean_dec(v_toConstantVal_2677_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2891_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v_inheritedTraceOptions_2684_; uint8_t v_hasTrace_2685_; lean_object* v_name_2686_; 
v_inheritedTraceOptions_2684_ = lean_ctor_get(v_a_2674_, 13);
v_hasTrace_2685_ = lean_ctor_get_uint8(v_options_2678_, sizeof(void*)*1);
lean_inc(v_name_2679_);
v_name_2686_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_2679_);
if (v_hasTrace_2685_ == 0)
{
lean_object* v___x_2687_; 
v___x_2687_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2725_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2690_ = v___x_2687_;
v_isShared_2691_ = v_isSharedCheck_2725_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2687_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2725_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
if (lean_obj_tag(v_a_2688_) == 1)
{
lean_object* v_val_2692_; lean_object* v___x_2693_; 
lean_del_object(v___x_2690_);
v_val_2692_ = lean_ctor_get(v_a_2688_, 0);
lean_inc_n(v_val_2692_, 2);
lean_dec_ref(v_a_2688_);
v___x_2693_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2679_, v_val_2692_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2695_; lean_object* v_a_2696_; lean_object* v___x_2697_; lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2712_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref(v___x_2693_);
v___x_2695_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2692_, v_a_2673_);
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref(v___x_2695_);
v___x_2697_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2694_, v_a_2673_);
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2700_ = v___x_2697_;
v_isShared_2701_ = v_isSharedCheck_2712_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2697_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2712_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
lean_inc(v_name_2686_);
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 2, v_a_2696_);
lean_ctor_set(v___x_2682_, 0, v_name_2686_);
v___x_2703_ = v___x_2682_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_name_2686_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v_levelParams_2680_);
lean_ctor_set(v_reuseFailAlloc_2711_, 2, v_a_2696_);
v___x_2703_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2708_; 
v___x_2704_ = lean_box(0);
v___x_2705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2705_, 0, v_name_2686_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2703_);
lean_ctor_set(v___x_2706_, 1, v_a_2698_);
lean_ctor_set(v___x_2706_, 2, v___x_2705_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set_tag(v___x_2700_, 2);
lean_ctor_set(v___x_2700_, 0, v___x_2706_);
v___x_2708_ = v___x_2700_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2706_);
v___x_2708_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_addDecl(v___x_2708_, v_hasTrace_2685_, v_a_2674_, v_a_2675_);
return v___x_2709_;
}
}
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
lean_dec(v_val_2692_);
lean_dec(v_name_2686_);
lean_del_object(v___x_2682_);
lean_dec(v_levelParams_2680_);
v_a_2713_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2693_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2693_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
else
{
lean_object* v___x_2721_; lean_object* v___x_2723_; 
lean_dec(v_a_2688_);
lean_dec(v_name_2686_);
lean_del_object(v___x_2682_);
lean_dec(v_levelParams_2680_);
lean_dec(v_name_2679_);
v___x_2721_ = lean_box(0);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v___x_2721_);
v___x_2723_ = v___x_2690_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2721_);
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
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec(v_name_2686_);
lean_del_object(v___x_2682_);
lean_dec(v_levelParams_2680_);
lean_dec(v_name_2679_);
v_a_2726_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2687_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2687_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
else
{
lean_object* v___f_2734_; lean_object* v_cls_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; uint8_t v___x_2738_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v_a_2742_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v_a_2754_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v_a_2759_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v_a_2770_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v_a_2785_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v_a_2790_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; 
lean_inc(v_name_2686_);
v___f_2734_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2734_, 0, v_name_2686_);
v_cls_2735_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2736_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_2737_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2738_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2684_, v_options_2678_, v___x_2737_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2833_; uint8_t v___x_2834_; 
v___x_2833_ = l_Lean_trace_profiler;
v___x_2834_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2678_, v___x_2833_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; 
lean_dec_ref(v___f_2734_);
v___x_2835_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2882_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2838_ = v___x_2835_;
v_isShared_2839_ = v_isSharedCheck_2882_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2835_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2882_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
if (lean_obj_tag(v_a_2836_) == 1)
{
lean_object* v_val_2840_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; 
lean_del_object(v___x_2838_);
v_val_2840_ = lean_ctor_get(v_a_2836_, 0);
lean_inc(v_val_2840_);
lean_dec_ref(v_a_2836_);
if (v___x_2738_ == 0)
{
v___y_2842_ = v_a_2672_;
v___y_2843_ = v_a_2673_;
v___y_2844_ = v_a_2674_;
v___y_2845_ = v_a_2675_;
goto v___jp_2841_;
}
else
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2874_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_2840_);
v___x_2875_ = l_Lean_MessageData_ofExpr(v_val_2840_);
v___x_2876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2874_);
lean_ctor_set(v___x_2876_, 1, v___x_2875_);
v___x_2877_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2735_, v___x_2876_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_dec_ref(v___x_2877_);
v___y_2842_ = v_a_2672_;
v___y_2843_ = v_a_2673_;
v___y_2844_ = v_a_2674_;
v___y_2845_ = v_a_2675_;
goto v___jp_2841_;
}
else
{
lean_dec(v_val_2840_);
lean_dec(v_name_2686_);
lean_del_object(v___x_2682_);
lean_dec(v_levelParams_2680_);
lean_dec(v_name_2679_);
return v___x_2877_;
}
}
v___jp_2841_:
{
lean_object* v___x_2846_; 
lean_inc(v_val_2840_);
v___x_2846_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2679_, v_val_2840_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2848_; lean_object* v_a_2849_; lean_object* v___x_2850_; lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2865_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref(v___x_2846_);
v___x_2848_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2840_, v___y_2843_);
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2849_);
lean_dec_ref(v___x_2848_);
v___x_2850_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2847_, v___y_2843_);
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2853_ = v___x_2850_;
v_isShared_2854_ = v_isSharedCheck_2865_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2850_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2865_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
lean_inc(v_name_2686_);
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 2, v_a_2849_);
lean_ctor_set(v___x_2682_, 0, v_name_2686_);
v___x_2856_ = v___x_2682_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_name_2686_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v_levelParams_2680_);
lean_ctor_set(v_reuseFailAlloc_2864_, 2, v_a_2849_);
v___x_2856_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2861_; 
v___x_2857_ = lean_box(0);
v___x_2858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2858_, 0, v_name_2686_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
v___x_2859_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2856_);
lean_ctor_set(v___x_2859_, 1, v_a_2851_);
lean_ctor_set(v___x_2859_, 2, v___x_2858_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set_tag(v___x_2853_, 2);
lean_ctor_set(v___x_2853_, 0, v___x_2859_);
v___x_2861_ = v___x_2853_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___x_2859_);
v___x_2861_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
lean_object* v___x_2862_; 
v___x_2862_ = l_Lean_addDecl(v___x_2861_, v___x_2834_, v___y_2844_, v___y_2845_);
return v___x_2862_;
}
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec(v_val_2840_);
lean_dec(v_name_2686_);
lean_del_object(v___x_2682_);
lean_dec(v_levelParams_2680_);
v_a_2866_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2846_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2846_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
}
else
{
lean_object* v___x_2878_; lean_object* v___x_2880_; 
lean_dec(v_a_2836_);
lean_dec(v_name_2686_);
lean_del_object(v___x_2682_);
lean_dec(v_levelParams_2680_);
lean_dec(v_name_2679_);
v___x_2878_ = lean_box(0);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 0, v___x_2878_);
v___x_2880_ = v___x_2838_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2878_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
lean_dec(v_name_2686_);
lean_del_object(v___x_2682_);
lean_dec(v_levelParams_2680_);
lean_dec(v_name_2679_);
v_a_2883_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2835_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2835_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
else
{
lean_del_object(v___x_2682_);
goto v___jp_2798_;
}
}
else
{
lean_del_object(v___x_2682_);
goto v___jp_2798_;
}
v___jp_2739_:
{
lean_object* v___x_2743_; double v___x_2744_; double v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2743_ = lean_io_get_num_heartbeats();
v___x_2744_ = lean_float_of_nat(v___y_2741_);
v___x_2745_ = lean_float_of_nat(v___x_2743_);
v___x_2746_ = lean_box_float(v___x_2744_);
v___x_2747_ = lean_box_float(v___x_2745_);
v___x_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2746_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2749_, 0, v_a_2742_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___x_2750_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2735_, v_hasTrace_2685_, v___x_2736_, v_options_2678_, v___x_2738_, v___y_2740_, v___f_2734_, v___x_2749_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
return v___x_2750_;
}
v___jp_2751_:
{
lean_object* v___x_2755_; 
v___x_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2755_, 0, v_a_2754_);
v___y_2740_ = v___y_2752_;
v___y_2741_ = v___y_2753_;
v_a_2742_ = v___x_2755_;
goto v___jp_2739_;
}
v___jp_2756_:
{
lean_object* v___x_2760_; 
v___x_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2760_, 0, v_a_2759_);
v___y_2740_ = v___y_2757_;
v___y_2741_ = v___y_2758_;
v_a_2742_ = v___x_2760_;
goto v___jp_2739_;
}
v___jp_2761_:
{
if (lean_obj_tag(v___y_2764_) == 0)
{
lean_object* v_a_2765_; 
v_a_2765_ = lean_ctor_get(v___y_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref(v___y_2764_);
v___y_2757_ = v___y_2762_;
v___y_2758_ = v___y_2763_;
v_a_2759_ = v_a_2765_;
goto v___jp_2756_;
}
else
{
lean_object* v_a_2766_; 
v_a_2766_ = lean_ctor_get(v___y_2764_, 0);
lean_inc(v_a_2766_);
lean_dec_ref(v___y_2764_);
v___y_2752_ = v___y_2762_;
v___y_2753_ = v___y_2763_;
v_a_2754_ = v_a_2766_;
goto v___jp_2751_;
}
}
v___jp_2767_:
{
lean_object* v___x_2771_; double v___x_2772_; double v___x_2773_; double v___x_2774_; double v___x_2775_; double v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2771_ = lean_io_mono_nanos_now();
v___x_2772_ = lean_float_of_nat(v___y_2769_);
v___x_2773_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_2774_ = lean_float_div(v___x_2772_, v___x_2773_);
v___x_2775_ = lean_float_of_nat(v___x_2771_);
v___x_2776_ = lean_float_div(v___x_2775_, v___x_2773_);
v___x_2777_ = lean_box_float(v___x_2774_);
v___x_2778_ = lean_box_float(v___x_2776_);
v___x_2779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2777_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2780_, 0, v_a_2770_);
lean_ctor_set(v___x_2780_, 1, v___x_2779_);
v___x_2781_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2735_, v_hasTrace_2685_, v___x_2736_, v_options_2678_, v___x_2738_, v___y_2768_, v___f_2734_, v___x_2780_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
return v___x_2781_;
}
v___jp_2782_:
{
lean_object* v___x_2786_; 
v___x_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2786_, 0, v_a_2785_);
v___y_2768_ = v___y_2783_;
v___y_2769_ = v___y_2784_;
v_a_2770_ = v___x_2786_;
goto v___jp_2767_;
}
v___jp_2787_:
{
lean_object* v___x_2791_; 
v___x_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2791_, 0, v_a_2790_);
v___y_2768_ = v___y_2788_;
v___y_2769_ = v___y_2789_;
v_a_2770_ = v___x_2791_;
goto v___jp_2767_;
}
v___jp_2792_:
{
if (lean_obj_tag(v___y_2795_) == 0)
{
lean_object* v_a_2796_; 
v_a_2796_ = lean_ctor_get(v___y_2795_, 0);
lean_inc(v_a_2796_);
lean_dec_ref(v___y_2795_);
v___y_2783_ = v___y_2793_;
v___y_2784_ = v___y_2794_;
v_a_2785_ = v_a_2796_;
goto v___jp_2782_;
}
else
{
lean_object* v_a_2797_; 
v_a_2797_ = lean_ctor_get(v___y_2795_, 0);
lean_inc(v_a_2797_);
lean_dec_ref(v___y_2795_);
v___y_2788_ = v___y_2793_;
v___y_2789_ = v___y_2794_;
v_a_2790_ = v_a_2797_;
goto v___jp_2787_;
}
}
v___jp_2798_:
{
lean_object* v___x_2799_; lean_object* v_a_2800_; lean_object* v___x_2801_; uint8_t v___x_2802_; 
v___x_2799_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_2675_);
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref(v___x_2799_);
v___x_2801_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2802_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2678_, v___x_2801_);
if (v___x_2802_ == 0)
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = lean_io_mono_nanos_now();
v___x_2804_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2805_);
lean_dec_ref(v___x_2804_);
if (lean_obj_tag(v_a_2805_) == 1)
{
if (v___x_2738_ == 0)
{
lean_object* v_val_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v_val_2806_ = lean_ctor_get(v_a_2805_, 0);
lean_inc(v_val_2806_);
lean_dec_ref(v_a_2805_);
v___x_2807_ = lean_box(0);
v___x_2808_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2679_, v_val_2806_, v_name_2686_, v_levelParams_2680_, v___x_2802_, v___x_2807_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
v___y_2793_ = v_a_2800_;
v___y_2794_ = v___x_2803_;
v___y_2795_ = v___x_2808_;
goto v___jp_2792_;
}
else
{
lean_object* v_val_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v_val_2809_ = lean_ctor_get(v_a_2805_, 0);
lean_inc_n(v_val_2809_, 2);
lean_dec_ref(v_a_2805_);
v___x_2810_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2811_ = l_Lean_MessageData_ofExpr(v_val_2809_);
v___x_2812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2810_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
v___x_2813_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2735_, v___x_2812_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___x_2815_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref(v___x_2813_);
v___x_2815_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2679_, v_val_2809_, v_name_2686_, v_levelParams_2680_, v___x_2802_, v_a_2814_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
v___y_2793_ = v_a_2800_;
v___y_2794_ = v___x_2803_;
v___y_2795_ = v___x_2815_;
goto v___jp_2792_;
}
else
{
lean_dec(v_val_2809_);
lean_dec(v_name_2686_);
lean_dec(v_levelParams_2680_);
lean_dec(v_name_2679_);
v___y_2793_ = v_a_2800_;
v___y_2794_ = v___x_2803_;
v___y_2795_ = v___x_2813_;
goto v___jp_2792_;
}
}
}
else
{
lean_object* v___x_2816_; 
lean_dec(v_a_2805_);
lean_dec(v_name_2686_);
lean_dec(v_levelParams_2680_);
lean_dec(v_name_2679_);
v___x_2816_ = lean_box(0);
v___y_2783_ = v_a_2800_;
v___y_2784_ = v___x_2803_;
v_a_2785_ = v___x_2816_;
goto v___jp_2782_;
}
}
else
{
lean_object* v_a_2817_; 
lean_dec(v_name_2686_);
lean_dec(v_levelParams_2680_);
lean_dec(v_name_2679_);
v_a_2817_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2817_);
lean_dec_ref(v___x_2804_);
v___y_2788_ = v_a_2800_;
v___y_2789_ = v___x_2803_;
v_a_2790_ = v_a_2817_;
goto v___jp_2787_;
}
}
else
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = lean_io_get_num_heartbeats();
v___x_2819_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
lean_dec_ref(v___x_2819_);
if (lean_obj_tag(v_a_2820_) == 1)
{
if (v___x_2738_ == 0)
{
lean_object* v_val_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v_val_2821_ = lean_ctor_get(v_a_2820_, 0);
lean_inc(v_val_2821_);
lean_dec_ref(v_a_2820_);
v___x_2822_ = lean_box(0);
v___x_2823_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2679_, v_val_2821_, v_name_2686_, v_levelParams_2680_, v___x_2822_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
v___y_2762_ = v_a_2800_;
v___y_2763_ = v___x_2818_;
v___y_2764_ = v___x_2823_;
goto v___jp_2761_;
}
else
{
lean_object* v_val_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v_val_2824_ = lean_ctor_get(v_a_2820_, 0);
lean_inc_n(v_val_2824_, 2);
lean_dec_ref(v_a_2820_);
v___x_2825_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2826_ = l_Lean_MessageData_ofExpr(v_val_2824_);
v___x_2827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2825_);
lean_ctor_set(v___x_2827_, 1, v___x_2826_);
v___x_2828_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2735_, v___x_2827_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v___x_2830_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_a_2829_);
lean_dec_ref(v___x_2828_);
v___x_2830_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2679_, v_val_2824_, v_name_2686_, v_levelParams_2680_, v_a_2829_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
v___y_2762_ = v_a_2800_;
v___y_2763_ = v___x_2818_;
v___y_2764_ = v___x_2830_;
goto v___jp_2761_;
}
else
{
lean_dec(v_val_2824_);
lean_dec(v_name_2686_);
lean_dec(v_levelParams_2680_);
lean_dec(v_name_2679_);
v___y_2762_ = v_a_2800_;
v___y_2763_ = v___x_2818_;
v___y_2764_ = v___x_2828_;
goto v___jp_2761_;
}
}
}
else
{
lean_object* v___x_2831_; 
lean_dec(v_a_2820_);
lean_dec(v_name_2686_);
lean_dec(v_levelParams_2680_);
lean_dec(v_name_2679_);
v___x_2831_ = lean_box(0);
v___y_2757_ = v_a_2800_;
v___y_2758_ = v___x_2818_;
v_a_2759_ = v___x_2831_;
goto v___jp_2756_;
}
}
else
{
lean_object* v_a_2832_; 
lean_dec(v_name_2686_);
lean_dec(v_levelParams_2680_);
lean_dec(v_name_2679_);
v_a_2832_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2832_);
lean_dec_ref(v___x_2819_);
v___y_2752_ = v_a_2800_;
v___y_2753_ = v___x_2818_;
v_a_2754_ = v_a_2832_;
goto v___jp_2751_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___boxed(lean_object* v_ctorVal_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_ctorVal_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
lean_dec(v_a_2897_);
lean_dec_ref(v_a_2896_);
lean_dec(v_a_2895_);
lean_dec_ref(v_a_2894_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object* v_00_u03b1_2900_, lean_object* v_x_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v___x_2907_; 
v___x_2907_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_x_2901_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2908_, lean_object* v_x_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_00_u03b1_2908_, v_x_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object* v_ctorName_2919_){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = ((lean_object*)(l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1));
v___x_2921_ = l_Lean_Name_append(v_ctorName_2919_, v___x_2920_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object* v_ctorVal_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_){
_start:
{
uint8_t v___x_2928_; lean_object* v___x_2929_; 
v___x_2928_ = 1;
v___x_2929_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_2922_, v___x_2928_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f___boxed(lean_object* v_ctorVal_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_);
lean_dec(v_a_2934_);
lean_dec_ref(v_a_2933_);
lean_dec(v_a_2932_);
lean_dec_ref(v_a_2931_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(lean_object* v_e_2937_, lean_object* v_t_2938_, lean_object* v_acc_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_t_2938_, v_a_2940_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2966_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2945_ = v___x_2942_;
v_isShared_2946_ = v_isSharedCheck_2966_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2942_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2966_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2952_; uint8_t v___x_2953_; 
v___x_2952_ = l_Lean_Expr_cleanupAnnotations(v_a_2943_);
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
lean_del_object(v___x_2945_);
v___x_2961_ = lean_unsigned_to_nat(0u);
v___x_2962_ = l_Lean_mkProj(v___x_2959_, v___x_2961_, v_e_2937_);
lean_inc_ref(v___x_2962_);
v___x_2963_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v___x_2962_, v_arg_2957_, v_acc_2939_, v_a_2940_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref(v___x_2963_);
v_e_2937_ = v___x_2962_;
v_t_2938_ = v_arg_2954_;
v_acc_2939_ = v_a_2964_;
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
v___jp_2947_:
{
lean_object* v___x_2948_; lean_object* v___x_2950_; 
v___x_2948_ = lean_array_push(v_acc_2939_, v_e_2937_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 0, v___x_2948_);
v___x_2950_ = v___x_2945_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_dec_ref(v_acc_2939_);
lean_dec_ref(v_e_2937_);
v_a_2967_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2942_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2942_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg___boxed(lean_object* v_e_2975_, lean_object* v_t_2976_, lean_object* v_acc_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_2975_, v_t_2976_, v_acc_2977_, v_a_2978_);
lean_dec(v_a_2978_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(lean_object* v_e_2981_, lean_object* v_t_2982_, lean_object* v_acc_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_2981_, v_t_2982_, v_acc_2983_, v_a_2985_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___boxed(lean_object* v_e_2990_, lean_object* v_t_2991_, lean_object* v_acc_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(v_e_2990_, v_t_2991_, v_acc_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_);
lean_dec(v_a_2996_);
lean_dec_ref(v_a_2995_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(lean_object* v_e_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v___x_3005_; 
lean_inc(v_a_3003_);
lean_inc_ref(v_a_3002_);
lean_inc(v_a_3001_);
lean_inc_ref(v_a_3000_);
lean_inc_ref(v_e_2999_);
v___x_3005_ = lean_infer_type(v_e_2999_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref(v___x_3005_);
v___x_3007_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_3008_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_2999_, v_a_3006_, v___x_3007_, v_a_3001_);
return v___x_3008_;
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
lean_dec_ref(v_e_2999_);
v_a_3009_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_3005_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_3005_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections___boxed(lean_object* v_e_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(v_e_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
lean_dec(v_a_3019_);
lean_dec_ref(v_a_3018_);
return v_res_3023_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3029_ = lean_box(0);
v___x_3030_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__2));
v___x_3031_ = l_Lean_mkConst(v___x_3030_, v___x_3029_);
return v___x_3031_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3033_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__4));
v___x_3034_ = l_Lean_stringToMessageData(v___x_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object* v_b_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
lean_object* v___x_3041_; 
lean_inc(v_b_3035_);
v___x_3041_ = l_Lean_MVarId_getType(v_b_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3122_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3044_ = v___x_3041_;
v_isShared_3045_ = v_isSharedCheck_3122_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3041_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3122_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
if (lean_obj_tag(v_a_3042_) == 7)
{
lean_object* v_binderType_3046_; lean_object* v_body_3047_; uint8_t v___x_3048_; lean_object* v_mvarId_u2082_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; 
v_binderType_3046_ = lean_ctor_get(v_a_3042_, 1);
lean_inc_ref(v_binderType_3046_);
v_body_3047_ = lean_ctor_get(v_a_3042_, 2);
lean_inc_ref(v_body_3047_);
lean_dec_ref(v_a_3042_);
v___x_3048_ = l_Lean_Expr_hasLooseBVars(v_body_3047_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3067_; 
lean_del_object(v___x_3044_);
v___x_3067_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3046_, v___y_3037_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; lean_object* v___x_3069_; uint8_t v___x_3070_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref(v___x_3067_);
v___x_3069_ = l_Lean_Expr_cleanupAnnotations(v_a_3068_);
v___x_3070_ = l_Lean_Expr_isApp(v___x_3069_);
if (v___x_3070_ == 0)
{
lean_dec_ref(v___x_3069_);
lean_dec_ref(v_body_3047_);
v_mvarId_u2082_3050_ = v_b_3035_;
v___y_3051_ = v___y_3036_;
v___y_3052_ = v___y_3037_;
v___y_3053_ = v___y_3038_;
v___y_3054_ = v___y_3039_;
goto v___jp_3049_;
}
else
{
lean_object* v_arg_3071_; lean_object* v___x_3072_; uint8_t v___x_3073_; 
v_arg_3071_ = lean_ctor_get(v___x_3069_, 1);
lean_inc_ref(v_arg_3071_);
v___x_3072_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3069_);
v___x_3073_ = l_Lean_Expr_isApp(v___x_3072_);
if (v___x_3073_ == 0)
{
lean_dec_ref(v___x_3072_);
lean_dec_ref(v_arg_3071_);
lean_dec_ref(v_body_3047_);
v_mvarId_u2082_3050_ = v_b_3035_;
v___y_3051_ = v___y_3036_;
v___y_3052_ = v___y_3037_;
v___y_3053_ = v___y_3038_;
v___y_3054_ = v___y_3039_;
goto v___jp_3049_;
}
else
{
lean_object* v_arg_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; uint8_t v___x_3077_; 
v_arg_3074_ = lean_ctor_get(v___x_3072_, 1);
lean_inc_ref(v_arg_3074_);
v___x_3075_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3072_);
v___x_3076_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3077_ = l_Lean_Expr_isConstOf(v___x_3075_, v___x_3076_);
lean_dec_ref(v___x_3075_);
if (v___x_3077_ == 0)
{
lean_dec_ref(v_arg_3074_);
lean_dec_ref(v_arg_3071_);
lean_dec_ref(v_body_3047_);
v_mvarId_u2082_3050_ = v_b_3035_;
v___y_3051_ = v___y_3036_;
v___y_3052_ = v___y_3037_;
v___y_3053_ = v___y_3038_;
v___y_3054_ = v___y_3039_;
goto v___jp_3049_;
}
else
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3078_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3);
v___x_3079_ = l_Lean_mkApp3(v___x_3078_, v_arg_3074_, v_arg_3071_, v_body_3047_);
v___x_3080_ = lean_unsigned_to_nat(1u);
lean_inc(v_b_3035_);
v___x_3081_ = l_Lean_MVarId_applyN(v_b_3035_, v___x_3079_, v___x_3080_, v___x_3077_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_a_3082_);
lean_dec_ref(v___x_3081_);
if (lean_obj_tag(v_a_3082_) == 1)
{
lean_object* v_tail_3098_; 
v_tail_3098_ = lean_ctor_get(v_a_3082_, 1);
if (lean_obj_tag(v_tail_3098_) == 0)
{
lean_object* v_head_3099_; 
lean_dec(v_b_3035_);
v_head_3099_ = lean_ctor_get(v_a_3082_, 0);
lean_inc(v_head_3099_);
lean_dec_ref(v_a_3082_);
v_mvarId_u2082_3050_ = v_head_3099_;
v___y_3051_ = v___y_3036_;
v___y_3052_ = v___y_3037_;
v___y_3053_ = v___y_3038_;
v___y_3054_ = v___y_3039_;
goto v___jp_3049_;
}
else
{
lean_dec_ref(v_a_3082_);
v___y_3084_ = v___y_3036_;
v___y_3085_ = v___y_3037_;
v___y_3086_ = v___y_3038_;
v___y_3087_ = v___y_3039_;
goto v___jp_3083_;
}
}
else
{
lean_dec(v_a_3082_);
v___y_3084_ = v___y_3036_;
v___y_3085_ = v___y_3037_;
v___y_3086_ = v___y_3038_;
v___y_3087_ = v___y_3039_;
goto v___jp_3083_;
}
v___jp_3083_:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5);
v___x_3089_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3088_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_dec_ref(v___x_3089_);
v_mvarId_u2082_3050_ = v_b_3035_;
v___y_3051_ = v___y_3084_;
v___y_3052_ = v___y_3085_;
v___y_3053_ = v___y_3086_;
v___y_3054_ = v___y_3087_;
goto v___jp_3049_;
}
else
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
lean_dec(v_b_3035_);
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_3089_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3089_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3095_; 
if (v_isShared_3093_ == 0)
{
v___x_3095_ = v___x_3092_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
lean_dec(v_b_3035_);
v_a_3100_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3081_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3081_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_dec_ref(v_body_3047_);
lean_dec(v_b_3035_);
v_a_3108_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_3067_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3067_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
else
{
lean_object* v___x_3117_; 
lean_dec_ref(v_body_3047_);
lean_dec_ref(v_binderType_3046_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 0, v_b_3035_);
v___x_3117_ = v___x_3044_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_b_3035_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
v___jp_3049_:
{
lean_object* v___x_3055_; 
v___x_3055_ = l_Lean_Meta_introSubstEq(v_mvarId_u2082_3050_, v___x_3048_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; lean_object* v_snd_3057_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_a_3056_);
lean_dec_ref(v___x_3055_);
v_snd_3057_ = lean_ctor_get(v_a_3056_, 1);
lean_inc(v_snd_3057_);
lean_dec(v_a_3056_);
v_b_3035_ = v_snd_3057_;
goto _start;
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
v_a_3059_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_3055_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3055_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
}
else
{
lean_object* v___x_3120_; 
lean_dec(v_a_3042_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 0, v_b_3035_);
v___x_3120_ = v___x_3044_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_b_3035_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec(v_b_3035_);
v_a_3123_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3041_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3041_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object* v_b_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_b_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_x_3138_, lean_object* v_x_3139_, lean_object* v_x_3140_, lean_object* v_x_3141_){
_start:
{
lean_object* v_ks_3142_; lean_object* v_vs_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3167_; 
v_ks_3142_ = lean_ctor_get(v_x_3138_, 0);
v_vs_3143_ = lean_ctor_get(v_x_3138_, 1);
v_isSharedCheck_3167_ = !lean_is_exclusive(v_x_3138_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3145_ = v_x_3138_;
v_isShared_3146_ = v_isSharedCheck_3167_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_vs_3143_);
lean_inc(v_ks_3142_);
lean_dec(v_x_3138_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3167_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3147_; uint8_t v___x_3148_; 
v___x_3147_ = lean_array_get_size(v_ks_3142_);
v___x_3148_ = lean_nat_dec_lt(v_x_3139_, v___x_3147_);
if (v___x_3148_ == 0)
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3152_; 
lean_dec(v_x_3139_);
v___x_3149_ = lean_array_push(v_ks_3142_, v_x_3140_);
v___x_3150_ = lean_array_push(v_vs_3143_, v_x_3141_);
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 1, v___x_3150_);
lean_ctor_set(v___x_3145_, 0, v___x_3149_);
v___x_3152_ = v___x_3145_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3149_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v___x_3150_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
else
{
lean_object* v_k_x27_3154_; uint8_t v___x_3155_; 
v_k_x27_3154_ = lean_array_fget_borrowed(v_ks_3142_, v_x_3139_);
v___x_3155_ = l_Lean_instBEqMVarId_beq(v_x_3140_, v_k_x27_3154_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3157_; 
if (v_isShared_3146_ == 0)
{
v___x_3157_ = v___x_3145_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_ks_3142_);
lean_ctor_set(v_reuseFailAlloc_3161_, 1, v_vs_3143_);
v___x_3157_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = lean_unsigned_to_nat(1u);
v___x_3159_ = lean_nat_add(v_x_3139_, v___x_3158_);
lean_dec(v_x_3139_);
v_x_3138_ = v___x_3157_;
v_x_3139_ = v___x_3159_;
goto _start;
}
}
else
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3165_; 
v___x_3162_ = lean_array_fset(v_ks_3142_, v_x_3139_, v_x_3140_);
v___x_3163_ = lean_array_fset(v_vs_3143_, v_x_3139_, v_x_3141_);
lean_dec(v_x_3139_);
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 1, v___x_3163_);
lean_ctor_set(v___x_3145_, 0, v___x_3162_);
v___x_3165_ = v___x_3145_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3162_);
lean_ctor_set(v_reuseFailAlloc_3166_, 1, v___x_3163_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_3168_, lean_object* v_k_3169_, lean_object* v_v_3170_){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = lean_unsigned_to_nat(0u);
v___x_3172_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_3168_, v___x_3171_, v_k_3169_, v_v_3170_);
return v___x_3172_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_3173_; size_t v___x_3174_; size_t v___x_3175_; 
v___x_3173_ = ((size_t)5ULL);
v___x_3174_ = ((size_t)1ULL);
v___x_3175_ = lean_usize_shift_left(v___x_3174_, v___x_3173_);
return v___x_3175_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_3176_; size_t v___x_3177_; size_t v___x_3178_; 
v___x_3176_ = ((size_t)1ULL);
v___x_3177_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3178_ = lean_usize_sub(v___x_3177_, v___x_3176_);
return v___x_3178_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_3179_; 
v___x_3179_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3180_, size_t v_x_3181_, size_t v_x_3182_, lean_object* v_x_3183_, lean_object* v_x_3184_){
_start:
{
if (lean_obj_tag(v_x_3180_) == 0)
{
lean_object* v_es_3185_; size_t v___x_3186_; size_t v___x_3187_; size_t v___x_3188_; size_t v___x_3189_; lean_object* v_j_3190_; lean_object* v___x_3191_; uint8_t v___x_3192_; 
v_es_3185_ = lean_ctor_get(v_x_3180_, 0);
v___x_3186_ = ((size_t)5ULL);
v___x_3187_ = ((size_t)1ULL);
v___x_3188_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_3189_ = lean_usize_land(v_x_3181_, v___x_3188_);
v_j_3190_ = lean_usize_to_nat(v___x_3189_);
v___x_3191_ = lean_array_get_size(v_es_3185_);
v___x_3192_ = lean_nat_dec_lt(v_j_3190_, v___x_3191_);
if (v___x_3192_ == 0)
{
lean_dec(v_j_3190_);
lean_dec(v_x_3184_);
lean_dec(v_x_3183_);
return v_x_3180_;
}
else
{
lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3229_; 
lean_inc_ref(v_es_3185_);
v_isSharedCheck_3229_ = !lean_is_exclusive(v_x_3180_);
if (v_isSharedCheck_3229_ == 0)
{
lean_object* v_unused_3230_; 
v_unused_3230_ = lean_ctor_get(v_x_3180_, 0);
lean_dec(v_unused_3230_);
v___x_3194_ = v_x_3180_;
v_isShared_3195_ = v_isSharedCheck_3229_;
goto v_resetjp_3193_;
}
else
{
lean_dec(v_x_3180_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3229_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v_v_3196_; lean_object* v___x_3197_; lean_object* v_xs_x27_3198_; lean_object* v___y_3200_; 
v_v_3196_ = lean_array_fget(v_es_3185_, v_j_3190_);
v___x_3197_ = lean_box(0);
v_xs_x27_3198_ = lean_array_fset(v_es_3185_, v_j_3190_, v___x_3197_);
switch(lean_obj_tag(v_v_3196_))
{
case 0:
{
lean_object* v_key_3205_; lean_object* v_val_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3216_; 
v_key_3205_ = lean_ctor_get(v_v_3196_, 0);
v_val_3206_ = lean_ctor_get(v_v_3196_, 1);
v_isSharedCheck_3216_ = !lean_is_exclusive(v_v_3196_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3208_ = v_v_3196_;
v_isShared_3209_ = v_isSharedCheck_3216_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_val_3206_);
lean_inc(v_key_3205_);
lean_dec(v_v_3196_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3216_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
uint8_t v___x_3210_; 
v___x_3210_ = l_Lean_instBEqMVarId_beq(v_x_3183_, v_key_3205_);
if (v___x_3210_ == 0)
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
lean_del_object(v___x_3208_);
v___x_3211_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3205_, v_val_3206_, v_x_3183_, v_x_3184_);
v___x_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
v___y_3200_ = v___x_3212_;
goto v___jp_3199_;
}
else
{
lean_object* v___x_3214_; 
lean_dec(v_val_3206_);
lean_dec(v_key_3205_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 1, v_x_3184_);
lean_ctor_set(v___x_3208_, 0, v_x_3183_);
v___x_3214_ = v___x_3208_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_x_3183_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v_x_3184_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
v___y_3200_ = v___x_3214_;
goto v___jp_3199_;
}
}
}
}
case 1:
{
lean_object* v_node_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3227_; 
v_node_3217_ = lean_ctor_get(v_v_3196_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v_v_3196_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3219_ = v_v_3196_;
v_isShared_3220_ = v_isSharedCheck_3227_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_node_3217_);
lean_dec(v_v_3196_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3227_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
size_t v___x_3221_; size_t v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3225_; 
v___x_3221_ = lean_usize_shift_right(v_x_3181_, v___x_3186_);
v___x_3222_ = lean_usize_add(v_x_3182_, v___x_3187_);
v___x_3223_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_node_3217_, v___x_3221_, v___x_3222_, v_x_3183_, v_x_3184_);
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 0, v___x_3223_);
v___x_3225_ = v___x_3219_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3223_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
v___y_3200_ = v___x_3225_;
goto v___jp_3199_;
}
}
}
default: 
{
lean_object* v___x_3228_; 
v___x_3228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3228_, 0, v_x_3183_);
lean_ctor_set(v___x_3228_, 1, v_x_3184_);
v___y_3200_ = v___x_3228_;
goto v___jp_3199_;
}
}
v___jp_3199_:
{
lean_object* v___x_3201_; lean_object* v___x_3203_; 
v___x_3201_ = lean_array_fset(v_xs_x27_3198_, v_j_3190_, v___y_3200_);
lean_dec(v_j_3190_);
if (v_isShared_3195_ == 0)
{
lean_ctor_set(v___x_3194_, 0, v___x_3201_);
v___x_3203_ = v___x_3194_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3201_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
}
else
{
lean_object* v_ks_3231_; lean_object* v_vs_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3252_; 
v_ks_3231_ = lean_ctor_get(v_x_3180_, 0);
v_vs_3232_ = lean_ctor_get(v_x_3180_, 1);
v_isSharedCheck_3252_ = !lean_is_exclusive(v_x_3180_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3234_ = v_x_3180_;
v_isShared_3235_ = v_isSharedCheck_3252_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_vs_3232_);
lean_inc(v_ks_3231_);
lean_dec(v_x_3180_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3252_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_ks_3231_);
lean_ctor_set(v_reuseFailAlloc_3251_, 1, v_vs_3232_);
v___x_3237_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
lean_object* v_newNode_3238_; uint8_t v___y_3240_; size_t v___x_3246_; uint8_t v___x_3247_; 
v_newNode_3238_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v___x_3237_, v_x_3183_, v_x_3184_);
v___x_3246_ = ((size_t)7ULL);
v___x_3247_ = lean_usize_dec_le(v___x_3246_, v_x_3182_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; lean_object* v___x_3249_; uint8_t v___x_3250_; 
v___x_3248_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3238_);
v___x_3249_ = lean_unsigned_to_nat(4u);
v___x_3250_ = lean_nat_dec_lt(v___x_3248_, v___x_3249_);
lean_dec(v___x_3248_);
v___y_3240_ = v___x_3250_;
goto v___jp_3239_;
}
else
{
v___y_3240_ = v___x_3247_;
goto v___jp_3239_;
}
v___jp_3239_:
{
if (v___y_3240_ == 0)
{
lean_object* v_ks_3241_; lean_object* v_vs_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v_ks_3241_ = lean_ctor_get(v_newNode_3238_, 0);
lean_inc_ref(v_ks_3241_);
v_vs_3242_ = lean_ctor_get(v_newNode_3238_, 1);
lean_inc_ref(v_vs_3242_);
lean_dec_ref(v_newNode_3238_);
v___x_3243_ = lean_unsigned_to_nat(0u);
v___x_3244_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_3245_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_x_3182_, v_ks_3241_, v_vs_3242_, v___x_3243_, v___x_3244_);
lean_dec_ref(v_vs_3242_);
lean_dec_ref(v_ks_3241_);
return v___x_3245_;
}
else
{
return v_newNode_3238_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_3253_, lean_object* v_keys_3254_, lean_object* v_vals_3255_, lean_object* v_i_3256_, lean_object* v_entries_3257_){
_start:
{
lean_object* v___x_3258_; uint8_t v___x_3259_; 
v___x_3258_ = lean_array_get_size(v_keys_3254_);
v___x_3259_ = lean_nat_dec_lt(v_i_3256_, v___x_3258_);
if (v___x_3259_ == 0)
{
lean_dec(v_i_3256_);
return v_entries_3257_;
}
else
{
lean_object* v_k_3260_; lean_object* v_v_3261_; uint64_t v___x_3262_; size_t v_h_3263_; size_t v___x_3264_; lean_object* v___x_3265_; size_t v___x_3266_; size_t v___x_3267_; size_t v___x_3268_; size_t v_h_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v_k_3260_ = lean_array_fget_borrowed(v_keys_3254_, v_i_3256_);
v_v_3261_ = lean_array_fget_borrowed(v_vals_3255_, v_i_3256_);
v___x_3262_ = l_Lean_instHashableMVarId_hash(v_k_3260_);
v_h_3263_ = lean_uint64_to_usize(v___x_3262_);
v___x_3264_ = ((size_t)5ULL);
v___x_3265_ = lean_unsigned_to_nat(1u);
v___x_3266_ = ((size_t)1ULL);
v___x_3267_ = lean_usize_sub(v_depth_3253_, v___x_3266_);
v___x_3268_ = lean_usize_mul(v___x_3264_, v___x_3267_);
v_h_3269_ = lean_usize_shift_right(v_h_3263_, v___x_3268_);
v___x_3270_ = lean_nat_add(v_i_3256_, v___x_3265_);
lean_dec(v_i_3256_);
lean_inc(v_v_3261_);
lean_inc(v_k_3260_);
v___x_3271_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_entries_3257_, v_h_3269_, v_depth_3253_, v_k_3260_, v_v_3261_);
v_i_3256_ = v___x_3270_;
v_entries_3257_ = v___x_3271_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_3273_, lean_object* v_keys_3274_, lean_object* v_vals_3275_, lean_object* v_i_3276_, lean_object* v_entries_3277_){
_start:
{
size_t v_depth_boxed_3278_; lean_object* v_res_3279_; 
v_depth_boxed_3278_ = lean_unbox_usize(v_depth_3273_);
lean_dec(v_depth_3273_);
v_res_3279_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_3278_, v_keys_3274_, v_vals_3275_, v_i_3276_, v_entries_3277_);
lean_dec_ref(v_vals_3275_);
lean_dec_ref(v_keys_3274_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3280_, lean_object* v_x_3281_, lean_object* v_x_3282_, lean_object* v_x_3283_, lean_object* v_x_3284_){
_start:
{
size_t v_x_5080__boxed_3285_; size_t v_x_5081__boxed_3286_; lean_object* v_res_3287_; 
v_x_5080__boxed_3285_ = lean_unbox_usize(v_x_3281_);
lean_dec(v_x_3281_);
v_x_5081__boxed_3286_ = lean_unbox_usize(v_x_3282_);
lean_dec(v_x_3282_);
v_res_3287_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3280_, v_x_5080__boxed_3285_, v_x_5081__boxed_3286_, v_x_3283_, v_x_3284_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object* v_x_3288_, lean_object* v_x_3289_, lean_object* v_x_3290_){
_start:
{
uint64_t v___x_3291_; size_t v___x_3292_; size_t v___x_3293_; lean_object* v___x_3294_; 
v___x_3291_ = l_Lean_instHashableMVarId_hash(v_x_3289_);
v___x_3292_ = lean_uint64_to_usize(v___x_3291_);
v___x_3293_ = ((size_t)1ULL);
v___x_3294_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3288_, v___x_3292_, v___x_3293_, v_x_3289_, v_x_3290_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object* v_mvarId_3295_, lean_object* v_val_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v___x_3299_; lean_object* v_mctx_3300_; lean_object* v_cache_3301_; lean_object* v_zetaDeltaFVarIds_3302_; lean_object* v_postponed_3303_; lean_object* v_diag_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3331_; 
v___x_3299_ = lean_st_ref_take(v___y_3297_);
v_mctx_3300_ = lean_ctor_get(v___x_3299_, 0);
v_cache_3301_ = lean_ctor_get(v___x_3299_, 1);
v_zetaDeltaFVarIds_3302_ = lean_ctor_get(v___x_3299_, 2);
v_postponed_3303_ = lean_ctor_get(v___x_3299_, 3);
v_diag_3304_ = lean_ctor_get(v___x_3299_, 4);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3306_ = v___x_3299_;
v_isShared_3307_ = v_isSharedCheck_3331_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_diag_3304_);
lean_inc(v_postponed_3303_);
lean_inc(v_zetaDeltaFVarIds_3302_);
lean_inc(v_cache_3301_);
lean_inc(v_mctx_3300_);
lean_dec(v___x_3299_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3331_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v_depth_3308_; lean_object* v_levelAssignDepth_3309_; lean_object* v_mvarCounter_3310_; lean_object* v_lDepth_3311_; lean_object* v_decls_3312_; lean_object* v_userNames_3313_; lean_object* v_lAssignment_3314_; lean_object* v_eAssignment_3315_; lean_object* v_dAssignment_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3330_; 
v_depth_3308_ = lean_ctor_get(v_mctx_3300_, 0);
v_levelAssignDepth_3309_ = lean_ctor_get(v_mctx_3300_, 1);
v_mvarCounter_3310_ = lean_ctor_get(v_mctx_3300_, 2);
v_lDepth_3311_ = lean_ctor_get(v_mctx_3300_, 3);
v_decls_3312_ = lean_ctor_get(v_mctx_3300_, 4);
v_userNames_3313_ = lean_ctor_get(v_mctx_3300_, 5);
v_lAssignment_3314_ = lean_ctor_get(v_mctx_3300_, 6);
v_eAssignment_3315_ = lean_ctor_get(v_mctx_3300_, 7);
v_dAssignment_3316_ = lean_ctor_get(v_mctx_3300_, 8);
v_isSharedCheck_3330_ = !lean_is_exclusive(v_mctx_3300_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3318_ = v_mctx_3300_;
v_isShared_3319_ = v_isSharedCheck_3330_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_dAssignment_3316_);
lean_inc(v_eAssignment_3315_);
lean_inc(v_lAssignment_3314_);
lean_inc(v_userNames_3313_);
lean_inc(v_decls_3312_);
lean_inc(v_lDepth_3311_);
lean_inc(v_mvarCounter_3310_);
lean_inc(v_levelAssignDepth_3309_);
lean_inc(v_depth_3308_);
lean_dec(v_mctx_3300_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3330_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3320_; lean_object* v___x_3322_; 
v___x_3320_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_eAssignment_3315_, v_mvarId_3295_, v_val_3296_);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 7, v___x_3320_);
v___x_3322_ = v___x_3318_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_depth_3308_);
lean_ctor_set(v_reuseFailAlloc_3329_, 1, v_levelAssignDepth_3309_);
lean_ctor_set(v_reuseFailAlloc_3329_, 2, v_mvarCounter_3310_);
lean_ctor_set(v_reuseFailAlloc_3329_, 3, v_lDepth_3311_);
lean_ctor_set(v_reuseFailAlloc_3329_, 4, v_decls_3312_);
lean_ctor_set(v_reuseFailAlloc_3329_, 5, v_userNames_3313_);
lean_ctor_set(v_reuseFailAlloc_3329_, 6, v_lAssignment_3314_);
lean_ctor_set(v_reuseFailAlloc_3329_, 7, v___x_3320_);
lean_ctor_set(v_reuseFailAlloc_3329_, 8, v_dAssignment_3316_);
v___x_3322_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
lean_object* v___x_3324_; 
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 0, v___x_3322_);
v___x_3324_ = v___x_3306_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3322_);
lean_ctor_set(v_reuseFailAlloc_3328_, 1, v_cache_3301_);
lean_ctor_set(v_reuseFailAlloc_3328_, 2, v_zetaDeltaFVarIds_3302_);
lean_ctor_set(v_reuseFailAlloc_3328_, 3, v_postponed_3303_);
lean_ctor_set(v_reuseFailAlloc_3328_, 4, v_diag_3304_);
v___x_3324_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3325_ = lean_st_ref_set(v___y_3297_, v___x_3324_);
v___x_3326_ = lean_box(0);
v___x_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3326_);
return v___x_3327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object* v_mvarId_3332_, lean_object* v_val_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3332_, v_val_3333_, v___y_3334_);
lean_dec(v___y_3334_);
return v_res_3336_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3342_ = lean_box(0);
v___x_3343_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_3344_ = l_Lean_mkConst(v___x_3343_, v___x_3342_);
return v___x_3344_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3350_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5));
v___x_3351_ = l_Lean_stringToMessageData(v___x_3350_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(lean_object* v_ctorVal_3352_, lean_object* v_xs_3353_, lean_object* v_type_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = lean_box(0);
v___x_3361_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_3354_, v___x_3360_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; uint8_t v___x_3366_; uint8_t v___x_3367_; lean_object* v___y_3369_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref(v___x_3361_);
v___x_3363_ = l_Lean_Expr_mvarId_x21(v_a_3362_);
v___x_3364_ = lean_box(0);
v___x_3365_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3);
v___x_3366_ = 1;
v___x_3367_ = 0;
v___x_3380_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_3381_ = lean_box(0);
v___x_3382_ = l_Lean_MVarId_apply(v___x_3363_, v___x_3365_, v___x_3380_, v___x_3381_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref(v___x_3382_);
if (lean_obj_tag(v_a_3383_) == 1)
{
lean_object* v_tail_3397_; 
v_tail_3397_ = lean_ctor_get(v_a_3383_, 1);
lean_inc(v_tail_3397_);
if (lean_obj_tag(v_tail_3397_) == 1)
{
lean_object* v_tail_3398_; 
v_tail_3398_ = lean_ctor_get(v_tail_3397_, 1);
if (lean_obj_tag(v_tail_3398_) == 0)
{
lean_object* v_toConstantVal_3399_; lean_object* v_head_3400_; lean_object* v_head_3401_; lean_object* v_name_3402_; lean_object* v_levelParams_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v_toConstantVal_3399_ = lean_ctor_get(v_ctorVal_3352_, 0);
lean_inc_ref(v_toConstantVal_3399_);
lean_dec_ref(v_ctorVal_3352_);
v_head_3400_ = lean_ctor_get(v_a_3383_, 0);
lean_inc(v_head_3400_);
lean_dec_ref(v_a_3383_);
v_head_3401_ = lean_ctor_get(v_tail_3397_, 0);
lean_inc(v_head_3401_);
lean_dec_ref(v_tail_3397_);
v_name_3402_ = lean_ctor_get(v_toConstantVal_3399_, 0);
lean_inc_n(v_name_3402_, 2);
v_levelParams_3403_ = lean_ctor_get(v_toConstantVal_3399_, 1);
lean_inc(v_levelParams_3403_);
lean_dec_ref(v_toConstantVal_3399_);
v___x_3404_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_3402_);
v___x_3405_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_3403_, v___x_3364_);
v___x_3406_ = l_Lean_mkConst(v___x_3404_, v___x_3405_);
v___x_3407_ = l_Lean_mkAppN(v___x_3406_, v_xs_3353_);
v___x_3408_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_head_3400_, v___x_3407_, v___y_3356_);
lean_dec_ref(v___x_3408_);
v___x_3409_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_head_3401_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; lean_object* v___x_3411_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3410_);
lean_dec_ref(v___x_3409_);
v___x_3411_ = l_Lean_MVarId_refl(v_a_3410_, v___x_3366_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_dec(v_name_3402_);
v___y_3369_ = v___x_3411_;
goto v___jp_3368_;
}
else
{
lean_object* v_a_3412_; uint8_t v___y_3414_; uint8_t v___x_3417_; 
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
lean_inc(v_a_3412_);
v___x_3417_ = l_Lean_Exception_isInterrupt(v_a_3412_);
if (v___x_3417_ == 0)
{
uint8_t v___x_3418_; 
v___x_3418_ = l_Lean_Exception_isRuntime(v_a_3412_);
v___y_3414_ = v___x_3418_;
goto v___jp_3413_;
}
else
{
lean_dec(v_a_3412_);
v___y_3414_ = v___x_3417_;
goto v___jp_3413_;
}
v___jp_3413_:
{
if (v___y_3414_ == 0)
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
lean_dec_ref(v___x_3411_);
v___x_3415_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_name_3402_);
v___x_3416_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3415_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
v___y_3369_ = v___x_3416_;
goto v___jp_3368_;
}
else
{
lean_dec(v_name_3402_);
v___y_3369_ = v___x_3411_;
goto v___jp_3368_;
}
}
}
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_dec(v_name_3402_);
lean_dec(v_a_3362_);
v_a_3419_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3409_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3409_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
else
{
lean_dec_ref(v_tail_3397_);
lean_dec_ref(v_a_3383_);
lean_dec(v_a_3362_);
v___y_3385_ = v___y_3355_;
v___y_3386_ = v___y_3356_;
v___y_3387_ = v___y_3357_;
v___y_3388_ = v___y_3358_;
goto v___jp_3384_;
}
}
else
{
lean_dec_ref(v_a_3383_);
lean_dec(v_tail_3397_);
lean_dec(v_a_3362_);
v___y_3385_ = v___y_3355_;
v___y_3386_ = v___y_3356_;
v___y_3387_ = v___y_3357_;
v___y_3388_ = v___y_3358_;
goto v___jp_3384_;
}
}
else
{
lean_dec(v_a_3383_);
lean_dec(v_a_3362_);
v___y_3385_ = v___y_3355_;
v___y_3386_ = v___y_3356_;
v___y_3387_ = v___y_3357_;
v___y_3388_ = v___y_3358_;
goto v___jp_3384_;
}
v___jp_3384_:
{
lean_object* v_toConstantVal_3389_; lean_object* v_name_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v_toConstantVal_3389_ = lean_ctor_get(v_ctorVal_3352_, 0);
lean_inc_ref(v_toConstantVal_3389_);
lean_dec_ref(v_ctorVal_3352_);
v_name_3390_ = lean_ctor_get(v_toConstantVal_3389_, 0);
lean_inc(v_name_3390_);
lean_dec_ref(v_toConstantVal_3389_);
v___x_3391_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6);
v___x_3392_ = l_Lean_MessageData_ofName(v_name_3390_);
v___x_3393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3391_);
lean_ctor_set(v___x_3393_, 1, v___x_3392_);
v___x_3394_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_3395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3393_);
lean_ctor_set(v___x_3395_, 1, v___x_3394_);
v___x_3396_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3395_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
return v___x_3396_;
}
}
else
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_dec(v_a_3362_);
lean_dec_ref(v_ctorVal_3352_);
v_a_3427_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3382_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3382_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
v___jp_3368_:
{
if (lean_obj_tag(v___y_3369_) == 0)
{
uint8_t v___x_3370_; lean_object* v___x_3371_; 
lean_dec_ref(v___y_3369_);
v___x_3370_ = 1;
v___x_3371_ = l_Lean_Meta_mkLambdaFVars(v_xs_3353_, v_a_3362_, v___x_3367_, v___x_3366_, v___x_3367_, v___x_3366_, v___x_3370_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
return v___x_3371_;
}
else
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3379_; 
lean_dec(v_a_3362_);
v_a_3372_ = lean_ctor_get(v___y_3369_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___y_3369_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3374_ = v___y_3369_;
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___y_3369_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3377_; 
if (v_isShared_3375_ == 0)
{
v___x_3377_ = v___x_3374_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_a_3372_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorVal_3352_);
return v___x_3361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed(lean_object* v_ctorVal_3435_, lean_object* v_xs_3436_, lean_object* v_type_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(v_ctorVal_3435_, v_xs_3436_, v_type_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec_ref(v_xs_3436_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object* v_ctorVal_3444_, lean_object* v_targetType_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_){
_start:
{
lean_object* v___f_3451_; uint8_t v___x_3452_; lean_object* v___x_3453_; 
v___f_3451_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3451_, 0, v_ctorVal_3444_);
v___x_3452_ = 0;
v___x_3453_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_3445_, v___f_3451_, v___x_3452_, v___x_3452_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
return v___x_3453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___boxed(lean_object* v_ctorVal_3454_, lean_object* v_targetType_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3454_, v_targetType_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_);
lean_dec(v_a_3459_);
lean_dec_ref(v_a_3458_);
lean_dec(v_a_3457_);
lean_dec_ref(v_a_3456_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(lean_object* v_mvarId_3462_, lean_object* v_val_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
lean_object* v___x_3469_; 
v___x_3469_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3462_, v_val_3463_, v___y_3465_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___boxed(lean_object* v_mvarId_3470_, lean_object* v_val_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v_res_3477_; 
v_res_3477_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(v_mvarId_3470_, v_val_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0(lean_object* v_00_u03b2_3478_, lean_object* v_x_3479_, lean_object* v_x_3480_, lean_object* v_x_3481_){
_start:
{
lean_object* v___x_3482_; 
v___x_3482_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_x_3479_, v_x_3480_, v_x_3481_);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3483_, lean_object* v_x_3484_, size_t v_x_3485_, size_t v_x_3486_, lean_object* v_x_3487_, lean_object* v_x_3488_){
_start:
{
lean_object* v___x_3489_; 
v___x_3489_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3484_, v_x_3485_, v_x_3486_, v_x_3487_, v_x_3488_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3490_, lean_object* v_x_3491_, lean_object* v_x_3492_, lean_object* v_x_3493_, lean_object* v_x_3494_, lean_object* v_x_3495_){
_start:
{
size_t v_x_5544__boxed_3496_; size_t v_x_5545__boxed_3497_; lean_object* v_res_3498_; 
v_x_5544__boxed_3496_ = lean_unbox_usize(v_x_3492_);
lean_dec(v_x_3492_);
v_x_5545__boxed_3497_ = lean_unbox_usize(v_x_3493_);
lean_dec(v_x_3493_);
v_res_3498_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(v_00_u03b2_3490_, v_x_3491_, v_x_5544__boxed_3496_, v_x_5545__boxed_3497_, v_x_3494_, v_x_3495_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3499_, lean_object* v_n_3500_, lean_object* v_k_3501_, lean_object* v_v_3502_){
_start:
{
lean_object* v___x_3503_; 
v___x_3503_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v_n_3500_, v_k_3501_, v_v_3502_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3504_, size_t v_depth_3505_, lean_object* v_keys_3506_, lean_object* v_vals_3507_, lean_object* v_heq_3508_, lean_object* v_i_3509_, lean_object* v_entries_3510_){
_start:
{
lean_object* v___x_3511_; 
v___x_3511_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_3505_, v_keys_3506_, v_vals_3507_, v_i_3509_, v_entries_3510_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3512_, lean_object* v_depth_3513_, lean_object* v_keys_3514_, lean_object* v_vals_3515_, lean_object* v_heq_3516_, lean_object* v_i_3517_, lean_object* v_entries_3518_){
_start:
{
size_t v_depth_boxed_3519_; lean_object* v_res_3520_; 
v_depth_boxed_3519_ = lean_unbox_usize(v_depth_3513_);
lean_dec(v_depth_3513_);
v_res_3520_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_3512_, v_depth_boxed_3519_, v_keys_3514_, v_vals_3515_, v_heq_3516_, v_i_3517_, v_entries_3518_);
lean_dec_ref(v_vals_3515_);
lean_dec_ref(v_keys_3514_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_3521_, lean_object* v_x_3522_, lean_object* v_x_3523_, lean_object* v_x_3524_, lean_object* v_x_3525_){
_start:
{
lean_object* v___x_3526_; 
v___x_3526_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_3522_, v_x_3523_, v_x_3524_, v_x_3525_);
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(lean_object* v_ctorVal_3527_, lean_object* v_val_3528_, lean_object* v_name_3529_, lean_object* v_levelParams_3530_, uint8_t v___x_3531_, uint8_t v_hasTrace_3532_, lean_object* v_____r_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
lean_object* v___x_3539_; 
lean_inc_ref(v_val_3528_);
v___x_3539_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3527_, v_val_3528_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3541_; lean_object* v_a_3542_; lean_object* v___x_3543_; lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3560_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3540_);
lean_dec_ref(v___x_3539_);
v___x_3541_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3528_, v___y_3535_);
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3542_);
lean_dec_ref(v___x_3541_);
v___x_3543_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3540_, v___y_3535_);
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3546_ = v___x_3543_;
v_isShared_3547_ = v_isSharedCheck_3560_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3543_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3560_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3553_; 
lean_inc_n(v_name_3529_, 2);
v___x_3548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3548_, 0, v_name_3529_);
lean_ctor_set(v___x_3548_, 1, v_levelParams_3530_);
lean_ctor_set(v___x_3548_, 2, v_a_3542_);
v___x_3549_ = lean_box(0);
v___x_3550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3550_, 0, v_name_3529_);
lean_ctor_set(v___x_3550_, 1, v___x_3549_);
v___x_3551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3548_);
lean_ctor_set(v___x_3551_, 1, v_a_3544_);
lean_ctor_set(v___x_3551_, 2, v___x_3550_);
if (v_isShared_3547_ == 0)
{
lean_ctor_set_tag(v___x_3546_, 2);
lean_ctor_set(v___x_3546_, 0, v___x_3551_);
v___x_3553_ = v___x_3546_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3551_);
v___x_3553_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
lean_object* v___x_3554_; 
v___x_3554_ = l_Lean_addDecl(v___x_3553_, v___x_3531_, v___y_3536_, v___y_3537_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v___x_3555_; uint8_t v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
lean_dec_ref(v___x_3554_);
v___x_3555_ = l_Lean_Meta_simpExtension;
v___x_3556_ = 0;
v___x_3557_ = lean_unsigned_to_nat(1000u);
v___x_3558_ = l_Lean_Meta_addSimpTheorem(v___x_3555_, v_name_3529_, v_hasTrace_3532_, v___x_3531_, v___x_3556_, v___x_3557_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
return v___x_3558_;
}
else
{
lean_dec(v_name_3529_);
return v___x_3554_;
}
}
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_dec(v_levelParams_3530_);
lean_dec(v_name_3529_);
lean_dec_ref(v_val_3528_);
v_a_3561_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3539_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3539_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed(lean_object* v_ctorVal_3569_, lean_object* v_val_3570_, lean_object* v_name_3571_, lean_object* v_levelParams_3572_, lean_object* v___x_3573_, lean_object* v_hasTrace_3574_, lean_object* v_____r_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
uint8_t v___x_9094__boxed_3581_; uint8_t v_hasTrace_boxed_3582_; lean_object* v_res_3583_; 
v___x_9094__boxed_3581_ = lean_unbox(v___x_3573_);
v_hasTrace_boxed_3582_ = lean_unbox(v_hasTrace_3574_);
v_res_3583_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3569_, v_val_3570_, v_name_3571_, v_levelParams_3572_, v___x_9094__boxed_3581_, v_hasTrace_boxed_3582_, v_____r_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(lean_object* v_ctorVal_3584_, lean_object* v_val_3585_, lean_object* v_name_3586_, lean_object* v_levelParams_3587_, uint8_t v___x_3588_, lean_object* v_____r_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v___x_3595_; 
lean_inc_ref(v_val_3585_);
v___x_3595_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3584_, v_val_3585_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_a_3596_; lean_object* v___x_3597_; lean_object* v_a_3598_; lean_object* v___x_3599_; lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3617_; 
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_a_3596_);
lean_dec_ref(v___x_3595_);
v___x_3597_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3585_, v___y_3591_);
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3598_);
lean_dec_ref(v___x_3597_);
v___x_3599_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3596_, v___y_3591_);
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3602_ = v___x_3599_;
v_isShared_3603_ = v_isSharedCheck_3617_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3599_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3617_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3609_; 
lean_inc_n(v_name_3586_, 2);
v___x_3604_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3604_, 0, v_name_3586_);
lean_ctor_set(v___x_3604_, 1, v_levelParams_3587_);
lean_ctor_set(v___x_3604_, 2, v_a_3598_);
v___x_3605_ = lean_box(0);
v___x_3606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3606_, 0, v_name_3586_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
v___x_3607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3604_);
lean_ctor_set(v___x_3607_, 1, v_a_3600_);
lean_ctor_set(v___x_3607_, 2, v___x_3606_);
if (v_isShared_3603_ == 0)
{
lean_ctor_set_tag(v___x_3602_, 2);
lean_ctor_set(v___x_3602_, 0, v___x_3607_);
v___x_3609_ = v___x_3602_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3607_);
v___x_3609_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
uint8_t v___x_3610_; lean_object* v___x_3611_; 
v___x_3610_ = 0;
v___x_3611_ = l_Lean_addDecl(v___x_3609_, v___x_3610_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v___x_3612_; uint8_t v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
lean_dec_ref(v___x_3611_);
v___x_3612_ = l_Lean_Meta_simpExtension;
v___x_3613_ = 0;
v___x_3614_ = lean_unsigned_to_nat(1000u);
v___x_3615_ = l_Lean_Meta_addSimpTheorem(v___x_3612_, v_name_3586_, v___x_3588_, v___x_3610_, v___x_3613_, v___x_3614_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
return v___x_3615_;
}
else
{
lean_dec(v_name_3586_);
return v___x_3611_;
}
}
}
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_dec(v_levelParams_3587_);
lean_dec(v_name_3586_);
lean_dec_ref(v_val_3585_);
v_a_3618_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3595_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3595_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0___boxed(lean_object* v_ctorVal_3626_, lean_object* v_val_3627_, lean_object* v_name_3628_, lean_object* v_levelParams_3629_, lean_object* v___x_3630_, lean_object* v_____r_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
uint8_t v___x_9182__boxed_3637_; lean_object* v_res_3638_; 
v___x_9182__boxed_3637_ = lean_unbox(v___x_3630_);
v_res_3638_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3626_, v_val_3627_, v_name_3628_, v_levelParams_3629_, v___x_9182__boxed_3637_, v_____r_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object* v_ctorVal_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_){
_start:
{
lean_object* v_toConstantVal_3645_; lean_object* v_options_3646_; lean_object* v_name_3647_; lean_object* v_levelParams_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3868_; 
v_toConstantVal_3645_ = lean_ctor_get(v_ctorVal_3639_, 0);
lean_inc_ref(v_toConstantVal_3645_);
v_options_3646_ = lean_ctor_get(v_a_3642_, 2);
v_name_3647_ = lean_ctor_get(v_toConstantVal_3645_, 0);
v_levelParams_3648_ = lean_ctor_get(v_toConstantVal_3645_, 1);
v_isSharedCheck_3868_ = !lean_is_exclusive(v_toConstantVal_3645_);
if (v_isSharedCheck_3868_ == 0)
{
lean_object* v_unused_3869_; 
v_unused_3869_ = lean_ctor_get(v_toConstantVal_3645_, 2);
lean_dec(v_unused_3869_);
v___x_3650_ = v_toConstantVal_3645_;
v_isShared_3651_ = v_isSharedCheck_3868_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_levelParams_3648_);
lean_inc(v_name_3647_);
lean_dec(v_toConstantVal_3645_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3868_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v_inheritedTraceOptions_3652_; uint8_t v_hasTrace_3653_; lean_object* v_name_3654_; 
v_inheritedTraceOptions_3652_ = lean_ctor_get(v_a_3642_, 13);
v_hasTrace_3653_ = lean_ctor_get_uint8(v_options_3646_, sizeof(void*)*1);
v_name_3654_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_3647_);
if (v_hasTrace_3653_ == 0)
{
lean_object* v___x_3655_; 
lean_inc_ref(v_ctorVal_3639_);
v___x_3655_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3698_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3658_ = v___x_3655_;
v_isShared_3659_ = v_isSharedCheck_3698_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3655_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3698_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
if (lean_obj_tag(v_a_3656_) == 1)
{
lean_object* v_val_3660_; lean_object* v___x_3661_; 
lean_del_object(v___x_3658_);
v_val_3660_ = lean_ctor_get(v_a_3656_, 0);
lean_inc_n(v_val_3660_, 2);
lean_dec_ref(v_a_3656_);
v___x_3661_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3639_, v_val_3660_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3663_; lean_object* v_a_3664_; lean_object* v___x_3665_; lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3685_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref(v___x_3661_);
v___x_3663_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3660_, v_a_3641_);
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_a_3664_);
lean_dec_ref(v___x_3663_);
v___x_3665_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3662_, v_a_3641_);
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3668_ = v___x_3665_;
v_isShared_3669_ = v_isSharedCheck_3685_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3665_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3685_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
lean_inc(v_name_3654_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 2, v_a_3664_);
lean_ctor_set(v___x_3650_, 0, v_name_3654_);
v___x_3671_ = v___x_3650_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_name_3654_);
lean_ctor_set(v_reuseFailAlloc_3684_, 1, v_levelParams_3648_);
lean_ctor_set(v_reuseFailAlloc_3684_, 2, v_a_3664_);
v___x_3671_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3676_; 
v___x_3672_ = lean_box(0);
lean_inc(v_name_3654_);
v___x_3673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3673_, 0, v_name_3654_);
lean_ctor_set(v___x_3673_, 1, v___x_3672_);
v___x_3674_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3671_);
lean_ctor_set(v___x_3674_, 1, v_a_3666_);
lean_ctor_set(v___x_3674_, 2, v___x_3673_);
if (v_isShared_3669_ == 0)
{
lean_ctor_set_tag(v___x_3668_, 2);
lean_ctor_set(v___x_3668_, 0, v___x_3674_);
v___x_3676_ = v___x_3668_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3674_);
v___x_3676_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3677_; 
v___x_3677_ = l_Lean_addDecl(v___x_3676_, v_hasTrace_3653_, v_a_3642_, v_a_3643_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v___x_3678_; uint8_t v___x_3679_; uint8_t v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
lean_dec_ref(v___x_3677_);
v___x_3678_ = l_Lean_Meta_simpExtension;
v___x_3679_ = 1;
v___x_3680_ = 0;
v___x_3681_ = lean_unsigned_to_nat(1000u);
v___x_3682_ = l_Lean_Meta_addSimpTheorem(v___x_3678_, v_name_3654_, v___x_3679_, v_hasTrace_3653_, v___x_3680_, v___x_3681_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
return v___x_3682_;
}
else
{
lean_dec(v_name_3654_);
return v___x_3677_;
}
}
}
}
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
lean_dec(v_val_3660_);
lean_dec(v_name_3654_);
lean_del_object(v___x_3650_);
lean_dec(v_levelParams_3648_);
v_a_3686_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3661_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3661_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
else
{
lean_object* v___x_3694_; lean_object* v___x_3696_; 
lean_dec(v_a_3656_);
lean_dec(v_name_3654_);
lean_del_object(v___x_3650_);
lean_dec(v_levelParams_3648_);
lean_dec_ref(v_ctorVal_3639_);
v___x_3694_ = lean_box(0);
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 0, v___x_3694_);
v___x_3696_ = v___x_3658_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3694_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
lean_dec(v_name_3654_);
lean_del_object(v___x_3650_);
lean_dec(v_levelParams_3648_);
lean_dec_ref(v_ctorVal_3639_);
v_a_3699_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3655_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3655_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
else
{
lean_object* v___f_3707_; lean_object* v_cls_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; uint8_t v___x_3711_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v_a_3715_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v_a_3727_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v_a_3732_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v_a_3743_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v_a_3758_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v_a_3763_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; 
lean_inc(v_name_3654_);
v___f_3707_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3707_, 0, v_name_3654_);
v_cls_3708_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_3709_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_3710_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_3711_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3652_, v_options_3646_, v___x_3710_);
if (v___x_3711_ == 0)
{
lean_object* v___x_3806_; uint8_t v___x_3807_; 
v___x_3806_ = l_Lean_trace_profiler;
v___x_3807_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3646_, v___x_3806_);
if (v___x_3807_ == 0)
{
lean_object* v___x_3808_; 
lean_dec_ref(v___f_3707_);
lean_inc_ref(v_ctorVal_3639_);
v___x_3808_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
if (lean_obj_tag(v___x_3808_) == 0)
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3859_; 
v_a_3809_ = lean_ctor_get(v___x_3808_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3808_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3811_ = v___x_3808_;
v_isShared_3812_ = v_isSharedCheck_3859_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3808_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3859_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
if (lean_obj_tag(v_a_3809_) == 1)
{
lean_object* v_val_3813_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; 
lean_del_object(v___x_3811_);
v_val_3813_ = lean_ctor_get(v_a_3809_, 0);
lean_inc(v_val_3813_);
lean_dec_ref(v_a_3809_);
if (v___x_3711_ == 0)
{
v___y_3815_ = v_a_3640_;
v___y_3816_ = v_a_3641_;
v___y_3817_ = v_a_3642_;
v___y_3818_ = v_a_3643_;
goto v___jp_3814_;
}
else
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3851_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_3813_);
v___x_3852_ = l_Lean_MessageData_ofExpr(v_val_3813_);
v___x_3853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3851_);
lean_ctor_set(v___x_3853_, 1, v___x_3852_);
v___x_3854_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3708_, v___x_3853_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_dec_ref(v___x_3854_);
v___y_3815_ = v_a_3640_;
v___y_3816_ = v_a_3641_;
v___y_3817_ = v_a_3642_;
v___y_3818_ = v_a_3643_;
goto v___jp_3814_;
}
else
{
lean_dec(v_val_3813_);
lean_dec(v_name_3654_);
lean_del_object(v___x_3650_);
lean_dec(v_levelParams_3648_);
lean_dec_ref(v_ctorVal_3639_);
return v___x_3854_;
}
}
v___jp_3814_:
{
lean_object* v___x_3819_; 
lean_inc(v_val_3813_);
v___x_3819_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3639_, v_val_3813_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_a_3820_; lean_object* v___x_3821_; lean_object* v_a_3822_; lean_object* v___x_3823_; lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3842_; 
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3820_);
lean_dec_ref(v___x_3819_);
v___x_3821_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3813_, v___y_3816_);
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_a_3822_);
lean_dec_ref(v___x_3821_);
v___x_3823_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3820_, v___y_3816_);
v_a_3824_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3826_ = v___x_3823_;
v_isShared_3827_ = v_isSharedCheck_3842_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3823_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3842_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
lean_inc(v_name_3654_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 2, v_a_3822_);
lean_ctor_set(v___x_3650_, 0, v_name_3654_);
v___x_3829_ = v___x_3650_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_name_3654_);
lean_ctor_set(v_reuseFailAlloc_3841_, 1, v_levelParams_3648_);
lean_ctor_set(v_reuseFailAlloc_3841_, 2, v_a_3822_);
v___x_3829_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3834_; 
v___x_3830_ = lean_box(0);
lean_inc(v_name_3654_);
v___x_3831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3831_, 0, v_name_3654_);
lean_ctor_set(v___x_3831_, 1, v___x_3830_);
v___x_3832_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3829_);
lean_ctor_set(v___x_3832_, 1, v_a_3824_);
lean_ctor_set(v___x_3832_, 2, v___x_3831_);
if (v_isShared_3827_ == 0)
{
lean_ctor_set_tag(v___x_3826_, 2);
lean_ctor_set(v___x_3826_, 0, v___x_3832_);
v___x_3834_ = v___x_3826_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3832_);
v___x_3834_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
lean_object* v___x_3835_; 
v___x_3835_ = l_Lean_addDecl(v___x_3834_, v___x_3807_, v___y_3817_, v___y_3818_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v___x_3836_; uint8_t v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
lean_dec_ref(v___x_3835_);
v___x_3836_ = l_Lean_Meta_simpExtension;
v___x_3837_ = 0;
v___x_3838_ = lean_unsigned_to_nat(1000u);
v___x_3839_ = l_Lean_Meta_addSimpTheorem(v___x_3836_, v_name_3654_, v_hasTrace_3653_, v___x_3807_, v___x_3837_, v___x_3838_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
return v___x_3839_;
}
else
{
lean_dec(v_name_3654_);
return v___x_3835_;
}
}
}
}
}
else
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3850_; 
lean_dec(v_val_3813_);
lean_dec(v_name_3654_);
lean_del_object(v___x_3650_);
lean_dec(v_levelParams_3648_);
v_a_3843_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3845_ = v___x_3819_;
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3819_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
}
}
else
{
lean_object* v___x_3855_; lean_object* v___x_3857_; 
lean_dec(v_a_3809_);
lean_dec(v_name_3654_);
lean_del_object(v___x_3650_);
lean_dec(v_levelParams_3648_);
lean_dec_ref(v_ctorVal_3639_);
v___x_3855_ = lean_box(0);
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 0, v___x_3855_);
v___x_3857_ = v___x_3811_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v___x_3855_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec(v_name_3654_);
lean_del_object(v___x_3650_);
lean_dec(v_levelParams_3648_);
lean_dec_ref(v_ctorVal_3639_);
v_a_3860_ = lean_ctor_get(v___x_3808_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3808_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3808_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3808_);
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
else
{
lean_del_object(v___x_3650_);
goto v___jp_3771_;
}
}
else
{
lean_del_object(v___x_3650_);
goto v___jp_3771_;
}
v___jp_3712_:
{
lean_object* v___x_3716_; double v___x_3717_; double v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3716_ = lean_io_get_num_heartbeats();
v___x_3717_ = lean_float_of_nat(v___y_3714_);
v___x_3718_ = lean_float_of_nat(v___x_3716_);
v___x_3719_ = lean_box_float(v___x_3717_);
v___x_3720_ = lean_box_float(v___x_3718_);
v___x_3721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3719_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
v___x_3722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3722_, 0, v_a_3715_);
lean_ctor_set(v___x_3722_, 1, v___x_3721_);
v___x_3723_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3708_, v_hasTrace_3653_, v___x_3709_, v_options_3646_, v___x_3711_, v___y_3713_, v___f_3707_, v___x_3722_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
return v___x_3723_;
}
v___jp_3724_:
{
lean_object* v___x_3728_; 
v___x_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3728_, 0, v_a_3727_);
v___y_3713_ = v___y_3725_;
v___y_3714_ = v___y_3726_;
v_a_3715_ = v___x_3728_;
goto v___jp_3712_;
}
v___jp_3729_:
{
lean_object* v___x_3733_; 
v___x_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3733_, 0, v_a_3732_);
v___y_3713_ = v___y_3730_;
v___y_3714_ = v___y_3731_;
v_a_3715_ = v___x_3733_;
goto v___jp_3712_;
}
v___jp_3734_:
{
if (lean_obj_tag(v___y_3737_) == 0)
{
lean_object* v_a_3738_; 
v_a_3738_ = lean_ctor_get(v___y_3737_, 0);
lean_inc(v_a_3738_);
lean_dec_ref(v___y_3737_);
v___y_3730_ = v___y_3735_;
v___y_3731_ = v___y_3736_;
v_a_3732_ = v_a_3738_;
goto v___jp_3729_;
}
else
{
lean_object* v_a_3739_; 
v_a_3739_ = lean_ctor_get(v___y_3737_, 0);
lean_inc(v_a_3739_);
lean_dec_ref(v___y_3737_);
v___y_3725_ = v___y_3735_;
v___y_3726_ = v___y_3736_;
v_a_3727_ = v_a_3739_;
goto v___jp_3724_;
}
}
v___jp_3740_:
{
lean_object* v___x_3744_; double v___x_3745_; double v___x_3746_; double v___x_3747_; double v___x_3748_; double v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3744_ = lean_io_mono_nanos_now();
v___x_3745_ = lean_float_of_nat(v___y_3741_);
v___x_3746_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_3747_ = lean_float_div(v___x_3745_, v___x_3746_);
v___x_3748_ = lean_float_of_nat(v___x_3744_);
v___x_3749_ = lean_float_div(v___x_3748_, v___x_3746_);
v___x_3750_ = lean_box_float(v___x_3747_);
v___x_3751_ = lean_box_float(v___x_3749_);
v___x_3752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3750_);
lean_ctor_set(v___x_3752_, 1, v___x_3751_);
v___x_3753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3753_, 0, v_a_3743_);
lean_ctor_set(v___x_3753_, 1, v___x_3752_);
v___x_3754_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3708_, v_hasTrace_3653_, v___x_3709_, v_options_3646_, v___x_3711_, v___y_3742_, v___f_3707_, v___x_3753_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
return v___x_3754_;
}
v___jp_3755_:
{
lean_object* v___x_3759_; 
v___x_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3759_, 0, v_a_3758_);
v___y_3741_ = v___y_3756_;
v___y_3742_ = v___y_3757_;
v_a_3743_ = v___x_3759_;
goto v___jp_3740_;
}
v___jp_3760_:
{
lean_object* v___x_3764_; 
v___x_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3764_, 0, v_a_3763_);
v___y_3741_ = v___y_3761_;
v___y_3742_ = v___y_3762_;
v_a_3743_ = v___x_3764_;
goto v___jp_3740_;
}
v___jp_3765_:
{
if (lean_obj_tag(v___y_3768_) == 0)
{
lean_object* v_a_3769_; 
v_a_3769_ = lean_ctor_get(v___y_3768_, 0);
lean_inc(v_a_3769_);
lean_dec_ref(v___y_3768_);
v___y_3756_ = v___y_3766_;
v___y_3757_ = v___y_3767_;
v_a_3758_ = v_a_3769_;
goto v___jp_3755_;
}
else
{
lean_object* v_a_3770_; 
v_a_3770_ = lean_ctor_get(v___y_3768_, 0);
lean_inc(v_a_3770_);
lean_dec_ref(v___y_3768_);
v___y_3761_ = v___y_3766_;
v___y_3762_ = v___y_3767_;
v_a_3763_ = v_a_3770_;
goto v___jp_3760_;
}
}
v___jp_3771_:
{
lean_object* v___x_3772_; lean_object* v_a_3773_; lean_object* v___x_3774_; uint8_t v___x_3775_; 
v___x_3772_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_3643_);
v_a_3773_ = lean_ctor_get(v___x_3772_, 0);
lean_inc(v_a_3773_);
lean_dec_ref(v___x_3772_);
v___x_3774_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3775_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3646_, v___x_3774_);
if (v___x_3775_ == 0)
{
lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3776_ = lean_io_mono_nanos_now();
lean_inc_ref(v_ctorVal_3639_);
v___x_3777_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v_a_3778_; 
v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_a_3778_);
lean_dec_ref(v___x_3777_);
if (lean_obj_tag(v_a_3778_) == 1)
{
if (v___x_3711_ == 0)
{
lean_object* v_val_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v_val_3779_ = lean_ctor_get(v_a_3778_, 0);
lean_inc(v_val_3779_);
lean_dec_ref(v_a_3778_);
v___x_3780_ = lean_box(0);
v___x_3781_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3639_, v_val_3779_, v_name_3654_, v_levelParams_3648_, v___x_3775_, v_hasTrace_3653_, v___x_3780_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
v___y_3766_ = v___x_3776_;
v___y_3767_ = v_a_3773_;
v___y_3768_ = v___x_3781_;
goto v___jp_3765_;
}
else
{
lean_object* v_val_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v_val_3782_ = lean_ctor_get(v_a_3778_, 0);
lean_inc_n(v_val_3782_, 2);
lean_dec_ref(v_a_3778_);
v___x_3783_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3784_ = l_Lean_MessageData_ofExpr(v_val_3782_);
v___x_3785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3783_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
v___x_3786_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3708_, v___x_3785_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v___x_3788_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_a_3787_);
lean_dec_ref(v___x_3786_);
v___x_3788_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3639_, v_val_3782_, v_name_3654_, v_levelParams_3648_, v___x_3775_, v_hasTrace_3653_, v_a_3787_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
v___y_3766_ = v___x_3776_;
v___y_3767_ = v_a_3773_;
v___y_3768_ = v___x_3788_;
goto v___jp_3765_;
}
else
{
lean_dec(v_val_3782_);
lean_dec(v_name_3654_);
lean_dec(v_levelParams_3648_);
lean_dec_ref(v_ctorVal_3639_);
v___y_3766_ = v___x_3776_;
v___y_3767_ = v_a_3773_;
v___y_3768_ = v___x_3786_;
goto v___jp_3765_;
}
}
}
else
{
lean_object* v___x_3789_; 
lean_dec(v_a_3778_);
lean_dec(v_name_3654_);
lean_dec(v_levelParams_3648_);
lean_dec_ref(v_ctorVal_3639_);
v___x_3789_ = lean_box(0);
v___y_3756_ = v___x_3776_;
v___y_3757_ = v_a_3773_;
v_a_3758_ = v___x_3789_;
goto v___jp_3755_;
}
}
else
{
lean_object* v_a_3790_; 
lean_dec(v_name_3654_);
lean_dec(v_levelParams_3648_);
lean_dec_ref(v_ctorVal_3639_);
v_a_3790_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_a_3790_);
lean_dec_ref(v___x_3777_);
v___y_3761_ = v___x_3776_;
v___y_3762_ = v_a_3773_;
v_a_3763_ = v_a_3790_;
goto v___jp_3760_;
}
}
else
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_ctorVal_3639_);
v___x_3792_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref(v___x_3792_);
if (lean_obj_tag(v_a_3793_) == 1)
{
if (v___x_3711_ == 0)
{
lean_object* v_val_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v_val_3794_ = lean_ctor_get(v_a_3793_, 0);
lean_inc(v_val_3794_);
lean_dec_ref(v_a_3793_);
v___x_3795_ = lean_box(0);
v___x_3796_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3639_, v_val_3794_, v_name_3654_, v_levelParams_3648_, v___x_3775_, v___x_3795_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
v___y_3735_ = v_a_3773_;
v___y_3736_ = v___x_3791_;
v___y_3737_ = v___x_3796_;
goto v___jp_3734_;
}
else
{
lean_object* v_val_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v_val_3797_ = lean_ctor_get(v_a_3793_, 0);
lean_inc_n(v_val_3797_, 2);
lean_dec_ref(v_a_3793_);
v___x_3798_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3799_ = l_Lean_MessageData_ofExpr(v_val_3797_);
v___x_3800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3798_);
lean_ctor_set(v___x_3800_, 1, v___x_3799_);
v___x_3801_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3708_, v___x_3800_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; lean_object* v___x_3803_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_a_3802_);
lean_dec_ref(v___x_3801_);
v___x_3803_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3639_, v_val_3797_, v_name_3654_, v_levelParams_3648_, v___x_3775_, v_a_3802_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
v___y_3735_ = v_a_3773_;
v___y_3736_ = v___x_3791_;
v___y_3737_ = v___x_3803_;
goto v___jp_3734_;
}
else
{
lean_dec(v_val_3797_);
lean_dec(v_name_3654_);
lean_dec(v_levelParams_3648_);
lean_dec_ref(v_ctorVal_3639_);
v___y_3735_ = v_a_3773_;
v___y_3736_ = v___x_3791_;
v___y_3737_ = v___x_3801_;
goto v___jp_3734_;
}
}
}
else
{
lean_object* v___x_3804_; 
lean_dec(v_a_3793_);
lean_dec(v_name_3654_);
lean_dec(v_levelParams_3648_);
lean_dec_ref(v_ctorVal_3639_);
v___x_3804_ = lean_box(0);
v___y_3730_ = v_a_3773_;
v___y_3731_ = v___x_3791_;
v_a_3732_ = v___x_3804_;
goto v___jp_3729_;
}
}
else
{
lean_object* v_a_3805_; 
lean_dec(v_name_3654_);
lean_dec(v_levelParams_3648_);
lean_dec_ref(v_ctorVal_3639_);
v_a_3805_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3805_);
lean_dec_ref(v___x_3792_);
v___y_3725_ = v_a_3773_;
v___y_3726_ = v___x_3791_;
v_a_3727_ = v_a_3805_;
goto v___jp_3724_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___boxed(lean_object* v_ctorVal_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_ctorVal_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_);
lean_dec(v_a_3874_);
lean_dec_ref(v_a_3873_);
lean_dec(v_a_3872_);
lean_dec_ref(v_a_3871_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object* v_name_3877_, lean_object* v_decl_3878_, lean_object* v_ref_3879_){
_start:
{
lean_object* v_defValue_3881_; lean_object* v_descr_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3909_; 
v_defValue_3881_ = lean_ctor_get(v_decl_3878_, 0);
v_descr_3882_ = lean_ctor_get(v_decl_3878_, 1);
v_isSharedCheck_3909_ = !lean_is_exclusive(v_decl_3878_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3884_ = v_decl_3878_;
v_isShared_3885_ = v_isSharedCheck_3909_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_descr_3882_);
lean_inc(v_defValue_3881_);
lean_dec(v_decl_3878_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3909_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3886_; uint8_t v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3886_ = lean_alloc_ctor(1, 0, 1);
v___x_3887_ = lean_unbox(v_defValue_3881_);
lean_ctor_set_uint8(v___x_3886_, 0, v___x_3887_);
lean_inc_n(v_name_3877_, 2);
v___x_3888_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3888_, 0, v_name_3877_);
lean_ctor_set(v___x_3888_, 1, v_ref_3879_);
lean_ctor_set(v___x_3888_, 2, v___x_3886_);
lean_ctor_set(v___x_3888_, 3, v_descr_3882_);
v___x_3889_ = lean_register_option(v_name_3877_, v___x_3888_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3899_; 
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3899_ == 0)
{
lean_object* v_unused_3900_; 
v_unused_3900_ = lean_ctor_get(v___x_3889_, 0);
lean_dec(v_unused_3900_);
v___x_3891_ = v___x_3889_;
v_isShared_3892_ = v_isSharedCheck_3899_;
goto v_resetjp_3890_;
}
else
{
lean_dec(v___x_3889_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3899_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 1, v_defValue_3881_);
lean_ctor_set(v___x_3884_, 0, v_name_3877_);
v___x_3894_ = v___x_3884_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_name_3877_);
lean_ctor_set(v_reuseFailAlloc_3898_, 1, v_defValue_3881_);
v___x_3894_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
lean_object* v___x_3896_; 
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 0, v___x_3894_);
v___x_3896_ = v___x_3891_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3894_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
}
else
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
lean_del_object(v___x_3884_);
lean_dec(v_defValue_3881_);
lean_dec(v_name_3877_);
v_a_3901_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3889_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3889_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_3910_, lean_object* v_decl_3911_, lean_object* v_ref_3912_, lean_object* v_a_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v_name_3910_, v_decl_3911_, v_ref_3912_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3928_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_3929_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_3930_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_3931_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v___x_3928_, v___x_3929_, v___x_3930_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object* v_a_3932_){
_start:
{
lean_object* v_res_3933_; 
v_res_3933_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(lean_object* v___y_3934_, uint8_t v_isExporting_3935_, lean_object* v___x_3936_, lean_object* v___y_3937_, lean_object* v___x_3938_, lean_object* v_a_x3f_3939_){
_start:
{
lean_object* v___x_3941_; lean_object* v_env_3942_; lean_object* v_nextMacroScope_3943_; lean_object* v_ngen_3944_; lean_object* v_auxDeclNGen_3945_; lean_object* v_traceState_3946_; lean_object* v_messages_3947_; lean_object* v_infoState_3948_; lean_object* v_snapshotTasks_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3974_; 
v___x_3941_ = lean_st_ref_take(v___y_3934_);
v_env_3942_ = lean_ctor_get(v___x_3941_, 0);
v_nextMacroScope_3943_ = lean_ctor_get(v___x_3941_, 1);
v_ngen_3944_ = lean_ctor_get(v___x_3941_, 2);
v_auxDeclNGen_3945_ = lean_ctor_get(v___x_3941_, 3);
v_traceState_3946_ = lean_ctor_get(v___x_3941_, 4);
v_messages_3947_ = lean_ctor_get(v___x_3941_, 6);
v_infoState_3948_ = lean_ctor_get(v___x_3941_, 7);
v_snapshotTasks_3949_ = lean_ctor_get(v___x_3941_, 8);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3974_ == 0)
{
lean_object* v_unused_3975_; 
v_unused_3975_ = lean_ctor_get(v___x_3941_, 5);
lean_dec(v_unused_3975_);
v___x_3951_ = v___x_3941_;
v_isShared_3952_ = v_isSharedCheck_3974_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_snapshotTasks_3949_);
lean_inc(v_infoState_3948_);
lean_inc(v_messages_3947_);
lean_inc(v_traceState_3946_);
lean_inc(v_auxDeclNGen_3945_);
lean_inc(v_ngen_3944_);
lean_inc(v_nextMacroScope_3943_);
lean_inc(v_env_3942_);
lean_dec(v___x_3941_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3974_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3953_; lean_object* v___x_3955_; 
v___x_3953_ = l_Lean_Environment_setExporting(v_env_3942_, v_isExporting_3935_);
if (v_isShared_3952_ == 0)
{
lean_ctor_set(v___x_3951_, 5, v___x_3936_);
lean_ctor_set(v___x_3951_, 0, v___x_3953_);
v___x_3955_ = v___x_3951_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v___x_3953_);
lean_ctor_set(v_reuseFailAlloc_3973_, 1, v_nextMacroScope_3943_);
lean_ctor_set(v_reuseFailAlloc_3973_, 2, v_ngen_3944_);
lean_ctor_set(v_reuseFailAlloc_3973_, 3, v_auxDeclNGen_3945_);
lean_ctor_set(v_reuseFailAlloc_3973_, 4, v_traceState_3946_);
lean_ctor_set(v_reuseFailAlloc_3973_, 5, v___x_3936_);
lean_ctor_set(v_reuseFailAlloc_3973_, 6, v_messages_3947_);
lean_ctor_set(v_reuseFailAlloc_3973_, 7, v_infoState_3948_);
lean_ctor_set(v_reuseFailAlloc_3973_, 8, v_snapshotTasks_3949_);
v___x_3955_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v_mctx_3958_; lean_object* v_zetaDeltaFVarIds_3959_; lean_object* v_postponed_3960_; lean_object* v_diag_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3971_; 
v___x_3956_ = lean_st_ref_set(v___y_3934_, v___x_3955_);
v___x_3957_ = lean_st_ref_take(v___y_3937_);
v_mctx_3958_ = lean_ctor_get(v___x_3957_, 0);
v_zetaDeltaFVarIds_3959_ = lean_ctor_get(v___x_3957_, 2);
v_postponed_3960_ = lean_ctor_get(v___x_3957_, 3);
v_diag_3961_ = lean_ctor_get(v___x_3957_, 4);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3971_ == 0)
{
lean_object* v_unused_3972_; 
v_unused_3972_ = lean_ctor_get(v___x_3957_, 1);
lean_dec(v_unused_3972_);
v___x_3963_ = v___x_3957_;
v_isShared_3964_ = v_isSharedCheck_3971_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_diag_3961_);
lean_inc(v_postponed_3960_);
lean_inc(v_zetaDeltaFVarIds_3959_);
lean_inc(v_mctx_3958_);
lean_dec(v___x_3957_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3971_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3966_; 
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 1, v___x_3938_);
v___x_3966_ = v___x_3963_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_mctx_3958_);
lean_ctor_set(v_reuseFailAlloc_3970_, 1, v___x_3938_);
lean_ctor_set(v_reuseFailAlloc_3970_, 2, v_zetaDeltaFVarIds_3959_);
lean_ctor_set(v_reuseFailAlloc_3970_, 3, v_postponed_3960_);
lean_ctor_set(v_reuseFailAlloc_3970_, 4, v_diag_3961_);
v___x_3966_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3967_ = lean_st_ref_set(v___y_3937_, v___x_3966_);
v___x_3968_ = lean_box(0);
v___x_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3968_);
return v___x_3969_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0___boxed(lean_object* v___y_3976_, lean_object* v_isExporting_3977_, lean_object* v___x_3978_, lean_object* v___y_3979_, lean_object* v___x_3980_, lean_object* v_a_x3f_3981_, lean_object* v___y_3982_){
_start:
{
uint8_t v_isExporting_boxed_3983_; lean_object* v_res_3984_; 
v_isExporting_boxed_3983_ = lean_unbox(v_isExporting_3977_);
v_res_3984_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_3976_, v_isExporting_boxed_3983_, v___x_3978_, v___y_3979_, v___x_3980_, v_a_x3f_3981_);
lean_dec(v_a_x3f_3981_);
lean_dec(v___y_3979_);
lean_dec(v___y_3976_);
return v_res_3984_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3985_; 
v___x_3985_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3985_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3986_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3986_);
return v___x_3987_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_3989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3988_);
lean_ctor_set(v___x_3989_, 1, v___x_3988_);
return v___x_3989_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3990_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_3991_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
lean_ctor_set(v___x_3991_, 1, v___x_3990_);
lean_ctor_set(v___x_3991_, 2, v___x_3990_);
lean_ctor_set(v___x_3991_, 3, v___x_3990_);
lean_ctor_set(v___x_3991_, 4, v___x_3990_);
lean_ctor_set(v___x_3991_, 5, v___x_3990_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(lean_object* v_x_3992_, uint8_t v_isExporting_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v___x_3999_; lean_object* v_env_4000_; uint8_t v_isExporting_4001_; lean_object* v___x_4002_; lean_object* v_env_4003_; lean_object* v_nextMacroScope_4004_; lean_object* v_ngen_4005_; lean_object* v_auxDeclNGen_4006_; lean_object* v_traceState_4007_; lean_object* v_messages_4008_; lean_object* v_infoState_4009_; lean_object* v_snapshotTasks_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4064_; 
v___x_3999_ = lean_st_ref_get(v___y_3997_);
v_env_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc_ref(v_env_4000_);
lean_dec(v___x_3999_);
v_isExporting_4001_ = lean_ctor_get_uint8(v_env_4000_, sizeof(void*)*8);
lean_dec_ref(v_env_4000_);
v___x_4002_ = lean_st_ref_take(v___y_3997_);
v_env_4003_ = lean_ctor_get(v___x_4002_, 0);
v_nextMacroScope_4004_ = lean_ctor_get(v___x_4002_, 1);
v_ngen_4005_ = lean_ctor_get(v___x_4002_, 2);
v_auxDeclNGen_4006_ = lean_ctor_get(v___x_4002_, 3);
v_traceState_4007_ = lean_ctor_get(v___x_4002_, 4);
v_messages_4008_ = lean_ctor_get(v___x_4002_, 6);
v_infoState_4009_ = lean_ctor_get(v___x_4002_, 7);
v_snapshotTasks_4010_ = lean_ctor_get(v___x_4002_, 8);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4064_ == 0)
{
lean_object* v_unused_4065_; 
v_unused_4065_ = lean_ctor_get(v___x_4002_, 5);
lean_dec(v_unused_4065_);
v___x_4012_ = v___x_4002_;
v_isShared_4013_ = v_isSharedCheck_4064_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_snapshotTasks_4010_);
lean_inc(v_infoState_4009_);
lean_inc(v_messages_4008_);
lean_inc(v_traceState_4007_);
lean_inc(v_auxDeclNGen_4006_);
lean_inc(v_ngen_4005_);
lean_inc(v_nextMacroScope_4004_);
lean_inc(v_env_4003_);
lean_dec(v___x_4002_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4064_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4017_; 
v___x_4014_ = l_Lean_Environment_setExporting(v_env_4003_, v_isExporting_3993_);
v___x_4015_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 5, v___x_4015_);
lean_ctor_set(v___x_4012_, 0, v___x_4014_);
v___x_4017_ = v___x_4012_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4014_);
lean_ctor_set(v_reuseFailAlloc_4063_, 1, v_nextMacroScope_4004_);
lean_ctor_set(v_reuseFailAlloc_4063_, 2, v_ngen_4005_);
lean_ctor_set(v_reuseFailAlloc_4063_, 3, v_auxDeclNGen_4006_);
lean_ctor_set(v_reuseFailAlloc_4063_, 4, v_traceState_4007_);
lean_ctor_set(v_reuseFailAlloc_4063_, 5, v___x_4015_);
lean_ctor_set(v_reuseFailAlloc_4063_, 6, v_messages_4008_);
lean_ctor_set(v_reuseFailAlloc_4063_, 7, v_infoState_4009_);
lean_ctor_set(v_reuseFailAlloc_4063_, 8, v_snapshotTasks_4010_);
v___x_4017_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v_mctx_4020_; lean_object* v_zetaDeltaFVarIds_4021_; lean_object* v_postponed_4022_; lean_object* v_diag_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4061_; 
v___x_4018_ = lean_st_ref_set(v___y_3997_, v___x_4017_);
v___x_4019_ = lean_st_ref_take(v___y_3995_);
v_mctx_4020_ = lean_ctor_get(v___x_4019_, 0);
v_zetaDeltaFVarIds_4021_ = lean_ctor_get(v___x_4019_, 2);
v_postponed_4022_ = lean_ctor_get(v___x_4019_, 3);
v_diag_4023_ = lean_ctor_get(v___x_4019_, 4);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4061_ == 0)
{
lean_object* v_unused_4062_; 
v_unused_4062_ = lean_ctor_get(v___x_4019_, 1);
lean_dec(v_unused_4062_);
v___x_4025_ = v___x_4019_;
v_isShared_4026_ = v_isSharedCheck_4061_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_diag_4023_);
lean_inc(v_postponed_4022_);
lean_inc(v_zetaDeltaFVarIds_4021_);
lean_inc(v_mctx_4020_);
lean_dec(v___x_4019_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4061_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4027_; lean_object* v___x_4029_; 
v___x_4027_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3);
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 1, v___x_4027_);
v___x_4029_ = v___x_4025_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_mctx_4020_);
lean_ctor_set(v_reuseFailAlloc_4060_, 1, v___x_4027_);
lean_ctor_set(v_reuseFailAlloc_4060_, 2, v_zetaDeltaFVarIds_4021_);
lean_ctor_set(v_reuseFailAlloc_4060_, 3, v_postponed_4022_);
lean_ctor_set(v_reuseFailAlloc_4060_, 4, v_diag_4023_);
v___x_4029_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
lean_object* v___x_4030_; lean_object* v_r_4031_; 
v___x_4030_ = lean_st_ref_set(v___y_3995_, v___x_4029_);
lean_inc(v___y_3997_);
lean_inc_ref(v___y_3996_);
lean_inc(v___y_3995_);
lean_inc_ref(v___y_3994_);
v_r_4031_ = lean_apply_5(v_x_3992_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, lean_box(0));
if (lean_obj_tag(v_r_4031_) == 0)
{
lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4048_; 
v_a_4032_ = lean_ctor_get(v_r_4031_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v_r_4031_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4034_ = v_r_4031_;
v_isShared_4035_ = v_isSharedCheck_4048_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v_r_4031_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4048_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4037_; 
lean_inc(v_a_4032_);
if (v_isShared_4035_ == 0)
{
lean_ctor_set_tag(v___x_4034_, 1);
v___x_4037_ = v___x_4034_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4032_);
v___x_4037_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
lean_object* v___x_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
v___x_4038_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_3997_, v_isExporting_4001_, v___x_4015_, v___y_3995_, v___x_4027_, v___x_4037_);
lean_dec_ref(v___x_4037_);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4045_ == 0)
{
lean_object* v_unused_4046_; 
v_unused_4046_ = lean_ctor_get(v___x_4038_, 0);
lean_dec(v_unused_4046_);
v___x_4040_ = v___x_4038_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_dec(v___x_4038_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 0, v_a_4032_);
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4032_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4058_; 
v_a_4049_ = lean_ctor_get(v_r_4031_, 0);
lean_inc(v_a_4049_);
lean_dec_ref(v_r_4031_);
v___x_4050_ = lean_box(0);
v___x_4051_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_3997_, v_isExporting_4001_, v___x_4015_, v___y_3995_, v___x_4027_, v___x_4050_);
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
lean_ctor_set_tag(v___x_4053_, 1);
lean_ctor_set(v___x_4053_, 0, v_a_4049_);
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4049_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___boxed(lean_object* v_x_4066_, lean_object* v_isExporting_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
uint8_t v_isExporting_boxed_4073_; lean_object* v_res_4074_; 
v_isExporting_boxed_4073_ = lean_unbox(v_isExporting_4067_);
v_res_4074_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4066_, v_isExporting_boxed_4073_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(lean_object* v_00_u03b1_4075_, lean_object* v_x_4076_, uint8_t v_isExporting_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4076_, v_isExporting_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___boxed(lean_object* v_00_u03b1_4084_, lean_object* v_x_4085_, lean_object* v_isExporting_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
uint8_t v_isExporting_boxed_4092_; lean_object* v_res_4093_; 
v_isExporting_boxed_4092_ = lean_unbox(v_isExporting_4086_);
v_res_4093_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(v_00_u03b1_4084_, v_x_4085_, v_isExporting_boxed_4092_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(lean_object* v_lctx_4094_, lean_object* v_localInsts_4095_, lean_object* v_x_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4094_, v_localInsts_4095_, v_x_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4110_; 
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4105_ = v___x_4102_;
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4102_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
else
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
v_a_4111_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4102_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4102_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg___boxed(lean_object* v_lctx_4119_, lean_object* v_localInsts_4120_, lean_object* v_x_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
lean_object* v_res_4127_; 
v_res_4127_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4119_, v_localInsts_4120_, v_x_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
return v_res_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(lean_object* v_00_u03b1_4128_, lean_object* v_lctx_4129_, lean_object* v_localInsts_4130_, lean_object* v_x_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v___x_4137_; 
v___x_4137_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4129_, v_localInsts_4130_, v_x_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___boxed(lean_object* v_00_u03b1_4138_, lean_object* v_lctx_4139_, lean_object* v_localInsts_4140_, lean_object* v_x_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_){
_start:
{
lean_object* v_res_4147_; 
v_res_4147_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(v_00_u03b1_4138_, v_lctx_4139_, v_localInsts_4140_, v_x_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
return v_res_4147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0(lean_object* v_declName_4148_, lean_object* v_x_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4155_ = l_Lean_MessageData_ofName(v_declName_4148_);
v___x_4156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4155_);
return v___x_4156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed(lean_object* v_declName_4157_, lean_object* v_x_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Lean_Meta_mkInjectiveTheorems___lam__0(v_declName_4157_, v_x_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec_ref(v_x_4158_);
return v_res_4164_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4165_; 
v___x_4165_ = l_instMonadEIO(lean_box(0));
return v___x_4165_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(lean_object* v_msg_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v_toApplicative_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4239_; 
v___x_4176_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0);
v___x_4177_ = l_StateRefT_x27_instMonad___redArg(v___x_4176_);
v_toApplicative_4178_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4239_ == 0)
{
lean_object* v_unused_4240_; 
v_unused_4240_ = lean_ctor_get(v___x_4177_, 1);
lean_dec(v_unused_4240_);
v___x_4180_ = v___x_4177_;
v_isShared_4181_ = v_isSharedCheck_4239_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_toApplicative_4178_);
lean_dec(v___x_4177_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4239_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v_toFunctor_4182_; lean_object* v_toSeq_4183_; lean_object* v_toSeqLeft_4184_; lean_object* v_toSeqRight_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4237_; 
v_toFunctor_4182_ = lean_ctor_get(v_toApplicative_4178_, 0);
v_toSeq_4183_ = lean_ctor_get(v_toApplicative_4178_, 2);
v_toSeqLeft_4184_ = lean_ctor_get(v_toApplicative_4178_, 3);
v_toSeqRight_4185_ = lean_ctor_get(v_toApplicative_4178_, 4);
v_isSharedCheck_4237_ = !lean_is_exclusive(v_toApplicative_4178_);
if (v_isSharedCheck_4237_ == 0)
{
lean_object* v_unused_4238_; 
v_unused_4238_ = lean_ctor_get(v_toApplicative_4178_, 1);
lean_dec(v_unused_4238_);
v___x_4187_ = v_toApplicative_4178_;
v_isShared_4188_ = v_isSharedCheck_4237_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_toSeqRight_4185_);
lean_inc(v_toSeqLeft_4184_);
lean_inc(v_toSeq_4183_);
lean_inc(v_toFunctor_4182_);
lean_dec(v_toApplicative_4178_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4237_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v___f_4189_; lean_object* v___f_4190_; lean_object* v___f_4191_; lean_object* v___f_4192_; lean_object* v___x_4193_; lean_object* v___f_4194_; lean_object* v___f_4195_; lean_object* v___f_4196_; lean_object* v___x_4198_; 
v___f_4189_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1));
v___f_4190_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4182_);
v___f_4191_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4191_, 0, v_toFunctor_4182_);
v___f_4192_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4192_, 0, v_toFunctor_4182_);
v___x_4193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4193_, 0, v___f_4191_);
lean_ctor_set(v___x_4193_, 1, v___f_4192_);
v___f_4194_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4194_, 0, v_toSeqRight_4185_);
v___f_4195_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4195_, 0, v_toSeqLeft_4184_);
v___f_4196_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4196_, 0, v_toSeq_4183_);
if (v_isShared_4188_ == 0)
{
lean_ctor_set(v___x_4187_, 4, v___f_4194_);
lean_ctor_set(v___x_4187_, 3, v___f_4195_);
lean_ctor_set(v___x_4187_, 2, v___f_4196_);
lean_ctor_set(v___x_4187_, 1, v___f_4189_);
lean_ctor_set(v___x_4187_, 0, v___x_4193_);
v___x_4198_ = v___x_4187_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v___x_4193_);
lean_ctor_set(v_reuseFailAlloc_4236_, 1, v___f_4189_);
lean_ctor_set(v_reuseFailAlloc_4236_, 2, v___f_4196_);
lean_ctor_set(v_reuseFailAlloc_4236_, 3, v___f_4195_);
lean_ctor_set(v_reuseFailAlloc_4236_, 4, v___f_4194_);
v___x_4198_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
lean_object* v___x_4200_; 
if (v_isShared_4181_ == 0)
{
lean_ctor_set(v___x_4180_, 1, v___f_4190_);
lean_ctor_set(v___x_4180_, 0, v___x_4198_);
v___x_4200_ = v___x_4180_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v___x_4198_);
lean_ctor_set(v_reuseFailAlloc_4235_, 1, v___f_4190_);
v___x_4200_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
lean_object* v___x_4201_; lean_object* v_toApplicative_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4233_; 
v___x_4201_ = l_StateRefT_x27_instMonad___redArg(v___x_4200_);
v_toApplicative_4202_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4233_ == 0)
{
lean_object* v_unused_4234_; 
v_unused_4234_ = lean_ctor_get(v___x_4201_, 1);
lean_dec(v_unused_4234_);
v___x_4204_ = v___x_4201_;
v_isShared_4205_ = v_isSharedCheck_4233_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_toApplicative_4202_);
lean_dec(v___x_4201_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4233_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v_toFunctor_4206_; lean_object* v_toSeq_4207_; lean_object* v_toSeqLeft_4208_; lean_object* v_toSeqRight_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4231_; 
v_toFunctor_4206_ = lean_ctor_get(v_toApplicative_4202_, 0);
v_toSeq_4207_ = lean_ctor_get(v_toApplicative_4202_, 2);
v_toSeqLeft_4208_ = lean_ctor_get(v_toApplicative_4202_, 3);
v_toSeqRight_4209_ = lean_ctor_get(v_toApplicative_4202_, 4);
v_isSharedCheck_4231_ = !lean_is_exclusive(v_toApplicative_4202_);
if (v_isSharedCheck_4231_ == 0)
{
lean_object* v_unused_4232_; 
v_unused_4232_ = lean_ctor_get(v_toApplicative_4202_, 1);
lean_dec(v_unused_4232_);
v___x_4211_ = v_toApplicative_4202_;
v_isShared_4212_ = v_isSharedCheck_4231_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_toSeqRight_4209_);
lean_inc(v_toSeqLeft_4208_);
lean_inc(v_toSeq_4207_);
lean_inc(v_toFunctor_4206_);
lean_dec(v_toApplicative_4202_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4231_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___f_4213_; lean_object* v___f_4214_; lean_object* v___f_4215_; lean_object* v___f_4216_; lean_object* v___x_4217_; lean_object* v___f_4218_; lean_object* v___f_4219_; lean_object* v___f_4220_; lean_object* v___x_4222_; 
v___f_4213_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3));
v___f_4214_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4206_);
v___f_4215_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4215_, 0, v_toFunctor_4206_);
v___f_4216_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4216_, 0, v_toFunctor_4206_);
v___x_4217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4217_, 0, v___f_4215_);
lean_ctor_set(v___x_4217_, 1, v___f_4216_);
v___f_4218_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4218_, 0, v_toSeqRight_4209_);
v___f_4219_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4219_, 0, v_toSeqLeft_4208_);
v___f_4220_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4220_, 0, v_toSeq_4207_);
if (v_isShared_4212_ == 0)
{
lean_ctor_set(v___x_4211_, 4, v___f_4218_);
lean_ctor_set(v___x_4211_, 3, v___f_4219_);
lean_ctor_set(v___x_4211_, 2, v___f_4220_);
lean_ctor_set(v___x_4211_, 1, v___f_4213_);
lean_ctor_set(v___x_4211_, 0, v___x_4217_);
v___x_4222_ = v___x_4211_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4217_);
lean_ctor_set(v_reuseFailAlloc_4230_, 1, v___f_4213_);
lean_ctor_set(v_reuseFailAlloc_4230_, 2, v___f_4220_);
lean_ctor_set(v_reuseFailAlloc_4230_, 3, v___f_4219_);
lean_ctor_set(v_reuseFailAlloc_4230_, 4, v___f_4218_);
v___x_4222_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
lean_object* v___x_4224_; 
if (v_isShared_4205_ == 0)
{
lean_ctor_set(v___x_4204_, 1, v___f_4214_);
lean_ctor_set(v___x_4204_, 0, v___x_4222_);
v___x_4224_ = v___x_4204_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v___x_4222_);
lean_ctor_set(v_reuseFailAlloc_4229_, 1, v___f_4214_);
v___x_4224_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_19007__overap_4227_; lean_object* v___x_4228_; 
v___x_4225_ = lean_box(0);
v___x_4226_ = l_instInhabitedOfMonad___redArg(v___x_4224_, v___x_4225_);
v___x_19007__overap_4227_ = lean_panic_fn_borrowed(v___x_4226_, v_msg_4170_);
lean_dec(v___x_4226_);
lean_inc(v___y_4174_);
lean_inc_ref(v___y_4173_);
lean_inc(v___y_4172_);
lean_inc_ref(v___y_4171_);
v___x_4228_ = lean_apply_5(v___x_19007__overap_4227_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, lean_box(0));
return v___x_4228_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___boxed(lean_object* v_msg_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v_msg_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
return v_res_4247_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4249_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0));
v___x_4250_ = l_Lean_stringToMessageData(v___x_4249_);
return v___x_4250_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4(void){
_start:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; 
v___x_4253_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_4254_ = lean_unsigned_to_nat(11u);
v___x_4255_ = lean_unsigned_to_nat(122u);
v___x_4256_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3));
v___x_4257_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2));
v___x_4258_ = l_mkPanicMessageWithDecl(v___x_4257_, v___x_4256_, v___x_4255_, v___x_4254_, v___x_4253_);
return v___x_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(lean_object* v_constName_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v___x_4273_; lean_object* v_env_4274_; uint8_t v___x_4275_; lean_object* v___x_4276_; 
v___x_4273_ = lean_st_ref_get(v___y_4263_);
v_env_4274_ = lean_ctor_get(v___x_4273_, 0);
lean_inc_ref(v_env_4274_);
lean_dec(v___x_4273_);
v___x_4275_ = 0;
lean_inc(v_constName_4259_);
v___x_4276_ = l_Lean_Environment_findAsync_x3f(v_env_4274_, v_constName_4259_, v___x_4275_);
if (lean_obj_tag(v___x_4276_) == 1)
{
lean_object* v_val_4277_; uint8_t v_kind_4278_; 
v_val_4277_ = lean_ctor_get(v___x_4276_, 0);
lean_inc(v_val_4277_);
lean_dec_ref(v___x_4276_);
v_kind_4278_ = lean_ctor_get_uint8(v_val_4277_, sizeof(void*)*3);
if (v_kind_4278_ == 6)
{
lean_object* v___x_4279_; 
v___x_4279_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4277_);
if (lean_obj_tag(v___x_4279_) == 6)
{
lean_object* v_val_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4287_; 
lean_dec(v_constName_4259_);
v_val_4280_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4282_ = v___x_4279_;
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_val_4280_);
lean_dec(v___x_4279_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4285_; 
if (v_isShared_4283_ == 0)
{
lean_ctor_set_tag(v___x_4282_, 0);
v___x_4285_ = v___x_4282_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_val_4280_);
v___x_4285_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
return v___x_4285_;
}
}
}
else
{
lean_object* v___x_4288_; lean_object* v___x_4289_; 
lean_dec_ref(v___x_4279_);
v___x_4288_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4);
v___x_4289_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v___x_4288_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_);
if (lean_obj_tag(v___x_4289_) == 0)
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4298_; 
v_a_4290_ = lean_ctor_get(v___x_4289_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4292_ = v___x_4289_;
v_isShared_4293_ = v_isSharedCheck_4298_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v___x_4289_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4298_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
if (lean_obj_tag(v_a_4290_) == 0)
{
lean_del_object(v___x_4292_);
goto v___jp_4265_;
}
else
{
lean_object* v_val_4294_; lean_object* v___x_4296_; 
lean_dec(v_constName_4259_);
v_val_4294_ = lean_ctor_get(v_a_4290_, 0);
lean_inc(v_val_4294_);
lean_dec_ref(v_a_4290_);
if (v_isShared_4293_ == 0)
{
lean_ctor_set(v___x_4292_, 0, v_val_4294_);
v___x_4296_ = v___x_4292_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_val_4294_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
return v___x_4296_;
}
}
}
}
else
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4306_; 
lean_dec(v_constName_4259_);
v_a_4299_ = lean_ctor_get(v___x_4289_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4301_ = v___x_4289_;
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4289_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
if (v_isShared_4302_ == 0)
{
v___x_4304_ = v___x_4301_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_a_4299_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
return v___x_4304_;
}
}
}
}
}
else
{
lean_dec(v_val_4277_);
goto v___jp_4265_;
}
}
else
{
lean_dec(v___x_4276_);
goto v___jp_4265_;
}
v___jp_4265_:
{
lean_object* v___x_4266_; uint8_t v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4266_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4267_ = 0;
v___x_4268_ = l_Lean_MessageData_ofConstName(v_constName_4259_, v___x_4267_);
v___x_4269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4266_);
lean_ctor_set(v___x_4269_, 1, v___x_4268_);
v___x_4270_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1);
v___x_4271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4269_);
lean_ctor_set(v___x_4271_, 1, v___x_4270_);
v___x_4272_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4271_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_);
return v___x_4272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___boxed(lean_object* v_constName_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v_res_4313_; 
v_res_4313_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_constName_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(lean_object* v_head_4314_, lean_object* v___x_4315_, lean_object* v___x_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_){
_start:
{
lean_object* v___x_4322_; 
v___x_4322_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_head_4314_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4334_; 
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4325_ = v___x_4322_;
v_isShared_4326_ = v_isSharedCheck_4334_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4322_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4334_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v_numFields_4327_; uint8_t v___x_4328_; 
v_numFields_4327_ = lean_ctor_get(v_a_4323_, 4);
v___x_4328_ = lean_nat_dec_lt(v___x_4315_, v_numFields_4327_);
if (v___x_4328_ == 0)
{
lean_object* v___x_4330_; 
lean_dec(v_a_4323_);
if (v_isShared_4326_ == 0)
{
lean_ctor_set(v___x_4325_, 0, v___x_4316_);
v___x_4330_ = v___x_4325_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4316_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
else
{
lean_object* v___x_4332_; 
lean_del_object(v___x_4325_);
lean_inc(v_a_4323_);
v___x_4332_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_a_4323_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_object* v___x_4333_; 
lean_dec_ref(v___x_4332_);
v___x_4333_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_a_4323_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_);
return v___x_4333_;
}
else
{
lean_dec(v_a_4323_);
return v___x_4332_;
}
}
}
}
else
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4342_; 
v_a_4335_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4337_ = v___x_4322_;
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4322_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4340_; 
if (v_isShared_4338_ == 0)
{
v___x_4340_ = v___x_4337_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4335_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed(lean_object* v_head_4343_, lean_object* v___x_4344_, lean_object* v___x_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_){
_start:
{
lean_object* v_res_4351_; 
v_res_4351_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(v_head_4343_, v___x_4344_, v___x_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_);
lean_dec(v___y_4349_);
lean_dec_ref(v___y_4348_);
lean_dec(v___y_4347_);
lean_dec_ref(v___y_4346_);
lean_dec(v___x_4344_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(uint8_t v___y_4352_, uint8_t v___x_4353_, lean_object* v_as_x27_4354_, lean_object* v_b_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_){
_start:
{
if (lean_obj_tag(v_as_x27_4354_) == 0)
{
lean_object* v___x_4361_; 
v___x_4361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4361_, 0, v_b_4355_);
return v___x_4361_;
}
else
{
lean_object* v_head_4362_; lean_object* v_tail_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___f_4366_; uint8_t v___y_4368_; uint8_t v___x_4371_; 
v_head_4362_ = lean_ctor_get(v_as_x27_4354_, 0);
lean_inc_n(v_head_4362_, 2);
v_tail_4363_ = lean_ctor_get(v_as_x27_4354_, 1);
lean_inc(v_tail_4363_);
lean_dec_ref(v_as_x27_4354_);
v___x_4364_ = lean_unsigned_to_nat(0u);
v___x_4365_ = lean_box(0);
v___f_4366_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4366_, 0, v_head_4362_);
lean_closure_set(v___f_4366_, 1, v___x_4364_);
lean_closure_set(v___f_4366_, 2, v___x_4365_);
v___x_4371_ = l_Lean_isPrivateName(v_head_4362_);
lean_dec(v_head_4362_);
if (v___x_4371_ == 0)
{
v___y_4368_ = v___y_4352_;
goto v___jp_4367_;
}
else
{
v___y_4368_ = v___x_4353_;
goto v___jp_4367_;
}
v___jp_4367_:
{
lean_object* v___x_4369_; 
v___x_4369_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v___f_4366_, v___y_4368_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_dec_ref(v___x_4369_);
v_as_x27_4354_ = v_tail_4363_;
v_b_4355_ = v___x_4365_;
goto _start;
}
else
{
lean_dec(v_tail_4363_);
return v___x_4369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___boxed(lean_object* v___y_4372_, lean_object* v___x_4373_, lean_object* v_as_x27_4374_, lean_object* v_b_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_){
_start:
{
uint8_t v___y_20116__boxed_4381_; uint8_t v___x_20117__boxed_4382_; lean_object* v_res_4383_; 
v___y_20116__boxed_4381_ = lean_unbox(v___y_4372_);
v___x_20117__boxed_4382_ = lean_unbox(v___x_4373_);
v_res_4383_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_20116__boxed_4381_, v___x_20117__boxed_4382_, v_as_x27_4374_, v_b_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4378_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
return v_res_4383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1(uint8_t v___y_4384_, uint8_t v_hasTrace_4385_, lean_object* v_ctors_4386_, lean_object* v___x_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_){
_start:
{
lean_object* v___x_4393_; 
v___x_4393_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4384_, v_hasTrace_4385_, v_ctors_4386_, v___x_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4400_; 
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4400_ == 0)
{
lean_object* v_unused_4401_; 
v_unused_4401_ = lean_ctor_get(v___x_4393_, 0);
lean_dec(v_unused_4401_);
v___x_4395_ = v___x_4393_;
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
else
{
lean_dec(v___x_4393_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4398_; 
if (v_isShared_4396_ == 0)
{
lean_ctor_set(v___x_4395_, 0, v___x_4387_);
v___x_4398_ = v___x_4395_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v___x_4387_);
v___x_4398_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
return v___x_4398_;
}
}
}
else
{
return v___x_4393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed(lean_object* v___y_4402_, lean_object* v_hasTrace_4403_, lean_object* v_ctors_4404_, lean_object* v___x_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_){
_start:
{
uint8_t v___y_20161__boxed_4411_; uint8_t v_hasTrace_boxed_4412_; lean_object* v_res_4413_; 
v___y_20161__boxed_4411_ = lean_unbox(v___y_4402_);
v_hasTrace_boxed_4412_ = lean_unbox(v_hasTrace_4403_);
v_res_4413_ = l_Lean_Meta_mkInjectiveTheorems___lam__1(v___y_20161__boxed_4411_, v_hasTrace_boxed_4412_, v_ctors_4404_, v___x_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2(uint8_t v_hasTrace_4414_, uint8_t v___x_4415_, lean_object* v_ctors_4416_, lean_object* v___x_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_){
_start:
{
lean_object* v___x_4423_; 
v___x_4423_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v_hasTrace_4414_, v___x_4415_, v_ctors_4416_, v___x_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4430_ == 0)
{
lean_object* v_unused_4431_; 
v_unused_4431_ = lean_ctor_get(v___x_4423_, 0);
lean_dec(v_unused_4431_);
v___x_4425_ = v___x_4423_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_dec(v___x_4423_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 0, v___x_4417_);
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v___x_4417_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
else
{
return v___x_4423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed(lean_object* v_hasTrace_4432_, lean_object* v___x_4433_, lean_object* v_ctors_4434_, lean_object* v___x_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
uint8_t v_hasTrace_boxed_4441_; uint8_t v___x_20202__boxed_4442_; lean_object* v_res_4443_; 
v_hasTrace_boxed_4441_ = lean_unbox(v_hasTrace_4432_);
v___x_20202__boxed_4442_ = lean_unbox(v___x_4433_);
v_res_4443_ = l_Lean_Meta_mkInjectiveTheorems___lam__2(v_hasTrace_boxed_4441_, v___x_20202__boxed_4442_, v_ctors_4434_, v___x_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3(uint8_t v___x_4444_, uint8_t v_isUnsafe_4445_, lean_object* v_ctors_4446_, lean_object* v___x_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
lean_object* v___x_4453_; 
v___x_4453_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___x_4444_, v_isUnsafe_4445_, v_ctors_4446_, v___x_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
if (lean_obj_tag(v___x_4453_) == 0)
{
lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4460_; 
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4453_);
if (v_isSharedCheck_4460_ == 0)
{
lean_object* v_unused_4461_; 
v_unused_4461_ = lean_ctor_get(v___x_4453_, 0);
lean_dec(v_unused_4461_);
v___x_4455_ = v___x_4453_;
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
else
{
lean_dec(v___x_4453_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v___x_4458_; 
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 0, v___x_4447_);
v___x_4458_ = v___x_4455_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v___x_4447_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
}
else
{
return v___x_4453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3___boxed(lean_object* v___x_4462_, lean_object* v_isUnsafe_4463_, lean_object* v_ctors_4464_, lean_object* v___x_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_){
_start:
{
uint8_t v___x_20243__boxed_4471_; uint8_t v_isUnsafe_boxed_4472_; lean_object* v_res_4473_; 
v___x_20243__boxed_4471_ = lean_unbox(v___x_4462_);
v_isUnsafe_boxed_4472_ = lean_unbox(v_isUnsafe_4463_);
v_res_4473_ = l_Lean_Meta_mkInjectiveTheorems___lam__3(v___x_20243__boxed_4471_, v_isUnsafe_boxed_4472_, v_ctors_4464_, v___x_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
lean_dec(v___y_4467_);
lean_dec_ref(v___y_4466_);
return v_res_4473_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; 
v___x_4475_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0));
v___x_4476_ = l_Lean_stringToMessageData(v___x_4475_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(lean_object* v_constName_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_){
_start:
{
lean_object* v___x_4483_; lean_object* v_env_4484_; lean_object* v___x_4485_; 
v___x_4483_ = lean_st_ref_get(v___y_4481_);
v_env_4484_ = lean_ctor_get(v___x_4483_, 0);
lean_inc_ref(v_env_4484_);
lean_dec(v___x_4483_);
lean_inc(v_constName_4477_);
v___x_4485_ = l_Lean_isInductiveCore_x3f(v_env_4484_, v_constName_4477_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v___x_4486_; uint8_t v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4486_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4487_ = 0;
v___x_4488_ = l_Lean_MessageData_ofConstName(v_constName_4477_, v___x_4487_);
v___x_4489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4489_, 0, v___x_4486_);
lean_ctor_set(v___x_4489_, 1, v___x_4488_);
v___x_4490_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1);
v___x_4491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4491_, 0, v___x_4489_);
lean_ctor_set(v___x_4491_, 1, v___x_4490_);
v___x_4492_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4491_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_);
return v___x_4492_;
}
else
{
lean_object* v_val_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4500_; 
lean_dec(v_constName_4477_);
v_val_4493_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4500_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4500_ == 0)
{
v___x_4495_ = v___x_4485_;
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_val_4493_);
lean_dec(v___x_4485_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4498_; 
if (v_isShared_4496_ == 0)
{
lean_ctor_set_tag(v___x_4495_, 0);
v___x_4498_ = v___x_4495_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v_val_4493_);
v___x_4498_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
return v___x_4498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___boxed(lean_object* v_constName_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
lean_object* v_res_4507_; 
v_res_4507_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_constName_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
return v_res_4507_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__0(void){
_start:
{
lean_object* v___x_4508_; 
v___x_4508_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4508_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__1(void){
_start:
{
lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4509_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_4510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4509_);
return v___x_4510_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__2(void){
_start:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; 
v___x_4511_ = lean_unsigned_to_nat(32u);
v___x_4512_ = lean_mk_empty_array_with_capacity(v___x_4511_);
v___x_4513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4513_, 0, v___x_4512_);
return v___x_4513_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__3(void){
_start:
{
size_t v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___x_4514_ = ((size_t)5ULL);
v___x_4515_ = lean_unsigned_to_nat(0u);
v___x_4516_ = lean_unsigned_to_nat(32u);
v___x_4517_ = lean_mk_empty_array_with_capacity(v___x_4516_);
v___x_4518_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4519_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4519_, 0, v___x_4518_);
lean_ctor_set(v___x_4519_, 1, v___x_4517_);
lean_ctor_set(v___x_4519_, 2, v___x_4515_);
lean_ctor_set(v___x_4519_, 3, v___x_4515_);
lean_ctor_set_usize(v___x_4519_, 4, v___x_4514_);
return v___x_4519_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__4(void){
_start:
{
lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4520_ = lean_box(1);
v___x_4521_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4522_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_4523_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4523_, 0, v___x_4522_);
lean_ctor_set(v___x_4523_, 1, v___x_4521_);
lean_ctor_set(v___x_4523_, 2, v___x_4520_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object* v_declName_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_){
_start:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; 
v___x_4532_ = lean_st_ref_get(v_a_4530_);
lean_inc(v_declName_4526_);
v___x_4533_ = l_Lean_Meta_isInductivePredicate(v_declName_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
if (lean_obj_tag(v___x_4533_) == 0)
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4730_; 
v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4730_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4730_ == 0)
{
v___x_4536_ = v___x_4533_;
v_isShared_4537_ = v_isSharedCheck_4730_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4533_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4730_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v_env_4543_; lean_object* v___f_4544_; lean_object* v___x_4545_; uint8_t v___x_4546_; lean_object* v___y_4548_; lean_object* v___y_4549_; uint8_t v___y_4550_; lean_object* v___y_4551_; lean_object* v___y_4552_; lean_object* v___y_4553_; lean_object* v_a_4554_; lean_object* v___y_4564_; lean_object* v___y_4565_; uint8_t v___y_4566_; lean_object* v___y_4567_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v_a_4570_; lean_object* v___y_4573_; lean_object* v___y_4574_; uint8_t v___y_4575_; lean_object* v___y_4576_; lean_object* v___y_4577_; lean_object* v___y_4578_; lean_object* v_a_4579_; lean_object* v___y_4582_; lean_object* v___y_4583_; uint8_t v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v_a_4588_; lean_object* v___y_4601_; lean_object* v___y_4602_; uint8_t v___y_4603_; lean_object* v___y_4604_; lean_object* v___y_4605_; lean_object* v___y_4606_; lean_object* v_a_4607_; lean_object* v___y_4610_; lean_object* v___y_4611_; uint8_t v___y_4612_; lean_object* v___y_4613_; lean_object* v___y_4614_; lean_object* v___y_4615_; lean_object* v_a_4616_; uint8_t v___y_4619_; lean_object* v___y_4620_; lean_object* v___y_4621_; uint8_t v___y_4622_; lean_object* v___y_4623_; uint8_t v___y_4661_; uint8_t v___x_4726_; 
v_env_4543_ = lean_ctor_get(v___x_4532_, 0);
lean_inc_ref(v_env_4543_);
lean_dec(v___x_4532_);
lean_inc(v_declName_4526_);
v___f_4544_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4544_, 0, v_declName_4526_);
v___x_4545_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_4546_ = 1;
v___x_4726_ = l_Lean_Environment_contains(v_env_4543_, v___x_4545_, v___x_4546_);
if (v___x_4726_ == 0)
{
v___y_4661_ = v___x_4726_;
goto v___jp_4660_;
}
else
{
lean_object* v_options_4727_; lean_object* v___x_4728_; uint8_t v___x_4729_; 
v_options_4727_ = lean_ctor_get(v_a_4529_, 2);
v___x_4728_ = l_Lean_Meta_genInjectivity;
v___x_4729_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4727_, v___x_4728_);
v___y_4661_ = v___x_4729_;
goto v___jp_4660_;
}
v___jp_4538_:
{
lean_object* v___x_4539_; lean_object* v___x_4541_; 
v___x_4539_ = lean_box(0);
if (v_isShared_4537_ == 0)
{
lean_ctor_set(v___x_4536_, 0, v___x_4539_);
v___x_4541_ = v___x_4536_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v___x_4539_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
return v___x_4541_;
}
}
v___jp_4547_:
{
lean_object* v___x_4555_; double v___x_4556_; double v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; 
v___x_4555_ = lean_io_get_num_heartbeats();
v___x_4556_ = lean_float_of_nat(v___y_4553_);
v___x_4557_ = lean_float_of_nat(v___x_4555_);
v___x_4558_ = lean_box_float(v___x_4556_);
v___x_4559_ = lean_box_float(v___x_4557_);
v___x_4560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4560_, 0, v___x_4558_);
lean_ctor_set(v___x_4560_, 1, v___x_4559_);
v___x_4561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4561_, 0, v_a_4554_);
lean_ctor_set(v___x_4561_, 1, v___x_4560_);
lean_inc_ref(v___y_4548_);
lean_inc(v___y_4549_);
v___x_4562_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4549_, v___x_4546_, v___y_4548_, v___y_4552_, v___y_4550_, v___y_4551_, v___f_4544_, v___x_4561_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
return v___x_4562_;
}
v___jp_4563_:
{
lean_object* v___x_4571_; 
v___x_4571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4571_, 0, v_a_4570_);
v___y_4548_ = v___y_4565_;
v___y_4549_ = v___y_4564_;
v___y_4550_ = v___y_4566_;
v___y_4551_ = v___y_4567_;
v___y_4552_ = v___y_4568_;
v___y_4553_ = v___y_4569_;
v_a_4554_ = v___x_4571_;
goto v___jp_4547_;
}
v___jp_4572_:
{
lean_object* v___x_4580_; 
v___x_4580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4580_, 0, v_a_4579_);
v___y_4548_ = v___y_4574_;
v___y_4549_ = v___y_4573_;
v___y_4550_ = v___y_4575_;
v___y_4551_ = v___y_4576_;
v___y_4552_ = v___y_4577_;
v___y_4553_ = v___y_4578_;
v_a_4554_ = v___x_4580_;
goto v___jp_4547_;
}
v___jp_4581_:
{
lean_object* v___x_4589_; double v___x_4590_; double v___x_4591_; double v___x_4592_; double v___x_4593_; double v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4589_ = lean_io_mono_nanos_now();
v___x_4590_ = lean_float_of_nat(v___y_4585_);
v___x_4591_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_4592_ = lean_float_div(v___x_4590_, v___x_4591_);
v___x_4593_ = lean_float_of_nat(v___x_4589_);
v___x_4594_ = lean_float_div(v___x_4593_, v___x_4591_);
v___x_4595_ = lean_box_float(v___x_4592_);
v___x_4596_ = lean_box_float(v___x_4594_);
v___x_4597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4597_, 0, v___x_4595_);
lean_ctor_set(v___x_4597_, 1, v___x_4596_);
v___x_4598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4598_, 0, v_a_4588_);
lean_ctor_set(v___x_4598_, 1, v___x_4597_);
lean_inc_ref(v___y_4582_);
lean_inc(v___y_4583_);
v___x_4599_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4583_, v___x_4546_, v___y_4582_, v___y_4587_, v___y_4584_, v___y_4586_, v___f_4544_, v___x_4598_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
return v___x_4599_;
}
v___jp_4600_:
{
lean_object* v___x_4608_; 
v___x_4608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4608_, 0, v_a_4607_);
v___y_4582_ = v___y_4602_;
v___y_4583_ = v___y_4601_;
v___y_4584_ = v___y_4603_;
v___y_4585_ = v___y_4604_;
v___y_4586_ = v___y_4605_;
v___y_4587_ = v___y_4606_;
v_a_4588_ = v___x_4608_;
goto v___jp_4581_;
}
v___jp_4609_:
{
lean_object* v___x_4617_; 
v___x_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4617_, 0, v_a_4616_);
v___y_4582_ = v___y_4611_;
v___y_4583_ = v___y_4610_;
v___y_4584_ = v___y_4612_;
v___y_4585_ = v___y_4613_;
v___y_4586_ = v___y_4614_;
v___y_4587_ = v___y_4615_;
v_a_4588_ = v___x_4617_;
goto v___jp_4581_;
}
v___jp_4618_:
{
lean_object* v___x_4624_; lean_object* v_a_4625_; lean_object* v___x_4626_; uint8_t v___x_4627_; 
v___x_4624_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_4530_);
v_a_4625_ = lean_ctor_get(v___x_4624_, 0);
lean_inc(v_a_4625_);
lean_dec_ref(v___x_4624_);
v___x_4626_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4627_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v___y_4623_, v___x_4626_);
if (v___x_4627_ == 0)
{
lean_object* v___x_4628_; lean_object* v___x_4629_; 
v___x_4628_ = lean_io_mono_nanos_now();
v___x_4629_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
if (lean_obj_tag(v___x_4629_) == 0)
{
lean_object* v_a_4630_; uint8_t v_isUnsafe_4631_; 
v_a_4630_ = lean_ctor_get(v___x_4629_, 0);
lean_inc(v_a_4630_);
lean_dec_ref(v___x_4629_);
v_isUnsafe_4631_ = lean_ctor_get_uint8(v_a_4630_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4631_ == 0)
{
lean_object* v_ctors_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___f_4638_; lean_object* v___x_4639_; 
v_ctors_4632_ = lean_ctor_get(v_a_4630_, 4);
lean_inc(v_ctors_4632_);
lean_dec(v_a_4630_);
v___x_4633_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4634_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4635_ = lean_box(0);
v___x_4636_ = lean_box(v___y_4619_);
v___x_4637_ = lean_box(v___x_4627_);
v___f_4638_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed), 9, 4);
lean_closure_set(v___f_4638_, 0, v___x_4636_);
lean_closure_set(v___f_4638_, 1, v___x_4637_);
lean_closure_set(v___f_4638_, 2, v_ctors_4632_);
lean_closure_set(v___f_4638_, 3, v___x_4635_);
v___x_4639_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4633_, v___x_4634_, v___f_4638_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
if (lean_obj_tag(v___x_4639_) == 0)
{
lean_object* v_a_4640_; 
v_a_4640_ = lean_ctor_get(v___x_4639_, 0);
lean_inc(v_a_4640_);
lean_dec_ref(v___x_4639_);
v___y_4601_ = v___y_4620_;
v___y_4602_ = v___y_4621_;
v___y_4603_ = v___y_4622_;
v___y_4604_ = v___x_4628_;
v___y_4605_ = v_a_4625_;
v___y_4606_ = v___y_4623_;
v_a_4607_ = v_a_4640_;
goto v___jp_4600_;
}
else
{
lean_object* v_a_4641_; 
v_a_4641_ = lean_ctor_get(v___x_4639_, 0);
lean_inc(v_a_4641_);
lean_dec_ref(v___x_4639_);
v___y_4610_ = v___y_4620_;
v___y_4611_ = v___y_4621_;
v___y_4612_ = v___y_4622_;
v___y_4613_ = v___x_4628_;
v___y_4614_ = v_a_4625_;
v___y_4615_ = v___y_4623_;
v_a_4616_ = v_a_4641_;
goto v___jp_4609_;
}
}
else
{
lean_object* v___x_4642_; 
lean_dec(v_a_4630_);
v___x_4642_ = lean_box(0);
v___y_4601_ = v___y_4620_;
v___y_4602_ = v___y_4621_;
v___y_4603_ = v___y_4622_;
v___y_4604_ = v___x_4628_;
v___y_4605_ = v_a_4625_;
v___y_4606_ = v___y_4623_;
v_a_4607_ = v___x_4642_;
goto v___jp_4600_;
}
}
else
{
lean_object* v_a_4643_; 
v_a_4643_ = lean_ctor_get(v___x_4629_, 0);
lean_inc(v_a_4643_);
lean_dec_ref(v___x_4629_);
v___y_4610_ = v___y_4620_;
v___y_4611_ = v___y_4621_;
v___y_4612_ = v___y_4622_;
v___y_4613_ = v___x_4628_;
v___y_4614_ = v_a_4625_;
v___y_4615_ = v___y_4623_;
v_a_4616_ = v_a_4643_;
goto v___jp_4609_;
}
}
else
{
lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4644_ = lean_io_get_num_heartbeats();
v___x_4645_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
if (lean_obj_tag(v___x_4645_) == 0)
{
lean_object* v_a_4646_; uint8_t v_isUnsafe_4647_; 
v_a_4646_ = lean_ctor_get(v___x_4645_, 0);
lean_inc(v_a_4646_);
lean_dec_ref(v___x_4645_);
v_isUnsafe_4647_ = lean_ctor_get_uint8(v_a_4646_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4647_ == 0)
{
lean_object* v_ctors_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___f_4654_; lean_object* v___x_4655_; 
v_ctors_4648_ = lean_ctor_get(v_a_4646_, 4);
lean_inc(v_ctors_4648_);
lean_dec(v_a_4646_);
v___x_4649_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4650_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4651_ = lean_box(0);
v___x_4652_ = lean_box(v___x_4627_);
v___x_4653_ = lean_box(v_isUnsafe_4647_);
v___f_4654_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__3___boxed), 9, 4);
lean_closure_set(v___f_4654_, 0, v___x_4652_);
lean_closure_set(v___f_4654_, 1, v___x_4653_);
lean_closure_set(v___f_4654_, 2, v_ctors_4648_);
lean_closure_set(v___f_4654_, 3, v___x_4651_);
v___x_4655_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4649_, v___x_4650_, v___f_4654_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
if (lean_obj_tag(v___x_4655_) == 0)
{
lean_object* v_a_4656_; 
v_a_4656_ = lean_ctor_get(v___x_4655_, 0);
lean_inc(v_a_4656_);
lean_dec_ref(v___x_4655_);
v___y_4564_ = v___y_4620_;
v___y_4565_ = v___y_4621_;
v___y_4566_ = v___y_4622_;
v___y_4567_ = v_a_4625_;
v___y_4568_ = v___y_4623_;
v___y_4569_ = v___x_4644_;
v_a_4570_ = v_a_4656_;
goto v___jp_4563_;
}
else
{
lean_object* v_a_4657_; 
v_a_4657_ = lean_ctor_get(v___x_4655_, 0);
lean_inc(v_a_4657_);
lean_dec_ref(v___x_4655_);
v___y_4573_ = v___y_4620_;
v___y_4574_ = v___y_4621_;
v___y_4575_ = v___y_4622_;
v___y_4576_ = v_a_4625_;
v___y_4577_ = v___y_4623_;
v___y_4578_ = v___x_4644_;
v_a_4579_ = v_a_4657_;
goto v___jp_4572_;
}
}
else
{
lean_object* v___x_4658_; 
lean_dec(v_a_4646_);
v___x_4658_ = lean_box(0);
v___y_4564_ = v___y_4620_;
v___y_4565_ = v___y_4621_;
v___y_4566_ = v___y_4622_;
v___y_4567_ = v_a_4625_;
v___y_4568_ = v___y_4623_;
v___y_4569_ = v___x_4644_;
v_a_4570_ = v___x_4658_;
goto v___jp_4563_;
}
}
else
{
lean_object* v_a_4659_; 
v_a_4659_ = lean_ctor_get(v___x_4645_, 0);
lean_inc(v_a_4659_);
lean_dec_ref(v___x_4645_);
v___y_4573_ = v___y_4620_;
v___y_4574_ = v___y_4621_;
v___y_4575_ = v___y_4622_;
v___y_4576_ = v_a_4625_;
v___y_4577_ = v___y_4623_;
v___y_4578_ = v___x_4644_;
v_a_4579_ = v_a_4659_;
goto v___jp_4572_;
}
}
}
v___jp_4660_:
{
if (v___y_4661_ == 0)
{
lean_dec_ref(v___f_4544_);
lean_dec(v_a_4534_);
lean_dec(v_declName_4526_);
goto v___jp_4538_;
}
else
{
uint8_t v___x_4662_; 
v___x_4662_ = lean_unbox(v_a_4534_);
lean_dec(v_a_4534_);
if (v___x_4662_ == 0)
{
lean_object* v_options_4663_; uint8_t v_hasTrace_4664_; 
lean_del_object(v___x_4536_);
v_options_4663_ = lean_ctor_get(v_a_4529_, 2);
v_hasTrace_4664_ = lean_ctor_get_uint8(v_options_4663_, sizeof(void*)*1);
if (v_hasTrace_4664_ == 0)
{
lean_object* v___x_4665_; 
lean_dec_ref(v___f_4544_);
v___x_4665_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4683_; 
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
v_isSharedCheck_4683_ = !lean_is_exclusive(v___x_4665_);
if (v_isSharedCheck_4683_ == 0)
{
v___x_4668_ = v___x_4665_;
v_isShared_4669_ = v_isSharedCheck_4683_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_a_4666_);
lean_dec(v___x_4665_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4683_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
uint8_t v_isUnsafe_4670_; 
v_isUnsafe_4670_ = lean_ctor_get_uint8(v_a_4666_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4670_ == 0)
{
lean_object* v_ctors_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___f_4677_; lean_object* v___x_4678_; 
lean_del_object(v___x_4668_);
v_ctors_4671_ = lean_ctor_get(v_a_4666_, 4);
lean_inc(v_ctors_4671_);
lean_dec(v_a_4666_);
v___x_4672_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4673_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4674_ = lean_box(0);
v___x_4675_ = lean_box(v___y_4661_);
v___x_4676_ = lean_box(v_hasTrace_4664_);
v___f_4677_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4677_, 0, v___x_4675_);
lean_closure_set(v___f_4677_, 1, v___x_4676_);
lean_closure_set(v___f_4677_, 2, v_ctors_4671_);
lean_closure_set(v___f_4677_, 3, v___x_4674_);
v___x_4678_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4672_, v___x_4673_, v___f_4677_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
return v___x_4678_;
}
else
{
lean_object* v___x_4679_; lean_object* v___x_4681_; 
lean_dec(v_a_4666_);
v___x_4679_ = lean_box(0);
if (v_isShared_4669_ == 0)
{
lean_ctor_set(v___x_4668_, 0, v___x_4679_);
v___x_4681_ = v___x_4668_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v___x_4679_);
v___x_4681_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
return v___x_4681_;
}
}
}
}
else
{
lean_object* v_a_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4691_; 
v_a_4684_ = lean_ctor_get(v___x_4665_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v___x_4665_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4686_ = v___x_4665_;
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_a_4684_);
lean_dec(v___x_4665_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
lean_object* v___x_4689_; 
if (v_isShared_4687_ == 0)
{
v___x_4689_ = v___x_4686_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_a_4684_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; uint8_t v___x_4696_; 
v_inheritedTraceOptions_4692_ = lean_ctor_get(v_a_4529_, 13);
v___x_4693_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4694_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_4695_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_4696_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4692_, v_options_4663_, v___x_4695_);
if (v___x_4696_ == 0)
{
lean_object* v___x_4697_; uint8_t v___x_4698_; 
v___x_4697_ = l_Lean_trace_profiler;
v___x_4698_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4663_, v___x_4697_);
if (v___x_4698_ == 0)
{
lean_object* v___x_4699_; 
lean_dec_ref(v___f_4544_);
v___x_4699_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
if (lean_obj_tag(v___x_4699_) == 0)
{
lean_object* v_a_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4717_; 
v_a_4700_ = lean_ctor_get(v___x_4699_, 0);
v_isSharedCheck_4717_ = !lean_is_exclusive(v___x_4699_);
if (v_isSharedCheck_4717_ == 0)
{
v___x_4702_ = v___x_4699_;
v_isShared_4703_ = v_isSharedCheck_4717_;
goto v_resetjp_4701_;
}
else
{
lean_inc(v_a_4700_);
lean_dec(v___x_4699_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4717_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
uint8_t v_isUnsafe_4704_; 
v_isUnsafe_4704_ = lean_ctor_get_uint8(v_a_4700_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4704_ == 0)
{
lean_object* v_ctors_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___f_4711_; lean_object* v___x_4712_; 
lean_del_object(v___x_4702_);
v_ctors_4705_ = lean_ctor_get(v_a_4700_, 4);
lean_inc(v_ctors_4705_);
lean_dec(v_a_4700_);
v___x_4706_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4707_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4708_ = lean_box(0);
v___x_4709_ = lean_box(v_hasTrace_4664_);
v___x_4710_ = lean_box(v___x_4698_);
v___f_4711_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed), 9, 4);
lean_closure_set(v___f_4711_, 0, v___x_4709_);
lean_closure_set(v___f_4711_, 1, v___x_4710_);
lean_closure_set(v___f_4711_, 2, v_ctors_4705_);
lean_closure_set(v___f_4711_, 3, v___x_4708_);
v___x_4712_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4706_, v___x_4707_, v___f_4711_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
return v___x_4712_;
}
else
{
lean_object* v___x_4713_; lean_object* v___x_4715_; 
lean_dec(v_a_4700_);
v___x_4713_ = lean_box(0);
if (v_isShared_4703_ == 0)
{
lean_ctor_set(v___x_4702_, 0, v___x_4713_);
v___x_4715_ = v___x_4702_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v___x_4713_);
v___x_4715_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
return v___x_4715_;
}
}
}
}
else
{
lean_object* v_a_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4725_; 
v_a_4718_ = lean_ctor_get(v___x_4699_, 0);
v_isSharedCheck_4725_ = !lean_is_exclusive(v___x_4699_);
if (v_isSharedCheck_4725_ == 0)
{
v___x_4720_ = v___x_4699_;
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_a_4718_);
lean_dec(v___x_4699_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4723_; 
if (v_isShared_4721_ == 0)
{
v___x_4723_ = v___x_4720_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_a_4718_);
v___x_4723_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
return v___x_4723_;
}
}
}
}
else
{
v___y_4619_ = v_hasTrace_4664_;
v___y_4620_ = v___x_4693_;
v___y_4621_ = v___x_4694_;
v___y_4622_ = v___x_4696_;
v___y_4623_ = v_options_4663_;
goto v___jp_4618_;
}
}
else
{
v___y_4619_ = v_hasTrace_4664_;
v___y_4620_ = v___x_4693_;
v___y_4621_ = v___x_4694_;
v___y_4622_ = v___x_4696_;
v___y_4623_ = v_options_4663_;
goto v___jp_4618_;
}
}
}
else
{
lean_dec_ref(v___f_4544_);
lean_dec(v_declName_4526_);
goto v___jp_4538_;
}
}
}
}
}
else
{
lean_object* v_a_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4738_; 
lean_dec(v___x_4532_);
lean_dec(v_declName_4526_);
v_a_4731_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4738_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4738_ == 0)
{
v___x_4733_ = v___x_4533_;
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_a_4731_);
lean_dec(v___x_4533_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object* v_declName_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l_Lean_Meta_mkInjectiveTheorems(v_declName_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_);
lean_dec(v_a_4743_);
lean_dec_ref(v_a_4742_);
lean_dec(v_a_4741_);
lean_dec_ref(v_a_4740_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t v___y_4746_, uint8_t v___x_4747_, lean_object* v_as_4748_, lean_object* v_as_x27_4749_, lean_object* v_b_4750_, lean_object* v_a_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_){
_start:
{
lean_object* v___x_4757_; 
v___x_4757_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4746_, v___x_4747_, v_as_x27_4749_, v_b_4750_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_);
return v___x_4757_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object* v___y_4758_, lean_object* v___x_4759_, lean_object* v_as_4760_, lean_object* v_as_x27_4761_, lean_object* v_b_4762_, lean_object* v_a_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_){
_start:
{
uint8_t v___y_20870__boxed_4769_; uint8_t v___x_20871__boxed_4770_; lean_object* v_res_4771_; 
v___y_20870__boxed_4769_ = lean_unbox(v___y_4758_);
v___x_20871__boxed_4770_ = lean_unbox(v___x_4759_);
v_res_4771_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(v___y_20870__boxed_4769_, v___x_20871__boxed_4770_, v_as_4760_, v_as_x27_4761_, v_b_4762_, v_a_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
lean_dec(v___y_4767_);
lean_dec_ref(v___y_4766_);
lean_dec(v___y_4765_);
lean_dec_ref(v___y_4764_);
lean_dec(v_as_4760_);
return v_res_4771_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; 
v___x_4812_ = lean_unsigned_to_nat(4172903888u);
v___x_4813_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4814_ = l_Lean_Name_num___override(v___x_4813_, v___x_4812_);
return v___x_4814_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; 
v___x_4816_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4817_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4818_ = l_Lean_Name_str___override(v___x_4817_, v___x_4816_);
return v___x_4818_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; 
v___x_4820_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4821_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4822_ = l_Lean_Name_str___override(v___x_4821_, v___x_4820_);
return v___x_4822_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; 
v___x_4823_ = lean_unsigned_to_nat(2u);
v___x_4824_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4825_ = l_Lean_Name_num___override(v___x_4824_, v___x_4823_);
return v___x_4825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4827_; uint8_t v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; 
v___x_4827_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4828_ = 0;
v___x_4829_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4830_ = l_Lean_registerTraceClass(v___x_4827_, v___x_4828_, v___x_4829_);
return v___x_4830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2____boxed(lean_object* v_a_4831_){
_start:
{
lean_object* v_res_4832_; 
v_res_4832_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
return v_res_4832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(lean_object* v_a_4833_, lean_object* v_b_4834_){
_start:
{
lean_object* v_array_4835_; lean_object* v_start_4836_; lean_object* v_stop_4837_; lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4850_; 
v_array_4835_ = lean_ctor_get(v_a_4833_, 0);
v_start_4836_ = lean_ctor_get(v_a_4833_, 1);
v_stop_4837_ = lean_ctor_get(v_a_4833_, 2);
v_isSharedCheck_4850_ = !lean_is_exclusive(v_a_4833_);
if (v_isSharedCheck_4850_ == 0)
{
v___x_4839_ = v_a_4833_;
v_isShared_4840_ = v_isSharedCheck_4850_;
goto v_resetjp_4838_;
}
else
{
lean_inc(v_stop_4837_);
lean_inc(v_start_4836_);
lean_inc(v_array_4835_);
lean_dec(v_a_4833_);
v___x_4839_ = lean_box(0);
v_isShared_4840_ = v_isSharedCheck_4850_;
goto v_resetjp_4838_;
}
v_resetjp_4838_:
{
uint8_t v___x_4841_; 
v___x_4841_ = lean_nat_dec_lt(v_start_4836_, v_stop_4837_);
if (v___x_4841_ == 0)
{
lean_del_object(v___x_4839_);
lean_dec(v_stop_4837_);
lean_dec(v_start_4836_);
lean_dec_ref(v_array_4835_);
return v_b_4834_;
}
else
{
lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4845_; 
v___x_4842_ = lean_unsigned_to_nat(1u);
v___x_4843_ = lean_nat_add(v_start_4836_, v___x_4842_);
lean_inc_ref(v_array_4835_);
if (v_isShared_4840_ == 0)
{
lean_ctor_set(v___x_4839_, 1, v___x_4843_);
v___x_4845_ = v___x_4839_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4849_; 
v_reuseFailAlloc_4849_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4849_, 0, v_array_4835_);
lean_ctor_set(v_reuseFailAlloc_4849_, 1, v___x_4843_);
lean_ctor_set(v_reuseFailAlloc_4849_, 2, v_stop_4837_);
v___x_4845_ = v_reuseFailAlloc_4849_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; 
v___x_4846_ = lean_array_fget(v_array_4835_, v_start_4836_);
lean_dec(v_start_4836_);
lean_dec_ref(v_array_4835_);
v___x_4847_ = lean_array_push(v_b_4834_, v___x_4846_);
v_a_4833_ = v___x_4845_;
v_b_4834_ = v___x_4847_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4851_; 
v___x_4851_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4851_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_4852_; lean_object* v___x_4853_; 
v___x_4852_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4853_, 0, v___x_4852_);
return v___x_4853_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; 
v___x_4854_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4855_ = lean_unsigned_to_nat(0u);
v___x_4856_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4855_);
lean_ctor_set(v___x_4856_, 1, v___x_4855_);
lean_ctor_set(v___x_4856_, 2, v___x_4855_);
lean_ctor_set(v___x_4856_, 3, v___x_4854_);
lean_ctor_set(v___x_4856_, 4, v___x_4854_);
lean_ctor_set(v___x_4856_, 5, v___x_4854_);
lean_ctor_set(v___x_4856_, 6, v___x_4854_);
lean_ctor_set(v___x_4856_, 7, v___x_4854_);
lean_ctor_set(v___x_4856_, 8, v___x_4854_);
return v___x_4856_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; 
v___x_4857_ = lean_box(1);
v___x_4858_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4859_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4860_, 0, v___x_4859_);
lean_ctor_set(v___x_4860_, 1, v___x_4858_);
lean_ctor_set(v___x_4860_, 2, v___x_4857_);
return v___x_4860_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4862_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_4863_ = l_Lean_stringToMessageData(v___x_4862_);
return v___x_4863_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___x_4865_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_4866_ = l_Lean_stringToMessageData(v___x_4865_);
return v___x_4866_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_4868_; lean_object* v___x_4869_; 
v___x_4868_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_4869_ = l_Lean_stringToMessageData(v___x_4868_);
return v___x_4869_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_4871_; lean_object* v___x_4872_; 
v___x_4871_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_4872_ = l_Lean_stringToMessageData(v___x_4871_);
return v___x_4872_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_4874_; lean_object* v___x_4875_; 
v___x_4874_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_4875_ = l_Lean_stringToMessageData(v___x_4874_);
return v___x_4875_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_4877_; lean_object* v___x_4878_; 
v___x_4877_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_4878_ = l_Lean_stringToMessageData(v___x_4877_);
return v___x_4878_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_4880_; lean_object* v___x_4881_; 
v___x_4880_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_4881_ = l_Lean_stringToMessageData(v___x_4880_);
return v___x_4881_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_4882_, lean_object* v_declHint_4883_, lean_object* v___y_4884_){
_start:
{
lean_object* v___x_4886_; lean_object* v_env_4887_; uint8_t v___x_4888_; 
v___x_4886_ = lean_st_ref_get(v___y_4884_);
v_env_4887_ = lean_ctor_get(v___x_4886_, 0);
lean_inc_ref(v_env_4887_);
lean_dec(v___x_4886_);
v___x_4888_ = l_Lean_Name_isAnonymous(v_declHint_4883_);
if (v___x_4888_ == 0)
{
uint8_t v_isExporting_4889_; 
v_isExporting_4889_ = lean_ctor_get_uint8(v_env_4887_, sizeof(void*)*8);
if (v_isExporting_4889_ == 0)
{
lean_object* v___x_4890_; 
lean_dec_ref(v_env_4887_);
lean_dec(v_declHint_4883_);
v___x_4890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4890_, 0, v_msg_4882_);
return v___x_4890_;
}
else
{
lean_object* v___x_4891_; uint8_t v___x_4892_; 
lean_inc_ref(v_env_4887_);
v___x_4891_ = l_Lean_Environment_setExporting(v_env_4887_, v___x_4888_);
lean_inc(v_declHint_4883_);
lean_inc_ref(v___x_4891_);
v___x_4892_ = l_Lean_Environment_contains(v___x_4891_, v_declHint_4883_, v_isExporting_4889_);
if (v___x_4892_ == 0)
{
lean_object* v___x_4893_; 
lean_dec_ref(v___x_4891_);
lean_dec_ref(v_env_4887_);
lean_dec(v_declHint_4883_);
v___x_4893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4893_, 0, v_msg_4882_);
return v___x_4893_;
}
else
{
lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v_c_4899_; lean_object* v___x_4900_; 
v___x_4894_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_4895_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_4896_ = l_Lean_Options_empty;
v___x_4897_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4897_, 0, v___x_4891_);
lean_ctor_set(v___x_4897_, 1, v___x_4894_);
lean_ctor_set(v___x_4897_, 2, v___x_4895_);
lean_ctor_set(v___x_4897_, 3, v___x_4896_);
lean_inc(v_declHint_4883_);
v___x_4898_ = l_Lean_MessageData_ofConstName(v_declHint_4883_, v___x_4888_);
v_c_4899_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4899_, 0, v___x_4897_);
lean_ctor_set(v_c_4899_, 1, v___x_4898_);
v___x_4900_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4887_, v_declHint_4883_);
if (lean_obj_tag(v___x_4900_) == 0)
{
lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; 
lean_dec_ref(v_env_4887_);
lean_dec(v_declHint_4883_);
v___x_4901_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_4902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4902_, 0, v___x_4901_);
lean_ctor_set(v___x_4902_, 1, v_c_4899_);
v___x_4903_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_4904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4902_);
lean_ctor_set(v___x_4904_, 1, v___x_4903_);
v___x_4905_ = l_Lean_MessageData_note(v___x_4904_);
v___x_4906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4906_, 0, v_msg_4882_);
lean_ctor_set(v___x_4906_, 1, v___x_4905_);
v___x_4907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4907_, 0, v___x_4906_);
return v___x_4907_;
}
else
{
lean_object* v_val_4908_; lean_object* v___x_4910_; uint8_t v_isShared_4911_; uint8_t v_isSharedCheck_4943_; 
v_val_4908_ = lean_ctor_get(v___x_4900_, 0);
v_isSharedCheck_4943_ = !lean_is_exclusive(v___x_4900_);
if (v_isSharedCheck_4943_ == 0)
{
v___x_4910_ = v___x_4900_;
v_isShared_4911_ = v_isSharedCheck_4943_;
goto v_resetjp_4909_;
}
else
{
lean_inc(v_val_4908_);
lean_dec(v___x_4900_);
v___x_4910_ = lean_box(0);
v_isShared_4911_ = v_isSharedCheck_4943_;
goto v_resetjp_4909_;
}
v_resetjp_4909_:
{
lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v_mod_4915_; uint8_t v___x_4916_; 
v___x_4912_ = lean_box(0);
v___x_4913_ = l_Lean_Environment_header(v_env_4887_);
lean_dec_ref(v_env_4887_);
v___x_4914_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4913_);
v_mod_4915_ = lean_array_get(v___x_4912_, v___x_4914_, v_val_4908_);
lean_dec(v_val_4908_);
lean_dec_ref(v___x_4914_);
v___x_4916_ = l_Lean_isPrivateName(v_declHint_4883_);
lean_dec(v_declHint_4883_);
if (v___x_4916_ == 0)
{
lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4928_; 
v___x_4917_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_4918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4918_, 0, v___x_4917_);
lean_ctor_set(v___x_4918_, 1, v_c_4899_);
v___x_4919_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_4920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4920_, 0, v___x_4918_);
lean_ctor_set(v___x_4920_, 1, v___x_4919_);
v___x_4921_ = l_Lean_MessageData_ofName(v_mod_4915_);
v___x_4922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4922_, 0, v___x_4920_);
lean_ctor_set(v___x_4922_, 1, v___x_4921_);
v___x_4923_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_4924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4924_, 0, v___x_4922_);
lean_ctor_set(v___x_4924_, 1, v___x_4923_);
v___x_4925_ = l_Lean_MessageData_note(v___x_4924_);
v___x_4926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4926_, 0, v_msg_4882_);
lean_ctor_set(v___x_4926_, 1, v___x_4925_);
if (v_isShared_4911_ == 0)
{
lean_ctor_set_tag(v___x_4910_, 0);
lean_ctor_set(v___x_4910_, 0, v___x_4926_);
v___x_4928_ = v___x_4910_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4929_; 
v_reuseFailAlloc_4929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4929_, 0, v___x_4926_);
v___x_4928_ = v_reuseFailAlloc_4929_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
return v___x_4928_;
}
}
else
{
lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4941_; 
v___x_4930_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_4931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4931_, 0, v___x_4930_);
lean_ctor_set(v___x_4931_, 1, v_c_4899_);
v___x_4932_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_4933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4933_, 0, v___x_4931_);
lean_ctor_set(v___x_4933_, 1, v___x_4932_);
v___x_4934_ = l_Lean_MessageData_ofName(v_mod_4915_);
v___x_4935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4935_, 0, v___x_4933_);
lean_ctor_set(v___x_4935_, 1, v___x_4934_);
v___x_4936_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_4937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4937_, 0, v___x_4935_);
lean_ctor_set(v___x_4937_, 1, v___x_4936_);
v___x_4938_ = l_Lean_MessageData_note(v___x_4937_);
v___x_4939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4939_, 0, v_msg_4882_);
lean_ctor_set(v___x_4939_, 1, v___x_4938_);
if (v_isShared_4911_ == 0)
{
lean_ctor_set_tag(v___x_4910_, 0);
lean_ctor_set(v___x_4910_, 0, v___x_4939_);
v___x_4941_ = v___x_4910_;
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
}
}
}
}
}
else
{
lean_object* v___x_4944_; 
lean_dec_ref(v_env_4887_);
lean_dec(v_declHint_4883_);
v___x_4944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4944_, 0, v_msg_4882_);
return v___x_4944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_4945_, lean_object* v_declHint_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_){
_start:
{
lean_object* v_res_4949_; 
v_res_4949_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_4945_, v_declHint_4946_, v___y_4947_);
lean_dec(v___y_4947_);
return v_res_4949_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_4950_, lean_object* v_declHint_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_){
_start:
{
lean_object* v___x_4957_; lean_object* v_a_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4967_; 
v___x_4957_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_4950_, v_declHint_4951_, v___y_4955_);
v_a_4958_ = lean_ctor_get(v___x_4957_, 0);
v_isSharedCheck_4967_ = !lean_is_exclusive(v___x_4957_);
if (v_isSharedCheck_4967_ == 0)
{
v___x_4960_ = v___x_4957_;
v_isShared_4961_ = v_isSharedCheck_4967_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_a_4958_);
lean_dec(v___x_4957_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4967_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4965_; 
v___x_4962_ = l_Lean_unknownIdentifierMessageTag;
v___x_4963_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4963_, 0, v___x_4962_);
lean_ctor_set(v___x_4963_, 1, v_a_4958_);
if (v_isShared_4961_ == 0)
{
lean_ctor_set(v___x_4960_, 0, v___x_4963_);
v___x_4965_ = v___x_4960_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_4968_, lean_object* v_declHint_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_){
_start:
{
lean_object* v_res_4975_; 
v_res_4975_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_4968_, v_declHint_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_);
lean_dec(v___y_4973_);
lean_dec_ref(v___y_4972_);
lean_dec(v___y_4971_);
lean_dec_ref(v___y_4970_);
return v_res_4975_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_4976_, lean_object* v_msg_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_){
_start:
{
lean_object* v_fileName_4983_; lean_object* v_fileMap_4984_; lean_object* v_options_4985_; lean_object* v_currRecDepth_4986_; lean_object* v_maxRecDepth_4987_; lean_object* v_ref_4988_; lean_object* v_currNamespace_4989_; lean_object* v_openDecls_4990_; lean_object* v_initHeartbeats_4991_; lean_object* v_maxHeartbeats_4992_; lean_object* v_quotContext_4993_; lean_object* v_currMacroScope_4994_; uint8_t v_diag_4995_; lean_object* v_cancelTk_x3f_4996_; uint8_t v_suppressElabErrors_4997_; lean_object* v_inheritedTraceOptions_4998_; lean_object* v_ref_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; 
v_fileName_4983_ = lean_ctor_get(v___y_4980_, 0);
v_fileMap_4984_ = lean_ctor_get(v___y_4980_, 1);
v_options_4985_ = lean_ctor_get(v___y_4980_, 2);
v_currRecDepth_4986_ = lean_ctor_get(v___y_4980_, 3);
v_maxRecDepth_4987_ = lean_ctor_get(v___y_4980_, 4);
v_ref_4988_ = lean_ctor_get(v___y_4980_, 5);
v_currNamespace_4989_ = lean_ctor_get(v___y_4980_, 6);
v_openDecls_4990_ = lean_ctor_get(v___y_4980_, 7);
v_initHeartbeats_4991_ = lean_ctor_get(v___y_4980_, 8);
v_maxHeartbeats_4992_ = lean_ctor_get(v___y_4980_, 9);
v_quotContext_4993_ = lean_ctor_get(v___y_4980_, 10);
v_currMacroScope_4994_ = lean_ctor_get(v___y_4980_, 11);
v_diag_4995_ = lean_ctor_get_uint8(v___y_4980_, sizeof(void*)*14);
v_cancelTk_x3f_4996_ = lean_ctor_get(v___y_4980_, 12);
v_suppressElabErrors_4997_ = lean_ctor_get_uint8(v___y_4980_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4998_ = lean_ctor_get(v___y_4980_, 13);
v_ref_4999_ = l_Lean_replaceRef(v_ref_4976_, v_ref_4988_);
lean_inc_ref(v_inheritedTraceOptions_4998_);
lean_inc(v_cancelTk_x3f_4996_);
lean_inc(v_currMacroScope_4994_);
lean_inc(v_quotContext_4993_);
lean_inc(v_maxHeartbeats_4992_);
lean_inc(v_initHeartbeats_4991_);
lean_inc(v_openDecls_4990_);
lean_inc(v_currNamespace_4989_);
lean_inc(v_maxRecDepth_4987_);
lean_inc(v_currRecDepth_4986_);
lean_inc_ref(v_options_4985_);
lean_inc_ref(v_fileMap_4984_);
lean_inc_ref(v_fileName_4983_);
v___x_5000_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5000_, 0, v_fileName_4983_);
lean_ctor_set(v___x_5000_, 1, v_fileMap_4984_);
lean_ctor_set(v___x_5000_, 2, v_options_4985_);
lean_ctor_set(v___x_5000_, 3, v_currRecDepth_4986_);
lean_ctor_set(v___x_5000_, 4, v_maxRecDepth_4987_);
lean_ctor_set(v___x_5000_, 5, v_ref_4999_);
lean_ctor_set(v___x_5000_, 6, v_currNamespace_4989_);
lean_ctor_set(v___x_5000_, 7, v_openDecls_4990_);
lean_ctor_set(v___x_5000_, 8, v_initHeartbeats_4991_);
lean_ctor_set(v___x_5000_, 9, v_maxHeartbeats_4992_);
lean_ctor_set(v___x_5000_, 10, v_quotContext_4993_);
lean_ctor_set(v___x_5000_, 11, v_currMacroScope_4994_);
lean_ctor_set(v___x_5000_, 12, v_cancelTk_x3f_4996_);
lean_ctor_set(v___x_5000_, 13, v_inheritedTraceOptions_4998_);
lean_ctor_set_uint8(v___x_5000_, sizeof(void*)*14, v_diag_4995_);
lean_ctor_set_uint8(v___x_5000_, sizeof(void*)*14 + 1, v_suppressElabErrors_4997_);
v___x_5001_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_4977_, v___y_4978_, v___y_4979_, v___x_5000_, v___y_4981_);
lean_dec_ref(v___x_5000_);
return v___x_5001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_5002_, lean_object* v_msg_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_){
_start:
{
lean_object* v_res_5009_; 
v_res_5009_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5002_, v_msg_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_);
lean_dec(v___y_5007_);
lean_dec_ref(v___y_5006_);
lean_dec(v___y_5005_);
lean_dec_ref(v___y_5004_);
lean_dec(v_ref_5002_);
return v_res_5009_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_5010_, lean_object* v_msg_5011_, lean_object* v_declHint_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_){
_start:
{
lean_object* v___x_5018_; lean_object* v_a_5019_; lean_object* v___x_5020_; 
v___x_5018_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5011_, v_declHint_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_);
v_a_5019_ = lean_ctor_get(v___x_5018_, 0);
lean_inc(v_a_5019_);
lean_dec_ref(v___x_5018_);
v___x_5020_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5010_, v_a_5019_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_);
return v___x_5020_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_5021_, lean_object* v_msg_5022_, lean_object* v_declHint_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_){
_start:
{
lean_object* v_res_5029_; 
v_res_5029_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5021_, v_msg_5022_, v_declHint_5023_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_);
lean_dec(v___y_5027_);
lean_dec_ref(v___y_5026_);
lean_dec(v___y_5025_);
lean_dec_ref(v___y_5024_);
lean_dec(v_ref_5021_);
return v_res_5029_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5031_; lean_object* v___x_5032_; 
v___x_5031_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_5032_ = l_Lean_stringToMessageData(v___x_5031_);
return v___x_5032_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_5033_, lean_object* v_constName_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_){
_start:
{
lean_object* v___x_5040_; uint8_t v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; 
v___x_5040_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_5041_ = 0;
lean_inc(v_constName_5034_);
v___x_5042_ = l_Lean_MessageData_ofConstName(v_constName_5034_, v___x_5041_);
v___x_5043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5043_, 0, v___x_5040_);
lean_ctor_set(v___x_5043_, 1, v___x_5042_);
v___x_5044_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5045_, 0, v___x_5043_);
lean_ctor_set(v___x_5045_, 1, v___x_5044_);
v___x_5046_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5033_, v___x_5045_, v_constName_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_);
return v___x_5046_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_5047_, lean_object* v_constName_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_){
_start:
{
lean_object* v_res_5054_; 
v_res_5054_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5047_, v_constName_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_);
lean_dec(v___y_5052_);
lean_dec_ref(v___y_5051_);
lean_dec(v___y_5050_);
lean_dec_ref(v___y_5049_);
lean_dec(v_ref_5047_);
return v_res_5054_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(lean_object* v_constName_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_){
_start:
{
lean_object* v_ref_5061_; lean_object* v___x_5062_; 
v_ref_5061_ = lean_ctor_get(v___y_5058_, 5);
v___x_5062_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5061_, v_constName_5055_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_);
return v___x_5062_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_){
_start:
{
lean_object* v_res_5069_; 
v_res_5069_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
lean_dec(v___y_5067_);
lean_dec_ref(v___y_5066_);
lean_dec(v___y_5065_);
lean_dec_ref(v___y_5064_);
return v_res_5069_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(lean_object* v_constName_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_){
_start:
{
lean_object* v___x_5076_; lean_object* v_env_5077_; uint8_t v___x_5078_; lean_object* v___x_5079_; 
v___x_5076_ = lean_st_ref_get(v___y_5074_);
v_env_5077_ = lean_ctor_get(v___x_5076_, 0);
lean_inc_ref(v_env_5077_);
lean_dec(v___x_5076_);
v___x_5078_ = 0;
lean_inc(v_constName_5070_);
v___x_5079_ = l_Lean_Environment_find_x3f(v_env_5077_, v_constName_5070_, v___x_5078_);
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_object* v___x_5080_; 
v___x_5080_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5070_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_);
return v___x_5080_;
}
else
{
lean_object* v_val_5081_; lean_object* v___x_5083_; uint8_t v_isShared_5084_; uint8_t v_isSharedCheck_5088_; 
lean_dec(v_constName_5070_);
v_val_5081_ = lean_ctor_get(v___x_5079_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5083_ = v___x_5079_;
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
else
{
lean_inc(v_val_5081_);
lean_dec(v___x_5079_);
v___x_5083_ = lean_box(0);
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
v_resetjp_5082_:
{
lean_object* v___x_5086_; 
if (v_isShared_5084_ == 0)
{
lean_ctor_set_tag(v___x_5083_, 0);
v___x_5086_ = v___x_5083_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v_val_5081_);
v___x_5086_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
return v___x_5086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0___boxed(lean_object* v_constName_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_){
_start:
{
lean_object* v_res_5095_; 
v_res_5095_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_constName_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_);
lean_dec(v___y_5093_);
lean_dec_ref(v___y_5092_);
lean_dec(v___y_5091_);
lean_dec_ref(v___y_5090_);
return v_res_5095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(lean_object* v_x_5098_, lean_object* v_x_5099_, lean_object* v_x_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_){
_start:
{
if (lean_obj_tag(v_x_5098_) == 5)
{
lean_object* v_fn_5106_; lean_object* v_arg_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; 
v_fn_5106_ = lean_ctor_get(v_x_5098_, 0);
lean_inc_ref(v_fn_5106_);
v_arg_5107_ = lean_ctor_get(v_x_5098_, 1);
lean_inc_ref(v_arg_5107_);
lean_dec_ref(v_x_5098_);
v___x_5108_ = lean_array_set(v_x_5099_, v_x_5100_, v_arg_5107_);
v___x_5109_ = lean_unsigned_to_nat(1u);
v___x_5110_ = lean_nat_sub(v_x_5100_, v___x_5109_);
lean_dec(v_x_5100_);
v_x_5098_ = v_fn_5106_;
v_x_5099_ = v___x_5108_;
v_x_5100_ = v___x_5110_;
goto _start;
}
else
{
lean_dec(v_x_5100_);
if (lean_obj_tag(v_x_5098_) == 4)
{
lean_object* v_declName_5112_; lean_object* v___x_5113_; 
v_declName_5112_ = lean_ctor_get(v_x_5098_, 0);
lean_inc(v_declName_5112_);
lean_dec_ref(v_x_5098_);
v___x_5113_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_declName_5112_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_);
if (lean_obj_tag(v___x_5113_) == 0)
{
lean_object* v_a_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5145_; 
v_a_5114_ = lean_ctor_get(v___x_5113_, 0);
v_isSharedCheck_5145_ = !lean_is_exclusive(v___x_5113_);
if (v_isSharedCheck_5145_ == 0)
{
v___x_5116_ = v___x_5113_;
v_isShared_5117_ = v_isSharedCheck_5145_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_a_5114_);
lean_dec(v___x_5113_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5145_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
lean_object* v_lower_5119_; lean_object* v_upper_5120_; 
if (lean_obj_tag(v_a_5114_) == 5)
{
lean_object* v_val_5128_; lean_object* v___x_5130_; uint8_t v_isShared_5131_; uint8_t v_isSharedCheck_5142_; 
v_val_5128_ = lean_ctor_get(v_a_5114_, 0);
v_isSharedCheck_5142_ = !lean_is_exclusive(v_a_5114_);
if (v_isSharedCheck_5142_ == 0)
{
v___x_5130_ = v_a_5114_;
v_isShared_5131_ = v_isSharedCheck_5142_;
goto v_resetjp_5129_;
}
else
{
lean_inc(v_val_5128_);
lean_dec(v_a_5114_);
v___x_5130_ = lean_box(0);
v_isShared_5131_ = v_isSharedCheck_5142_;
goto v_resetjp_5129_;
}
v_resetjp_5129_:
{
lean_object* v_numParams_5132_; lean_object* v_numIndices_5133_; lean_object* v___x_5134_; uint8_t v___x_5135_; 
v_numParams_5132_ = lean_ctor_get(v_val_5128_, 1);
lean_inc(v_numParams_5132_);
v_numIndices_5133_ = lean_ctor_get(v_val_5128_, 2);
lean_inc(v_numIndices_5133_);
lean_dec_ref(v_val_5128_);
v___x_5134_ = lean_unsigned_to_nat(0u);
v___x_5135_ = lean_nat_dec_eq(v_numIndices_5133_, v___x_5134_);
lean_dec(v_numIndices_5133_);
if (v___x_5135_ == 0)
{
lean_object* v___x_5136_; uint8_t v___x_5137_; 
lean_del_object(v___x_5130_);
v___x_5136_ = lean_array_get_size(v_x_5099_);
v___x_5137_ = lean_nat_dec_le(v_numParams_5132_, v___x_5134_);
if (v___x_5137_ == 0)
{
v_lower_5119_ = v_numParams_5132_;
v_upper_5120_ = v___x_5136_;
goto v___jp_5118_;
}
else
{
lean_dec(v_numParams_5132_);
v_lower_5119_ = v___x_5134_;
v_upper_5120_ = v___x_5136_;
goto v___jp_5118_;
}
}
else
{
lean_object* v___x_5138_; lean_object* v___x_5140_; 
lean_dec(v_numParams_5132_);
lean_del_object(v___x_5116_);
lean_dec_ref(v_x_5099_);
v___x_5138_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0));
if (v_isShared_5131_ == 0)
{
lean_ctor_set_tag(v___x_5130_, 0);
lean_ctor_set(v___x_5130_, 0, v___x_5138_);
v___x_5140_ = v___x_5130_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5141_; 
v_reuseFailAlloc_5141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5141_, 0, v___x_5138_);
v___x_5140_ = v_reuseFailAlloc_5141_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
return v___x_5140_;
}
}
}
}
else
{
lean_object* v___x_5143_; lean_object* v___x_5144_; 
lean_del_object(v___x_5116_);
lean_dec(v_a_5114_);
lean_dec_ref(v_x_5099_);
v___x_5143_ = lean_box(0);
v___x_5144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5144_, 0, v___x_5143_);
return v___x_5144_;
}
v___jp_5118_:
{
lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5126_; 
v___x_5121_ = l_Array_toSubarray___redArg(v_x_5099_, v_lower_5119_, v_upper_5120_);
v___x_5122_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5123_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5121_, v___x_5122_);
v___x_5124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5124_, 0, v___x_5123_);
if (v_isShared_5117_ == 0)
{
lean_ctor_set(v___x_5116_, 0, v___x_5124_);
v___x_5126_ = v___x_5116_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5127_; 
v_reuseFailAlloc_5127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5127_, 0, v___x_5124_);
v___x_5126_ = v_reuseFailAlloc_5127_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
return v___x_5126_;
}
}
}
}
else
{
lean_object* v_a_5146_; lean_object* v___x_5148_; uint8_t v_isShared_5149_; uint8_t v_isSharedCheck_5153_; 
lean_dec_ref(v_x_5099_);
v_a_5146_ = lean_ctor_get(v___x_5113_, 0);
v_isSharedCheck_5153_ = !lean_is_exclusive(v___x_5113_);
if (v_isSharedCheck_5153_ == 0)
{
v___x_5148_ = v___x_5113_;
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
else
{
lean_inc(v_a_5146_);
lean_dec(v___x_5113_);
v___x_5148_ = lean_box(0);
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
v_resetjp_5147_:
{
lean_object* v___x_5151_; 
if (v_isShared_5149_ == 0)
{
v___x_5151_ = v___x_5148_;
goto v_reusejp_5150_;
}
else
{
lean_object* v_reuseFailAlloc_5152_; 
v_reuseFailAlloc_5152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5152_, 0, v_a_5146_);
v___x_5151_ = v_reuseFailAlloc_5152_;
goto v_reusejp_5150_;
}
v_reusejp_5150_:
{
return v___x_5151_;
}
}
}
}
else
{
lean_object* v___x_5154_; lean_object* v___x_5155_; 
lean_dec_ref(v_x_5099_);
lean_dec_ref(v_x_5098_);
v___x_5154_ = lean_box(0);
v___x_5155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5155_, 0, v___x_5154_);
return v___x_5155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___boxed(lean_object* v_x_5156_, lean_object* v_x_5157_, lean_object* v_x_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_){
_start:
{
lean_object* v_res_5164_; 
v_res_5164_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_x_5156_, v_x_5157_, v_x_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5161_);
lean_dec(v___y_5160_);
lean_dec_ref(v___y_5159_);
return v_res_5164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f(lean_object* v_ctorApp_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_, lean_object* v_a_5169_){
_start:
{
lean_object* v___x_5171_; 
lean_inc(v_a_5169_);
lean_inc_ref(v_a_5168_);
lean_inc(v_a_5167_);
lean_inc_ref(v_a_5166_);
v___x_5171_ = lean_infer_type(v_ctorApp_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_);
if (lean_obj_tag(v___x_5171_) == 0)
{
lean_object* v_a_5172_; lean_object* v___x_5173_; 
v_a_5172_ = lean_ctor_get(v___x_5171_, 0);
lean_inc(v_a_5172_);
lean_dec_ref(v___x_5171_);
v___x_5173_ = l_Lean_Meta_whnfD(v_a_5172_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_);
if (lean_obj_tag(v___x_5173_) == 0)
{
lean_object* v_a_5174_; lean_object* v_dummy_5175_; lean_object* v_nargs_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; 
v_a_5174_ = lean_ctor_get(v___x_5173_, 0);
lean_inc(v_a_5174_);
lean_dec_ref(v___x_5173_);
v_dummy_5175_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_5176_ = l_Lean_Expr_getAppNumArgs(v_a_5174_);
lean_inc(v_nargs_5176_);
v___x_5177_ = lean_mk_array(v_nargs_5176_, v_dummy_5175_);
v___x_5178_ = lean_unsigned_to_nat(1u);
v___x_5179_ = lean_nat_sub(v_nargs_5176_, v___x_5178_);
lean_dec(v_nargs_5176_);
v___x_5180_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_a_5174_, v___x_5177_, v___x_5179_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_);
return v___x_5180_;
}
else
{
lean_object* v_a_5181_; lean_object* v___x_5183_; uint8_t v_isShared_5184_; uint8_t v_isSharedCheck_5188_; 
v_a_5181_ = lean_ctor_get(v___x_5173_, 0);
v_isSharedCheck_5188_ = !lean_is_exclusive(v___x_5173_);
if (v_isSharedCheck_5188_ == 0)
{
v___x_5183_ = v___x_5173_;
v_isShared_5184_ = v_isSharedCheck_5188_;
goto v_resetjp_5182_;
}
else
{
lean_inc(v_a_5181_);
lean_dec(v___x_5173_);
v___x_5183_ = lean_box(0);
v_isShared_5184_ = v_isSharedCheck_5188_;
goto v_resetjp_5182_;
}
v_resetjp_5182_:
{
lean_object* v___x_5186_; 
if (v_isShared_5184_ == 0)
{
v___x_5186_ = v___x_5183_;
goto v_reusejp_5185_;
}
else
{
lean_object* v_reuseFailAlloc_5187_; 
v_reuseFailAlloc_5187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5187_, 0, v_a_5181_);
v___x_5186_ = v_reuseFailAlloc_5187_;
goto v_reusejp_5185_;
}
v_reusejp_5185_:
{
return v___x_5186_;
}
}
}
}
else
{
lean_object* v_a_5189_; lean_object* v___x_5191_; uint8_t v_isShared_5192_; uint8_t v_isSharedCheck_5196_; 
v_a_5189_ = lean_ctor_get(v___x_5171_, 0);
v_isSharedCheck_5196_ = !lean_is_exclusive(v___x_5171_);
if (v_isSharedCheck_5196_ == 0)
{
v___x_5191_ = v___x_5171_;
v_isShared_5192_ = v_isSharedCheck_5196_;
goto v_resetjp_5190_;
}
else
{
lean_inc(v_a_5189_);
lean_dec(v___x_5171_);
v___x_5191_ = lean_box(0);
v_isShared_5192_ = v_isSharedCheck_5196_;
goto v_resetjp_5190_;
}
v_resetjp_5190_:
{
lean_object* v___x_5194_; 
if (v_isShared_5192_ == 0)
{
v___x_5194_ = v___x_5191_;
goto v_reusejp_5193_;
}
else
{
lean_object* v_reuseFailAlloc_5195_; 
v_reuseFailAlloc_5195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5195_, 0, v_a_5189_);
v___x_5194_ = v_reuseFailAlloc_5195_;
goto v_reusejp_5193_;
}
v_reusejp_5193_:
{
return v___x_5194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f___boxed(lean_object* v_ctorApp_5197_, lean_object* v_a_5198_, lean_object* v_a_5199_, lean_object* v_a_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_){
_start:
{
lean_object* v_res_5203_; 
v_res_5203_ = l_Lean_Meta_getCtorAppIndices_x3f(v_ctorApp_5197_, v_a_5198_, v_a_5199_, v_a_5200_, v_a_5201_);
lean_dec(v_a_5201_);
lean_dec_ref(v_a_5200_);
lean_dec(v_a_5199_);
lean_dec_ref(v_a_5198_);
return v_res_5203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1(lean_object* v_inst_5204_, lean_object* v_R_5205_, lean_object* v_a_5206_, lean_object* v_b_5207_){
_start:
{
lean_object* v___x_5208_; 
v___x_5208_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v_a_5206_, v_b_5207_);
return v___x_5208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(lean_object* v_00_u03b1_5209_, lean_object* v_constName_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_){
_start:
{
lean_object* v___x_5216_; 
v___x_5216_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_);
return v___x_5216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_5217_, lean_object* v_constName_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_){
_start:
{
lean_object* v_res_5224_; 
v_res_5224_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(v_00_u03b1_5217_, v_constName_5218_, v___y_5219_, v___y_5220_, v___y_5221_, v___y_5222_);
lean_dec(v___y_5222_);
lean_dec_ref(v___y_5221_);
lean_dec(v___y_5220_);
lean_dec_ref(v___y_5219_);
return v_res_5224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_5225_, lean_object* v_ref_5226_, lean_object* v_constName_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_){
_start:
{
lean_object* v___x_5233_; 
v___x_5233_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5226_, v_constName_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_);
return v___x_5233_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_5234_, lean_object* v_ref_5235_, lean_object* v_constName_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_){
_start:
{
lean_object* v_res_5242_; 
v_res_5242_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(v_00_u03b1_5234_, v_ref_5235_, v_constName_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_);
lean_dec(v___y_5240_);
lean_dec_ref(v___y_5239_);
lean_dec(v___y_5238_);
lean_dec_ref(v___y_5237_);
lean_dec(v_ref_5235_);
return v_res_5242_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_5243_, lean_object* v_ref_5244_, lean_object* v_msg_5245_, lean_object* v_declHint_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_){
_start:
{
lean_object* v___x_5252_; 
v___x_5252_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5244_, v_msg_5245_, v_declHint_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
return v___x_5252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_5253_, lean_object* v_ref_5254_, lean_object* v_msg_5255_, lean_object* v_declHint_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_){
_start:
{
lean_object* v_res_5262_; 
v_res_5262_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_5253_, v_ref_5254_, v_msg_5255_, v_declHint_5256_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_);
lean_dec(v___y_5260_);
lean_dec_ref(v___y_5259_);
lean_dec(v___y_5258_);
lean_dec_ref(v___y_5257_);
lean_dec(v_ref_5254_);
return v_res_5262_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_5263_, lean_object* v_declHint_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_){
_start:
{
lean_object* v___x_5270_; 
v___x_5270_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5263_, v_declHint_5264_, v___y_5268_);
return v___x_5270_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_5271_, lean_object* v_declHint_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_){
_start:
{
lean_object* v_res_5278_; 
v_res_5278_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_5271_, v_declHint_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_);
lean_dec(v___y_5276_);
lean_dec_ref(v___y_5275_);
lean_dec(v___y_5274_);
lean_dec_ref(v___y_5273_);
return v_res_5278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_5279_, lean_object* v_ref_5280_, lean_object* v_msg_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_){
_start:
{
lean_object* v___x_5287_; 
v___x_5287_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5280_, v_msg_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_);
return v___x_5287_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_5288_, lean_object* v_ref_5289_, lean_object* v_msg_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_){
_start:
{
lean_object* v_res_5296_; 
v_res_5296_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_5288_, v_ref_5289_, v_msg_5290_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_);
lean_dec(v___y_5294_);
lean_dec_ref(v___y_5293_);
lean_dec(v___y_5292_);
lean_dec_ref(v___y_5291_);
lean_dec(v_ref_5289_);
return v_res_5296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_5297_, lean_object* v_body_5298_, lean_object* v_args2_5299_, lean_object* v_ctorVal_5300_, lean_object* v_args1_5301_, lean_object* v_k_5302_, lean_object* v_arg2_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_){
_start:
{
lean_object* v_res_5309_; 
v_res_5309_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(v_i_5297_, v_body_5298_, v_args2_5299_, v_ctorVal_5300_, v_args1_5301_, v_k_5302_, v_arg2_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_);
lean_dec(v___y_5307_);
lean_dec_ref(v___y_5306_);
lean_dec(v___y_5305_);
lean_dec_ref(v___y_5304_);
lean_dec_ref(v_body_5298_);
lean_dec(v_i_5297_);
return v_res_5309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(lean_object* v_ctorVal_5310_, lean_object* v_args1_5311_, lean_object* v_k_5312_, lean_object* v_i_5313_, lean_object* v_type_5314_, lean_object* v_args2_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_){
_start:
{
lean_object* v___x_5321_; uint8_t v___x_5322_; 
v___x_5321_ = lean_array_get_size(v_args1_5311_);
v___x_5322_ = lean_nat_dec_lt(v_i_5313_, v___x_5321_);
if (v___x_5322_ == 0)
{
lean_object* v___x_5323_; 
lean_dec_ref(v_type_5314_);
lean_dec(v_i_5313_);
lean_dec_ref(v_args1_5311_);
lean_dec_ref(v_ctorVal_5310_);
lean_inc(v_a_5319_);
lean_inc_ref(v_a_5318_);
lean_inc(v_a_5317_);
lean_inc_ref(v_a_5316_);
v___x_5323_ = lean_apply_6(v_k_5312_, v_args2_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, lean_box(0));
return v___x_5323_;
}
else
{
lean_object* v___x_5324_; 
lean_inc(v_a_5319_);
lean_inc_ref(v_a_5318_);
lean_inc(v_a_5317_);
lean_inc_ref(v_a_5316_);
v___x_5324_ = lean_whnf(v_type_5314_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_);
if (lean_obj_tag(v___x_5324_) == 0)
{
lean_object* v_a_5325_; 
v_a_5325_ = lean_ctor_get(v___x_5324_, 0);
lean_inc(v_a_5325_);
lean_dec_ref(v___x_5324_);
if (lean_obj_tag(v_a_5325_) == 7)
{
lean_object* v_binderName_5326_; lean_object* v_binderType_5327_; lean_object* v_body_5328_; lean_object* v___f_5329_; uint8_t v___x_5330_; uint8_t v___x_5331_; lean_object* v___x_5332_; 
v_binderName_5326_ = lean_ctor_get(v_a_5325_, 0);
lean_inc(v_binderName_5326_);
v_binderType_5327_ = lean_ctor_get(v_a_5325_, 1);
lean_inc_ref(v_binderType_5327_);
v_body_5328_ = lean_ctor_get(v_a_5325_, 2);
lean_inc_ref(v_body_5328_);
lean_dec_ref(v_a_5325_);
v___f_5329_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5329_, 0, v_i_5313_);
lean_closure_set(v___f_5329_, 1, v_body_5328_);
lean_closure_set(v___f_5329_, 2, v_args2_5315_);
lean_closure_set(v___f_5329_, 3, v_ctorVal_5310_);
lean_closure_set(v___f_5329_, 4, v_args1_5311_);
lean_closure_set(v___f_5329_, 5, v_k_5312_);
v___x_5330_ = 1;
v___x_5331_ = 0;
v___x_5332_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_5326_, v___x_5330_, v_binderType_5327_, v___f_5329_, v___x_5331_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_);
return v___x_5332_;
}
else
{
lean_object* v_toConstantVal_5333_; lean_object* v_name_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; 
lean_dec(v_a_5325_);
lean_dec_ref(v_args2_5315_);
lean_dec(v_i_5313_);
lean_dec_ref(v_k_5312_);
lean_dec_ref(v_args1_5311_);
v_toConstantVal_5333_ = lean_ctor_get(v_ctorVal_5310_, 0);
lean_inc_ref(v_toConstantVal_5333_);
lean_dec_ref(v_ctorVal_5310_);
v_name_5334_ = lean_ctor_get(v_toConstantVal_5333_, 0);
lean_inc(v_name_5334_);
lean_dec_ref(v_toConstantVal_5333_);
v___x_5335_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_5336_ = l_Lean_MessageData_ofName(v_name_5334_);
v___x_5337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5337_, 0, v___x_5335_);
lean_ctor_set(v___x_5337_, 1, v___x_5336_);
v___x_5338_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5339_, 0, v___x_5337_);
lean_ctor_set(v___x_5339_, 1, v___x_5338_);
v___x_5340_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5339_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_);
return v___x_5340_;
}
}
else
{
lean_object* v_a_5341_; lean_object* v___x_5343_; uint8_t v_isShared_5344_; uint8_t v_isSharedCheck_5348_; 
lean_dec_ref(v_args2_5315_);
lean_dec(v_i_5313_);
lean_dec_ref(v_k_5312_);
lean_dec_ref(v_args1_5311_);
lean_dec_ref(v_ctorVal_5310_);
v_a_5341_ = lean_ctor_get(v___x_5324_, 0);
v_isSharedCheck_5348_ = !lean_is_exclusive(v___x_5324_);
if (v_isSharedCheck_5348_ == 0)
{
v___x_5343_ = v___x_5324_;
v_isShared_5344_ = v_isSharedCheck_5348_;
goto v_resetjp_5342_;
}
else
{
lean_inc(v_a_5341_);
lean_dec(v___x_5324_);
v___x_5343_ = lean_box(0);
v_isShared_5344_ = v_isSharedCheck_5348_;
goto v_resetjp_5342_;
}
v_resetjp_5342_:
{
lean_object* v___x_5346_; 
if (v_isShared_5344_ == 0)
{
v___x_5346_ = v___x_5343_;
goto v_reusejp_5345_;
}
else
{
lean_object* v_reuseFailAlloc_5347_; 
v_reuseFailAlloc_5347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5347_, 0, v_a_5341_);
v___x_5346_ = v_reuseFailAlloc_5347_;
goto v_reusejp_5345_;
}
v_reusejp_5345_:
{
return v___x_5346_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(lean_object* v_i_5349_, lean_object* v_body_5350_, lean_object* v_args2_5351_, lean_object* v_ctorVal_5352_, lean_object* v_args1_5353_, lean_object* v_k_5354_, lean_object* v_arg2_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_){
_start:
{
lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; 
v___x_5361_ = lean_unsigned_to_nat(1u);
v___x_5362_ = lean_nat_add(v_i_5349_, v___x_5361_);
v___x_5363_ = lean_expr_instantiate1(v_body_5350_, v_arg2_5355_);
v___x_5364_ = lean_array_push(v_args2_5351_, v_arg2_5355_);
v___x_5365_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5352_, v_args1_5353_, v_k_5354_, v___x_5362_, v___x_5363_, v___x_5364_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_);
return v___x_5365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed(lean_object* v_ctorVal_5366_, lean_object* v_args1_5367_, lean_object* v_k_5368_, lean_object* v_i_5369_, lean_object* v_type_5370_, lean_object* v_args2_5371_, lean_object* v_a_5372_, lean_object* v_a_5373_, lean_object* v_a_5374_, lean_object* v_a_5375_, lean_object* v_a_5376_){
_start:
{
lean_object* v_res_5377_; 
v_res_5377_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5366_, v_args1_5367_, v_k_5368_, v_i_5369_, v_type_5370_, v_args2_5371_, v_a_5372_, v_a_5373_, v_a_5374_, v_a_5375_);
lean_dec(v_a_5375_);
lean_dec_ref(v_a_5374_);
lean_dec(v_a_5373_);
lean_dec_ref(v_a_5372_);
return v_res_5377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(lean_object* v_name_5378_, lean_object* v_us_5379_, lean_object* v_args1_5380_, lean_object* v___x_5381_, lean_object* v_numParams_5382_, lean_object* v___x_5383_, lean_object* v_args2_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_){
_start:
{
lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; 
lean_inc(v_us_5379_);
v___x_5390_ = l_Lean_mkConst(v_name_5378_, v_us_5379_);
lean_inc_ref(v___x_5390_);
v___x_5391_ = l_Lean_mkAppN(v___x_5390_, v_args1_5380_);
v___x_5392_ = l_Lean_mkAppN(v___x_5390_, v_args2_5384_);
lean_inc_ref(v___x_5392_);
lean_inc_ref(v___x_5391_);
v___x_5393_ = l_Lean_Meta_mkEqHEq(v___x_5391_, v___x_5392_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_);
if (lean_obj_tag(v___x_5393_) == 0)
{
lean_object* v_a_5394_; lean_object* v___x_5395_; uint8_t v___x_5396_; lean_object* v___x_5397_; 
v_a_5394_ = lean_ctor_get(v___x_5393_, 0);
lean_inc(v_a_5394_);
lean_dec_ref(v___x_5393_);
lean_inc_ref_n(v_args2_5384_, 2);
v___x_5395_ = l_Array_toSubarray___redArg(v_args2_5384_, v___x_5381_, v_numParams_5382_);
v___x_5396_ = 1;
v___x_5397_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_5380_, v_args2_5384_, v___x_5396_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_);
if (lean_obj_tag(v___x_5397_) == 0)
{
lean_object* v_a_5398_; lean_object* v___x_5400_; uint8_t v_isShared_5401_; uint8_t v_isSharedCheck_5518_; 
v_a_5398_ = lean_ctor_get(v___x_5397_, 0);
v_isSharedCheck_5518_ = !lean_is_exclusive(v___x_5397_);
if (v_isSharedCheck_5518_ == 0)
{
v___x_5400_ = v___x_5397_;
v_isShared_5401_ = v_isSharedCheck_5518_;
goto v_resetjp_5399_;
}
else
{
lean_inc(v_a_5398_);
lean_dec(v___x_5397_);
v___x_5400_ = lean_box(0);
v_isShared_5401_ = v_isSharedCheck_5518_;
goto v_resetjp_5399_;
}
v_resetjp_5399_:
{
lean_object* v___x_5402_; 
v___x_5402_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_5398_);
if (lean_obj_tag(v___x_5402_) == 1)
{
lean_object* v_val_5403_; lean_object* v___x_5404_; 
lean_del_object(v___x_5400_);
v_val_5403_ = lean_ctor_get(v___x_5402_, 0);
lean_inc(v_val_5403_);
lean_dec_ref(v___x_5402_);
v___x_5404_ = l_Lean_mkArrow(v_a_5394_, v_val_5403_, v___y_5387_, v___y_5388_);
if (lean_obj_tag(v___x_5404_) == 0)
{
lean_object* v_a_5405_; lean_object* v___x_5406_; 
v_a_5405_ = lean_ctor_get(v___x_5404_, 0);
lean_inc(v_a_5405_);
lean_dec_ref(v___x_5404_);
v___x_5406_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5391_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_);
if (lean_obj_tag(v___x_5406_) == 0)
{
lean_object* v_a_5407_; lean_object* v___x_5409_; uint8_t v_isShared_5410_; uint8_t v_isSharedCheck_5497_; 
v_a_5407_ = lean_ctor_get(v___x_5406_, 0);
v_isSharedCheck_5497_ = !lean_is_exclusive(v___x_5406_);
if (v_isSharedCheck_5497_ == 0)
{
v___x_5409_ = v___x_5406_;
v_isShared_5410_ = v_isSharedCheck_5497_;
goto v_resetjp_5408_;
}
else
{
lean_inc(v_a_5407_);
lean_dec(v___x_5406_);
v___x_5409_ = lean_box(0);
v_isShared_5410_ = v_isSharedCheck_5497_;
goto v_resetjp_5408_;
}
v_resetjp_5408_:
{
if (lean_obj_tag(v_a_5407_) == 1)
{
lean_object* v_val_5411_; lean_object* v___x_5412_; 
lean_del_object(v___x_5409_);
v_val_5411_ = lean_ctor_get(v_a_5407_, 0);
lean_inc(v_val_5411_);
lean_dec_ref(v_a_5407_);
v___x_5412_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5392_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_);
if (lean_obj_tag(v___x_5412_) == 0)
{
lean_object* v_a_5413_; lean_object* v___x_5415_; uint8_t v_isShared_5416_; uint8_t v_isSharedCheck_5484_; 
v_a_5413_ = lean_ctor_get(v___x_5412_, 0);
v_isSharedCheck_5484_ = !lean_is_exclusive(v___x_5412_);
if (v_isSharedCheck_5484_ == 0)
{
v___x_5415_ = v___x_5412_;
v_isShared_5416_ = v_isSharedCheck_5484_;
goto v_resetjp_5414_;
}
else
{
lean_inc(v_a_5413_);
lean_dec(v___x_5412_);
v___x_5415_ = lean_box(0);
v_isShared_5416_ = v_isSharedCheck_5484_;
goto v_resetjp_5414_;
}
v_resetjp_5414_:
{
if (lean_obj_tag(v_a_5413_) == 1)
{
lean_object* v_val_5417_; lean_object* v___x_5419_; uint8_t v_isShared_5420_; uint8_t v_isSharedCheck_5479_; 
lean_del_object(v___x_5415_);
v_val_5417_ = lean_ctor_get(v_a_5413_, 0);
v_isSharedCheck_5479_ = !lean_is_exclusive(v_a_5413_);
if (v_isSharedCheck_5479_ == 0)
{
v___x_5419_ = v_a_5413_;
v_isShared_5420_ = v_isSharedCheck_5479_;
goto v_resetjp_5418_;
}
else
{
lean_inc(v_val_5417_);
lean_dec(v_a_5413_);
v___x_5419_ = lean_box(0);
v_isShared_5420_ = v_isSharedCheck_5479_;
goto v_resetjp_5418_;
}
v_resetjp_5418_:
{
lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; uint8_t v___x_5425_; lean_object* v___x_5426_; 
v___x_5421_ = l_Subarray_copy___redArg(v___x_5383_);
v___x_5422_ = l_Array_append___redArg(v___x_5421_, v_val_5411_);
v___x_5423_ = l_Subarray_copy___redArg(v___x_5395_);
v___x_5424_ = l_Array_append___redArg(v___x_5423_, v_val_5417_);
lean_dec(v_val_5417_);
v___x_5425_ = 0;
v___x_5426_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v___x_5422_, v___x_5424_, v___x_5425_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_);
lean_dec_ref(v___x_5422_);
if (lean_obj_tag(v___x_5426_) == 0)
{
lean_object* v_a_5427_; lean_object* v___x_5428_; 
v_a_5427_ = lean_ctor_get(v___x_5426_, 0);
lean_inc(v_a_5427_);
lean_dec_ref(v___x_5426_);
v___x_5428_ = l_Lean_mkArrowN(v_a_5427_, v_a_5405_, v___y_5387_, v___y_5388_);
lean_dec(v_a_5427_);
if (lean_obj_tag(v___x_5428_) == 0)
{
lean_object* v_a_5429_; uint8_t v___x_5430_; lean_object* v___x_5431_; 
v_a_5429_ = lean_ctor_get(v___x_5428_, 0);
lean_inc(v_a_5429_);
lean_dec_ref(v___x_5428_);
v___x_5430_ = 1;
v___x_5431_ = l_Lean_Meta_mkForallFVars(v_args2_5384_, v_a_5429_, v___x_5425_, v___x_5396_, v___x_5396_, v___x_5430_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_);
lean_dec_ref(v_args2_5384_);
if (lean_obj_tag(v___x_5431_) == 0)
{
lean_object* v_a_5432_; lean_object* v___x_5433_; 
v_a_5432_ = lean_ctor_get(v___x_5431_, 0);
lean_inc(v_a_5432_);
lean_dec_ref(v___x_5431_);
v___x_5433_ = l_Lean_Meta_mkForallFVars(v_args1_5380_, v_a_5432_, v___x_5425_, v___x_5396_, v___x_5396_, v___x_5430_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_);
if (lean_obj_tag(v___x_5433_) == 0)
{
lean_object* v_a_5434_; lean_object* v___x_5436_; uint8_t v_isShared_5437_; uint8_t v_isSharedCheck_5446_; 
v_a_5434_ = lean_ctor_get(v___x_5433_, 0);
v_isSharedCheck_5446_ = !lean_is_exclusive(v___x_5433_);
if (v_isSharedCheck_5446_ == 0)
{
v___x_5436_ = v___x_5433_;
v_isShared_5437_ = v_isSharedCheck_5446_;
goto v_resetjp_5435_;
}
else
{
lean_inc(v_a_5434_);
lean_dec(v___x_5433_);
v___x_5436_ = lean_box(0);
v_isShared_5437_ = v_isSharedCheck_5446_;
goto v_resetjp_5435_;
}
v_resetjp_5435_:
{
lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5441_; 
v___x_5438_ = lean_array_get_size(v_val_5411_);
lean_dec(v_val_5411_);
v___x_5439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5439_, 0, v_a_5434_);
lean_ctor_set(v___x_5439_, 1, v_us_5379_);
lean_ctor_set(v___x_5439_, 2, v___x_5438_);
if (v_isShared_5420_ == 0)
{
lean_ctor_set(v___x_5419_, 0, v___x_5439_);
v___x_5441_ = v___x_5419_;
goto v_reusejp_5440_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v___x_5439_);
v___x_5441_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5440_;
}
v_reusejp_5440_:
{
lean_object* v___x_5443_; 
if (v_isShared_5437_ == 0)
{
lean_ctor_set(v___x_5436_, 0, v___x_5441_);
v___x_5443_ = v___x_5436_;
goto v_reusejp_5442_;
}
else
{
lean_object* v_reuseFailAlloc_5444_; 
v_reuseFailAlloc_5444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5444_, 0, v___x_5441_);
v___x_5443_ = v_reuseFailAlloc_5444_;
goto v_reusejp_5442_;
}
v_reusejp_5442_:
{
return v___x_5443_;
}
}
}
}
else
{
lean_object* v_a_5447_; lean_object* v___x_5449_; uint8_t v_isShared_5450_; uint8_t v_isSharedCheck_5454_; 
lean_del_object(v___x_5419_);
lean_dec(v_val_5411_);
lean_dec(v_us_5379_);
v_a_5447_ = lean_ctor_get(v___x_5433_, 0);
v_isSharedCheck_5454_ = !lean_is_exclusive(v___x_5433_);
if (v_isSharedCheck_5454_ == 0)
{
v___x_5449_ = v___x_5433_;
v_isShared_5450_ = v_isSharedCheck_5454_;
goto v_resetjp_5448_;
}
else
{
lean_inc(v_a_5447_);
lean_dec(v___x_5433_);
v___x_5449_ = lean_box(0);
v_isShared_5450_ = v_isSharedCheck_5454_;
goto v_resetjp_5448_;
}
v_resetjp_5448_:
{
lean_object* v___x_5452_; 
if (v_isShared_5450_ == 0)
{
v___x_5452_ = v___x_5449_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5453_; 
v_reuseFailAlloc_5453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5453_, 0, v_a_5447_);
v___x_5452_ = v_reuseFailAlloc_5453_;
goto v_reusejp_5451_;
}
v_reusejp_5451_:
{
return v___x_5452_;
}
}
}
}
else
{
lean_object* v_a_5455_; lean_object* v___x_5457_; uint8_t v_isShared_5458_; uint8_t v_isSharedCheck_5462_; 
lean_del_object(v___x_5419_);
lean_dec(v_val_5411_);
lean_dec(v_us_5379_);
v_a_5455_ = lean_ctor_get(v___x_5431_, 0);
v_isSharedCheck_5462_ = !lean_is_exclusive(v___x_5431_);
if (v_isSharedCheck_5462_ == 0)
{
v___x_5457_ = v___x_5431_;
v_isShared_5458_ = v_isSharedCheck_5462_;
goto v_resetjp_5456_;
}
else
{
lean_inc(v_a_5455_);
lean_dec(v___x_5431_);
v___x_5457_ = lean_box(0);
v_isShared_5458_ = v_isSharedCheck_5462_;
goto v_resetjp_5456_;
}
v_resetjp_5456_:
{
lean_object* v___x_5460_; 
if (v_isShared_5458_ == 0)
{
v___x_5460_ = v___x_5457_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_a_5455_);
v___x_5460_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5459_;
}
v_reusejp_5459_:
{
return v___x_5460_;
}
}
}
}
else
{
lean_object* v_a_5463_; lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5470_; 
lean_del_object(v___x_5419_);
lean_dec(v_val_5411_);
lean_dec_ref(v_args2_5384_);
lean_dec(v_us_5379_);
v_a_5463_ = lean_ctor_get(v___x_5428_, 0);
v_isSharedCheck_5470_ = !lean_is_exclusive(v___x_5428_);
if (v_isSharedCheck_5470_ == 0)
{
v___x_5465_ = v___x_5428_;
v_isShared_5466_ = v_isSharedCheck_5470_;
goto v_resetjp_5464_;
}
else
{
lean_inc(v_a_5463_);
lean_dec(v___x_5428_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5470_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
lean_object* v___x_5468_; 
if (v_isShared_5466_ == 0)
{
v___x_5468_ = v___x_5465_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5469_; 
v_reuseFailAlloc_5469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5469_, 0, v_a_5463_);
v___x_5468_ = v_reuseFailAlloc_5469_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
return v___x_5468_;
}
}
}
}
else
{
lean_object* v_a_5471_; lean_object* v___x_5473_; uint8_t v_isShared_5474_; uint8_t v_isSharedCheck_5478_; 
lean_del_object(v___x_5419_);
lean_dec(v_val_5411_);
lean_dec(v_a_5405_);
lean_dec_ref(v_args2_5384_);
lean_dec(v_us_5379_);
v_a_5471_ = lean_ctor_get(v___x_5426_, 0);
v_isSharedCheck_5478_ = !lean_is_exclusive(v___x_5426_);
if (v_isSharedCheck_5478_ == 0)
{
v___x_5473_ = v___x_5426_;
v_isShared_5474_ = v_isSharedCheck_5478_;
goto v_resetjp_5472_;
}
else
{
lean_inc(v_a_5471_);
lean_dec(v___x_5426_);
v___x_5473_ = lean_box(0);
v_isShared_5474_ = v_isSharedCheck_5478_;
goto v_resetjp_5472_;
}
v_resetjp_5472_:
{
lean_object* v___x_5476_; 
if (v_isShared_5474_ == 0)
{
v___x_5476_ = v___x_5473_;
goto v_reusejp_5475_;
}
else
{
lean_object* v_reuseFailAlloc_5477_; 
v_reuseFailAlloc_5477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5477_, 0, v_a_5471_);
v___x_5476_ = v_reuseFailAlloc_5477_;
goto v_reusejp_5475_;
}
v_reusejp_5475_:
{
return v___x_5476_;
}
}
}
}
}
else
{
lean_object* v___x_5480_; lean_object* v___x_5482_; 
lean_dec(v_a_5413_);
lean_dec(v_val_5411_);
lean_dec(v_a_5405_);
lean_dec_ref(v___x_5395_);
lean_dec_ref(v_args2_5384_);
lean_dec_ref(v___x_5383_);
lean_dec(v_us_5379_);
v___x_5480_ = lean_box(0);
if (v_isShared_5416_ == 0)
{
lean_ctor_set(v___x_5415_, 0, v___x_5480_);
v___x_5482_ = v___x_5415_;
goto v_reusejp_5481_;
}
else
{
lean_object* v_reuseFailAlloc_5483_; 
v_reuseFailAlloc_5483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5483_, 0, v___x_5480_);
v___x_5482_ = v_reuseFailAlloc_5483_;
goto v_reusejp_5481_;
}
v_reusejp_5481_:
{
return v___x_5482_;
}
}
}
}
else
{
lean_object* v_a_5485_; lean_object* v___x_5487_; uint8_t v_isShared_5488_; uint8_t v_isSharedCheck_5492_; 
lean_dec(v_val_5411_);
lean_dec(v_a_5405_);
lean_dec_ref(v___x_5395_);
lean_dec_ref(v_args2_5384_);
lean_dec_ref(v___x_5383_);
lean_dec(v_us_5379_);
v_a_5485_ = lean_ctor_get(v___x_5412_, 0);
v_isSharedCheck_5492_ = !lean_is_exclusive(v___x_5412_);
if (v_isSharedCheck_5492_ == 0)
{
v___x_5487_ = v___x_5412_;
v_isShared_5488_ = v_isSharedCheck_5492_;
goto v_resetjp_5486_;
}
else
{
lean_inc(v_a_5485_);
lean_dec(v___x_5412_);
v___x_5487_ = lean_box(0);
v_isShared_5488_ = v_isSharedCheck_5492_;
goto v_resetjp_5486_;
}
v_resetjp_5486_:
{
lean_object* v___x_5490_; 
if (v_isShared_5488_ == 0)
{
v___x_5490_ = v___x_5487_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v_a_5485_);
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
lean_object* v___x_5493_; lean_object* v___x_5495_; 
lean_dec(v_a_5407_);
lean_dec(v_a_5405_);
lean_dec_ref(v___x_5395_);
lean_dec_ref(v___x_5392_);
lean_dec_ref(v_args2_5384_);
lean_dec_ref(v___x_5383_);
lean_dec(v_us_5379_);
v___x_5493_ = lean_box(0);
if (v_isShared_5410_ == 0)
{
lean_ctor_set(v___x_5409_, 0, v___x_5493_);
v___x_5495_ = v___x_5409_;
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
lean_dec(v_a_5405_);
lean_dec_ref(v___x_5395_);
lean_dec_ref(v___x_5392_);
lean_dec_ref(v_args2_5384_);
lean_dec_ref(v___x_5383_);
lean_dec(v_us_5379_);
v_a_5498_ = lean_ctor_get(v___x_5406_, 0);
v_isSharedCheck_5505_ = !lean_is_exclusive(v___x_5406_);
if (v_isSharedCheck_5505_ == 0)
{
v___x_5500_ = v___x_5406_;
v_isShared_5501_ = v_isSharedCheck_5505_;
goto v_resetjp_5499_;
}
else
{
lean_inc(v_a_5498_);
lean_dec(v___x_5406_);
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
lean_object* v_a_5506_; lean_object* v___x_5508_; uint8_t v_isShared_5509_; uint8_t v_isSharedCheck_5513_; 
lean_dec_ref(v___x_5395_);
lean_dec_ref(v___x_5392_);
lean_dec_ref(v___x_5391_);
lean_dec_ref(v_args2_5384_);
lean_dec_ref(v___x_5383_);
lean_dec(v_us_5379_);
v_a_5506_ = lean_ctor_get(v___x_5404_, 0);
v_isSharedCheck_5513_ = !lean_is_exclusive(v___x_5404_);
if (v_isSharedCheck_5513_ == 0)
{
v___x_5508_ = v___x_5404_;
v_isShared_5509_ = v_isSharedCheck_5513_;
goto v_resetjp_5507_;
}
else
{
lean_inc(v_a_5506_);
lean_dec(v___x_5404_);
v___x_5508_ = lean_box(0);
v_isShared_5509_ = v_isSharedCheck_5513_;
goto v_resetjp_5507_;
}
v_resetjp_5507_:
{
lean_object* v___x_5511_; 
if (v_isShared_5509_ == 0)
{
v___x_5511_ = v___x_5508_;
goto v_reusejp_5510_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v_a_5506_);
v___x_5511_ = v_reuseFailAlloc_5512_;
goto v_reusejp_5510_;
}
v_reusejp_5510_:
{
return v___x_5511_;
}
}
}
}
else
{
lean_object* v___x_5514_; lean_object* v___x_5516_; 
lean_dec(v___x_5402_);
lean_dec_ref(v___x_5395_);
lean_dec(v_a_5394_);
lean_dec_ref(v___x_5392_);
lean_dec_ref(v___x_5391_);
lean_dec_ref(v_args2_5384_);
lean_dec_ref(v___x_5383_);
lean_dec(v_us_5379_);
v___x_5514_ = lean_box(0);
if (v_isShared_5401_ == 0)
{
lean_ctor_set(v___x_5400_, 0, v___x_5514_);
v___x_5516_ = v___x_5400_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v___x_5514_);
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
lean_dec_ref(v___x_5395_);
lean_dec(v_a_5394_);
lean_dec_ref(v___x_5392_);
lean_dec_ref(v___x_5391_);
lean_dec_ref(v_args2_5384_);
lean_dec_ref(v___x_5383_);
lean_dec(v_us_5379_);
v_a_5519_ = lean_ctor_get(v___x_5397_, 0);
v_isSharedCheck_5526_ = !lean_is_exclusive(v___x_5397_);
if (v_isSharedCheck_5526_ == 0)
{
v___x_5521_ = v___x_5397_;
v_isShared_5522_ = v_isSharedCheck_5526_;
goto v_resetjp_5520_;
}
else
{
lean_inc(v_a_5519_);
lean_dec(v___x_5397_);
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
lean_object* v_a_5527_; lean_object* v___x_5529_; uint8_t v_isShared_5530_; uint8_t v_isSharedCheck_5534_; 
lean_dec_ref(v___x_5392_);
lean_dec_ref(v___x_5391_);
lean_dec_ref(v_args2_5384_);
lean_dec_ref(v___x_5383_);
lean_dec(v_numParams_5382_);
lean_dec(v___x_5381_);
lean_dec(v_us_5379_);
v_a_5527_ = lean_ctor_get(v___x_5393_, 0);
v_isSharedCheck_5534_ = !lean_is_exclusive(v___x_5393_);
if (v_isSharedCheck_5534_ == 0)
{
v___x_5529_ = v___x_5393_;
v_isShared_5530_ = v_isSharedCheck_5534_;
goto v_resetjp_5528_;
}
else
{
lean_inc(v_a_5527_);
lean_dec(v___x_5393_);
v___x_5529_ = lean_box(0);
v_isShared_5530_ = v_isSharedCheck_5534_;
goto v_resetjp_5528_;
}
v_resetjp_5528_:
{
lean_object* v___x_5532_; 
if (v_isShared_5530_ == 0)
{
v___x_5532_ = v___x_5529_;
goto v_reusejp_5531_;
}
else
{
lean_object* v_reuseFailAlloc_5533_; 
v_reuseFailAlloc_5533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5533_, 0, v_a_5527_);
v___x_5532_ = v_reuseFailAlloc_5533_;
goto v_reusejp_5531_;
}
v_reusejp_5531_:
{
return v___x_5532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed(lean_object* v_name_5535_, lean_object* v_us_5536_, lean_object* v_args1_5537_, lean_object* v___x_5538_, lean_object* v_numParams_5539_, lean_object* v___x_5540_, lean_object* v_args2_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_){
_start:
{
lean_object* v_res_5547_; 
v_res_5547_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(v_name_5535_, v_us_5536_, v_args1_5537_, v___x_5538_, v_numParams_5539_, v___x_5540_, v_args2_5541_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_);
lean_dec(v___y_5545_);
lean_dec_ref(v___y_5544_);
lean_dec(v___y_5543_);
lean_dec_ref(v___y_5542_);
lean_dec_ref(v_args1_5537_);
return v_res_5547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(lean_object* v_numParams_5548_, lean_object* v_name_5549_, lean_object* v_us_5550_, lean_object* v_ctorVal_5551_, lean_object* v_a_5552_, lean_object* v_args1_5553_, lean_object* v_x_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_, lean_object* v___y_5558_){
_start:
{
lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___f_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; 
v___x_5560_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5548_);
lean_inc_ref_n(v_args1_5553_, 3);
v___x_5561_ = l_Array_toSubarray___redArg(v_args1_5553_, v___x_5560_, v_numParams_5548_);
v___f_5562_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5562_, 0, v_name_5549_);
lean_closure_set(v___f_5562_, 1, v_us_5550_);
lean_closure_set(v___f_5562_, 2, v_args1_5553_);
lean_closure_set(v___f_5562_, 3, v___x_5560_);
lean_closure_set(v___f_5562_, 4, v_numParams_5548_);
lean_closure_set(v___f_5562_, 5, v___x_5561_);
v___x_5563_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5564_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed), 11, 6);
lean_closure_set(v___x_5564_, 0, v_ctorVal_5551_);
lean_closure_set(v___x_5564_, 1, v_args1_5553_);
lean_closure_set(v___x_5564_, 2, v___f_5562_);
lean_closure_set(v___x_5564_, 3, v___x_5560_);
lean_closure_set(v___x_5564_, 4, v_a_5552_);
lean_closure_set(v___x_5564_, 5, v___x_5563_);
v___x_5565_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_args1_5553_, v___x_5564_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_);
return v___x_5565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed(lean_object* v_numParams_5566_, lean_object* v_name_5567_, lean_object* v_us_5568_, lean_object* v_ctorVal_5569_, lean_object* v_a_5570_, lean_object* v_args1_5571_, lean_object* v_x_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_){
_start:
{
lean_object* v_res_5578_; 
v_res_5578_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(v_numParams_5566_, v_name_5567_, v_us_5568_, v_ctorVal_5569_, v_a_5570_, v_args1_5571_, v_x_5572_, v___y_5573_, v___y_5574_, v___y_5575_, v___y_5576_);
lean_dec(v___y_5576_);
lean_dec_ref(v___y_5575_);
lean_dec(v___y_5574_);
lean_dec_ref(v___y_5573_);
lean_dec_ref(v_x_5572_);
return v_res_5578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(lean_object* v_ctorVal_5579_, lean_object* v_a_5580_, lean_object* v_a_5581_, lean_object* v_a_5582_, lean_object* v_a_5583_){
_start:
{
lean_object* v_toConstantVal_5585_; lean_object* v_numParams_5586_; lean_object* v_name_5587_; lean_object* v_levelParams_5588_; lean_object* v_type_5589_; lean_object* v___x_5590_; 
v_toConstantVal_5585_ = lean_ctor_get(v_ctorVal_5579_, 0);
v_numParams_5586_ = lean_ctor_get(v_ctorVal_5579_, 3);
lean_inc(v_numParams_5586_);
v_name_5587_ = lean_ctor_get(v_toConstantVal_5585_, 0);
lean_inc(v_name_5587_);
v_levelParams_5588_ = lean_ctor_get(v_toConstantVal_5585_, 1);
v_type_5589_ = lean_ctor_get(v_toConstantVal_5585_, 2);
lean_inc_ref(v_type_5589_);
v___x_5590_ = l_Lean_Meta_elimOptParam(v_type_5589_, v_a_5582_, v_a_5583_);
if (lean_obj_tag(v___x_5590_) == 0)
{
lean_object* v_a_5591_; lean_object* v___x_5592_; lean_object* v_us_5593_; lean_object* v___f_5594_; uint8_t v___x_5595_; lean_object* v___x_5596_; 
v_a_5591_ = lean_ctor_get(v___x_5590_, 0);
lean_inc_n(v_a_5591_, 2);
lean_dec_ref(v___x_5590_);
v___x_5592_ = lean_box(0);
lean_inc(v_levelParams_5588_);
v_us_5593_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_5588_, v___x_5592_);
v___f_5594_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed), 12, 5);
lean_closure_set(v___f_5594_, 0, v_numParams_5586_);
lean_closure_set(v___f_5594_, 1, v_name_5587_);
lean_closure_set(v___f_5594_, 2, v_us_5593_);
lean_closure_set(v___f_5594_, 3, v_ctorVal_5579_);
lean_closure_set(v___f_5594_, 4, v_a_5591_);
v___x_5595_ = 0;
v___x_5596_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_a_5591_, v___f_5594_, v___x_5595_, v_a_5580_, v_a_5581_, v_a_5582_, v_a_5583_);
return v___x_5596_;
}
else
{
lean_object* v_a_5597_; lean_object* v___x_5599_; uint8_t v_isShared_5600_; uint8_t v_isSharedCheck_5604_; 
lean_dec(v_name_5587_);
lean_dec(v_numParams_5586_);
lean_dec_ref(v_ctorVal_5579_);
v_a_5597_ = lean_ctor_get(v___x_5590_, 0);
v_isSharedCheck_5604_ = !lean_is_exclusive(v___x_5590_);
if (v_isSharedCheck_5604_ == 0)
{
v___x_5599_ = v___x_5590_;
v_isShared_5600_ = v_isSharedCheck_5604_;
goto v_resetjp_5598_;
}
else
{
lean_inc(v_a_5597_);
lean_dec(v___x_5590_);
v___x_5599_ = lean_box(0);
v_isShared_5600_ = v_isSharedCheck_5604_;
goto v_resetjp_5598_;
}
v_resetjp_5598_:
{
lean_object* v___x_5602_; 
if (v_isShared_5600_ == 0)
{
v___x_5602_ = v___x_5599_;
goto v_reusejp_5601_;
}
else
{
lean_object* v_reuseFailAlloc_5603_; 
v_reuseFailAlloc_5603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5603_, 0, v_a_5597_);
v___x_5602_ = v_reuseFailAlloc_5603_;
goto v_reusejp_5601_;
}
v_reusejp_5601_:
{
return v___x_5602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___boxed(lean_object* v_ctorVal_5605_, lean_object* v_a_5606_, lean_object* v_a_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_, lean_object* v_a_5610_){
_start:
{
lean_object* v_res_5611_; 
v_res_5611_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5605_, v_a_5606_, v_a_5607_, v_a_5608_, v_a_5609_);
lean_dec(v_a_5609_);
lean_dec_ref(v_a_5608_);
lean_dec(v_a_5607_);
lean_dec_ref(v_a_5606_);
return v_res_5611_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1(void){
_start:
{
lean_object* v___x_5613_; lean_object* v___x_5614_; 
v___x_5613_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0));
v___x_5614_ = l_Lean_stringToMessageData(v___x_5613_);
return v___x_5614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(lean_object* v_ctorVal_5615_, lean_object* v_a_5616_, lean_object* v_a_5617_, lean_object* v_a_5618_, lean_object* v_a_5619_){
_start:
{
lean_object* v_toConstantVal_5621_; lean_object* v_name_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; 
v_toConstantVal_5621_ = lean_ctor_get(v_ctorVal_5615_, 0);
lean_inc_ref(v_toConstantVal_5621_);
lean_dec_ref(v_ctorVal_5615_);
v_name_5622_ = lean_ctor_get(v_toConstantVal_5621_, 0);
lean_inc(v_name_5622_);
lean_dec_ref(v_toConstantVal_5621_);
v___x_5623_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1);
v___x_5624_ = l_Lean_MessageData_ofName(v_name_5622_);
v___x_5625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5625_, 0, v___x_5623_);
lean_ctor_set(v___x_5625_, 1, v___x_5624_);
v___x_5626_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5627_, 0, v___x_5625_);
lean_ctor_set(v___x_5627_, 1, v___x_5626_);
v___x_5628_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5627_, v_a_5616_, v_a_5617_, v_a_5618_, v_a_5619_);
return v___x_5628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___boxed(lean_object* v_ctorVal_5629_, lean_object* v_a_5630_, lean_object* v_a_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_){
_start:
{
lean_object* v_res_5635_; 
v_res_5635_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5629_, v_a_5630_, v_a_5631_, v_a_5632_, v_a_5633_);
lean_dec(v_a_5633_);
lean_dec_ref(v_a_5632_);
lean_dec(v_a_5631_);
lean_dec_ref(v_a_5630_);
return v_res_5635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(lean_object* v_00_u03b1_5636_, lean_object* v_ctorVal_5637_, lean_object* v_a_5638_, lean_object* v_a_5639_, lean_object* v_a_5640_, lean_object* v_a_5641_){
_start:
{
lean_object* v___x_5643_; 
v___x_5643_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5637_, v_a_5638_, v_a_5639_, v_a_5640_, v_a_5641_);
return v___x_5643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___boxed(lean_object* v_00_u03b1_5644_, lean_object* v_ctorVal_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_){
_start:
{
lean_object* v_res_5651_; 
v_res_5651_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(v_00_u03b1_5644_, v_ctorVal_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_);
lean_dec(v_a_5649_);
lean_dec_ref(v_a_5648_);
lean_dec(v_a_5647_);
lean_dec_ref(v_a_5646_);
return v_res_5651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(lean_object* v_ctorVal_5657_, size_t v_sz_5658_, size_t v_i_5659_, lean_object* v_bs_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_){
_start:
{
uint8_t v___x_5666_; 
v___x_5666_ = lean_usize_dec_lt(v_i_5659_, v_sz_5658_);
if (v___x_5666_ == 0)
{
lean_object* v___x_5667_; 
lean_dec_ref(v_ctorVal_5657_);
v___x_5667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5667_, 0, v_bs_5660_);
return v___x_5667_;
}
else
{
lean_object* v_v_5668_; lean_object* v___x_5669_; 
v_v_5668_ = lean_array_uget_borrowed(v_bs_5660_, v_i_5659_);
lean_inc(v___y_5664_);
lean_inc_ref(v___y_5663_);
lean_inc(v___y_5662_);
lean_inc_ref(v___y_5661_);
lean_inc(v_v_5668_);
v___x_5669_ = lean_infer_type(v_v_5668_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_);
if (lean_obj_tag(v___x_5669_) == 0)
{
lean_object* v_a_5670_; lean_object* v___x_5671_; 
v_a_5670_ = lean_ctor_get(v___x_5669_, 0);
lean_inc(v_a_5670_);
lean_dec_ref(v___x_5669_);
v___x_5671_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_5670_, v___y_5662_);
if (lean_obj_tag(v___x_5671_) == 0)
{
lean_object* v_a_5672_; lean_object* v___x_5673_; lean_object* v_bs_x27_5674_; lean_object* v_a_5676_; lean_object* v___y_5682_; lean_object* v_lhs_5693_; lean_object* v_rhs_5694_; lean_object* v___x_5696_; uint8_t v___x_5697_; 
v_a_5672_ = lean_ctor_get(v___x_5671_, 0);
lean_inc(v_a_5672_);
lean_dec_ref(v___x_5671_);
v___x_5673_ = lean_unsigned_to_nat(0u);
v_bs_x27_5674_ = lean_array_uset(v_bs_5660_, v_i_5659_, v___x_5673_);
v___x_5696_ = l_Lean_Expr_cleanupAnnotations(v_a_5672_);
v___x_5697_ = l_Lean_Expr_isApp(v___x_5696_);
if (v___x_5697_ == 0)
{
lean_object* v___x_5698_; 
lean_dec_ref(v___x_5696_);
lean_inc_ref(v_ctorVal_5657_);
v___x_5698_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5657_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_);
v___y_5682_ = v___x_5698_;
goto v___jp_5681_;
}
else
{
lean_object* v_arg_5699_; lean_object* v___x_5700_; uint8_t v___x_5701_; 
v_arg_5699_ = lean_ctor_get(v___x_5696_, 1);
lean_inc_ref(v_arg_5699_);
v___x_5700_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5696_);
v___x_5701_ = l_Lean_Expr_isApp(v___x_5700_);
if (v___x_5701_ == 0)
{
lean_object* v___x_5702_; 
lean_dec_ref(v___x_5700_);
lean_dec_ref(v_arg_5699_);
lean_inc_ref(v_ctorVal_5657_);
v___x_5702_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5657_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_);
v___y_5682_ = v___x_5702_;
goto v___jp_5681_;
}
else
{
lean_object* v_arg_5703_; lean_object* v___x_5704_; uint8_t v___x_5705_; 
v_arg_5703_ = lean_ctor_get(v___x_5700_, 1);
lean_inc_ref(v_arg_5703_);
v___x_5704_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5700_);
v___x_5705_ = l_Lean_Expr_isApp(v___x_5704_);
if (v___x_5705_ == 0)
{
lean_object* v___x_5706_; 
lean_dec_ref(v___x_5704_);
lean_dec_ref(v_arg_5703_);
lean_dec_ref(v_arg_5699_);
lean_inc_ref(v_ctorVal_5657_);
v___x_5706_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5657_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_);
v___y_5682_ = v___x_5706_;
goto v___jp_5681_;
}
else
{
lean_object* v_arg_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; uint8_t v___x_5710_; 
v_arg_5707_ = lean_ctor_get(v___x_5704_, 1);
lean_inc_ref(v_arg_5707_);
v___x_5708_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5704_);
v___x_5709_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0));
v___x_5710_ = l_Lean_Expr_isConstOf(v___x_5708_, v___x_5709_);
if (v___x_5710_ == 0)
{
uint8_t v___x_5711_; 
lean_dec_ref(v_arg_5703_);
v___x_5711_ = l_Lean_Expr_isApp(v___x_5708_);
if (v___x_5711_ == 0)
{
lean_object* v___x_5712_; 
lean_dec_ref(v___x_5708_);
lean_dec_ref(v_arg_5707_);
lean_dec_ref(v_arg_5699_);
lean_inc_ref(v_ctorVal_5657_);
v___x_5712_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5657_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_);
v___y_5682_ = v___x_5712_;
goto v___jp_5681_;
}
else
{
lean_object* v___x_5713_; lean_object* v___x_5714_; uint8_t v___x_5715_; 
v___x_5713_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5708_);
v___x_5714_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2));
v___x_5715_ = l_Lean_Expr_isConstOf(v___x_5713_, v___x_5714_);
lean_dec_ref(v___x_5713_);
if (v___x_5715_ == 0)
{
lean_object* v___x_5716_; 
lean_dec_ref(v_arg_5707_);
lean_dec_ref(v_arg_5699_);
lean_inc_ref(v_ctorVal_5657_);
v___x_5716_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5657_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_);
v___y_5682_ = v___x_5716_;
goto v___jp_5681_;
}
else
{
v_lhs_5693_ = v_arg_5707_;
v_rhs_5694_ = v_arg_5699_;
goto v___jp_5692_;
}
}
}
else
{
lean_dec_ref(v___x_5708_);
lean_dec_ref(v_arg_5707_);
v_lhs_5693_ = v_arg_5703_;
v_rhs_5694_ = v_arg_5699_;
goto v___jp_5692_;
}
}
}
}
v___jp_5675_:
{
size_t v___x_5677_; size_t v___x_5678_; lean_object* v___x_5679_; 
v___x_5677_ = ((size_t)1ULL);
v___x_5678_ = lean_usize_add(v_i_5659_, v___x_5677_);
v___x_5679_ = lean_array_uset(v_bs_x27_5674_, v_i_5659_, v_a_5676_);
v_i_5659_ = v___x_5678_;
v_bs_5660_ = v___x_5679_;
goto _start;
}
v___jp_5681_:
{
if (lean_obj_tag(v___y_5682_) == 0)
{
lean_object* v_a_5683_; 
v_a_5683_ = lean_ctor_get(v___y_5682_, 0);
lean_inc(v_a_5683_);
lean_dec_ref(v___y_5682_);
v_a_5676_ = v_a_5683_;
goto v___jp_5675_;
}
else
{
lean_object* v_a_5684_; lean_object* v___x_5686_; uint8_t v_isShared_5687_; uint8_t v_isSharedCheck_5691_; 
lean_dec_ref(v_bs_x27_5674_);
lean_dec_ref(v_ctorVal_5657_);
v_a_5684_ = lean_ctor_get(v___y_5682_, 0);
v_isSharedCheck_5691_ = !lean_is_exclusive(v___y_5682_);
if (v_isSharedCheck_5691_ == 0)
{
v___x_5686_ = v___y_5682_;
v_isShared_5687_ = v_isSharedCheck_5691_;
goto v_resetjp_5685_;
}
else
{
lean_inc(v_a_5684_);
lean_dec(v___y_5682_);
v___x_5686_ = lean_box(0);
v_isShared_5687_ = v_isSharedCheck_5691_;
goto v_resetjp_5685_;
}
v_resetjp_5685_:
{
lean_object* v___x_5689_; 
if (v_isShared_5687_ == 0)
{
v___x_5689_ = v___x_5686_;
goto v_reusejp_5688_;
}
else
{
lean_object* v_reuseFailAlloc_5690_; 
v_reuseFailAlloc_5690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5690_, 0, v_a_5684_);
v___x_5689_ = v_reuseFailAlloc_5690_;
goto v_reusejp_5688_;
}
v_reusejp_5688_:
{
return v___x_5689_;
}
}
}
}
v___jp_5692_:
{
lean_object* v___x_5695_; 
v___x_5695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5695_, 0, v_lhs_5693_);
lean_ctor_set(v___x_5695_, 1, v_rhs_5694_);
v_a_5676_ = v___x_5695_;
goto v___jp_5675_;
}
}
else
{
lean_object* v_a_5717_; lean_object* v___x_5719_; uint8_t v_isShared_5720_; uint8_t v_isSharedCheck_5724_; 
lean_dec_ref(v_bs_5660_);
lean_dec_ref(v_ctorVal_5657_);
v_a_5717_ = lean_ctor_get(v___x_5671_, 0);
v_isSharedCheck_5724_ = !lean_is_exclusive(v___x_5671_);
if (v_isSharedCheck_5724_ == 0)
{
v___x_5719_ = v___x_5671_;
v_isShared_5720_ = v_isSharedCheck_5724_;
goto v_resetjp_5718_;
}
else
{
lean_inc(v_a_5717_);
lean_dec(v___x_5671_);
v___x_5719_ = lean_box(0);
v_isShared_5720_ = v_isSharedCheck_5724_;
goto v_resetjp_5718_;
}
v_resetjp_5718_:
{
lean_object* v___x_5722_; 
if (v_isShared_5720_ == 0)
{
v___x_5722_ = v___x_5719_;
goto v_reusejp_5721_;
}
else
{
lean_object* v_reuseFailAlloc_5723_; 
v_reuseFailAlloc_5723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5723_, 0, v_a_5717_);
v___x_5722_ = v_reuseFailAlloc_5723_;
goto v_reusejp_5721_;
}
v_reusejp_5721_:
{
return v___x_5722_;
}
}
}
}
else
{
lean_object* v_a_5725_; lean_object* v___x_5727_; uint8_t v_isShared_5728_; uint8_t v_isSharedCheck_5732_; 
lean_dec_ref(v_bs_5660_);
lean_dec_ref(v_ctorVal_5657_);
v_a_5725_ = lean_ctor_get(v___x_5669_, 0);
v_isSharedCheck_5732_ = !lean_is_exclusive(v___x_5669_);
if (v_isSharedCheck_5732_ == 0)
{
v___x_5727_ = v___x_5669_;
v_isShared_5728_ = v_isSharedCheck_5732_;
goto v_resetjp_5726_;
}
else
{
lean_inc(v_a_5725_);
lean_dec(v___x_5669_);
v___x_5727_ = lean_box(0);
v_isShared_5728_ = v_isSharedCheck_5732_;
goto v_resetjp_5726_;
}
v_resetjp_5726_:
{
lean_object* v___x_5730_; 
if (v_isShared_5728_ == 0)
{
v___x_5730_ = v___x_5727_;
goto v_reusejp_5729_;
}
else
{
lean_object* v_reuseFailAlloc_5731_; 
v_reuseFailAlloc_5731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5731_, 0, v_a_5725_);
v___x_5730_ = v_reuseFailAlloc_5731_;
goto v_reusejp_5729_;
}
v_reusejp_5729_:
{
return v___x_5730_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___boxed(lean_object* v_ctorVal_5733_, lean_object* v_sz_5734_, lean_object* v_i_5735_, lean_object* v_bs_5736_, lean_object* v___y_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_){
_start:
{
size_t v_sz_boxed_5742_; size_t v_i_boxed_5743_; lean_object* v_res_5744_; 
v_sz_boxed_5742_ = lean_unbox_usize(v_sz_5734_);
lean_dec(v_sz_5734_);
v_i_boxed_5743_ = lean_unbox_usize(v_i_5735_);
lean_dec(v_i_5735_);
v_res_5744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5733_, v_sz_boxed_5742_, v_i_boxed_5743_, v_bs_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_);
lean_dec(v___y_5740_);
lean_dec_ref(v___y_5739_);
lean_dec(v___y_5738_);
lean_dec_ref(v___y_5737_);
return v_res_5744_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5746_; lean_object* v___x_5747_; 
v___x_5746_ = lean_unsigned_to_nat(0u);
v___x_5747_ = l_Lean_Level_ofNat(v___x_5746_);
return v___x_5747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(lean_object* v_ctorVal_5748_, lean_object* v_us_5749_, lean_object* v_numIndices_5750_, lean_object* v_xs_5751_, lean_object* v_type_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_){
_start:
{
lean_object* v_toConstantVal_5758_; lean_object* v_induct_5759_; lean_object* v_numParams_5760_; lean_object* v___x_5761_; lean_object* v_noConfusionName_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v_noConfusion_5766_; lean_object* v_noConfusion_5767_; lean_object* v_lower_5769_; lean_object* v_upper_5770_; lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v_n_5881_; uint8_t v___x_5882_; 
v_toConstantVal_5758_ = lean_ctor_get(v_ctorVal_5748_, 0);
v_induct_5759_ = lean_ctor_get(v_ctorVal_5748_, 1);
v_numParams_5760_ = lean_ctor_get(v_ctorVal_5748_, 3);
v___x_5761_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0));
lean_inc(v_induct_5759_);
v_noConfusionName_5762_ = l_Lean_Name_str___override(v_induct_5759_, v___x_5761_);
v___x_5763_ = lean_unsigned_to_nat(0u);
v___x_5764_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1);
v___x_5765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5765_, 0, v___x_5764_);
lean_ctor_set(v___x_5765_, 1, v_us_5749_);
v_noConfusion_5766_ = l_Lean_mkConst(v_noConfusionName_5762_, v___x_5765_);
v_noConfusion_5767_ = l_Lean_Expr_app___override(v_noConfusion_5766_, v_type_5752_);
v___x_5877_ = lean_array_get_size(v_xs_5751_);
v___x_5878_ = lean_nat_sub(v___x_5877_, v_numParams_5760_);
v___x_5879_ = lean_nat_sub(v___x_5878_, v_numIndices_5750_);
lean_dec(v___x_5878_);
v___x_5880_ = lean_unsigned_to_nat(1u);
v_n_5881_ = lean_nat_sub(v___x_5879_, v___x_5880_);
lean_dec(v___x_5879_);
v___x_5882_ = lean_nat_dec_le(v_n_5881_, v___x_5763_);
if (v___x_5882_ == 0)
{
v_lower_5769_ = v_n_5881_;
v_upper_5770_ = v___x_5877_;
goto v___jp_5768_;
}
else
{
lean_dec(v_n_5881_);
v_lower_5769_ = v___x_5763_;
v_upper_5770_ = v___x_5877_;
goto v___jp_5768_;
}
v___jp_5768_:
{
lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v_eqs_5773_; size_t v_sz_5774_; size_t v___x_5775_; lean_object* v___x_5776_; 
lean_inc_ref(v_xs_5751_);
v___x_5771_ = l_Array_toSubarray___redArg(v_xs_5751_, v_lower_5769_, v_upper_5770_);
v___x_5772_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v_eqs_5773_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5771_, v___x_5772_);
v_sz_5774_ = lean_array_size(v_eqs_5773_);
v___x_5775_ = ((size_t)0ULL);
lean_inc_ref(v_eqs_5773_);
lean_inc_ref(v_ctorVal_5748_);
v___x_5776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5748_, v_sz_5774_, v___x_5775_, v_eqs_5773_, v___y_5753_, v___y_5754_, v___y_5755_, v___y_5756_);
if (lean_obj_tag(v___x_5776_) == 0)
{
lean_object* v_a_5777_; lean_object* v___x_5778_; lean_object* v_fst_5779_; lean_object* v_snd_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; 
v_a_5777_ = lean_ctor_get(v___x_5776_, 0);
lean_inc(v_a_5777_);
lean_dec_ref(v___x_5776_);
v___x_5778_ = l_Array_unzip___redArg(v_a_5777_);
lean_dec(v_a_5777_);
v_fst_5779_ = lean_ctor_get(v___x_5778_, 0);
lean_inc(v_fst_5779_);
v_snd_5780_ = lean_ctor_get(v___x_5778_, 1);
lean_inc(v_snd_5780_);
lean_dec_ref(v___x_5778_);
v___x_5781_ = l_Lean_mkAppN(v_noConfusion_5767_, v_fst_5779_);
lean_dec(v_fst_5779_);
v___x_5782_ = l_Lean_mkAppN(v___x_5781_, v_snd_5780_);
lean_dec(v_snd_5780_);
v___x_5783_ = l_Lean_mkAppN(v___x_5782_, v_eqs_5773_);
lean_dec_ref(v_eqs_5773_);
lean_inc(v___y_5756_);
lean_inc_ref(v___y_5755_);
lean_inc(v___y_5754_);
lean_inc_ref(v___y_5753_);
lean_inc_ref(v___x_5783_);
v___x_5784_ = lean_infer_type(v___x_5783_, v___y_5753_, v___y_5754_, v___y_5755_, v___y_5756_);
if (lean_obj_tag(v___x_5784_) == 0)
{
lean_object* v_a_5785_; lean_object* v___x_5786_; 
v_a_5785_ = lean_ctor_get(v___x_5784_, 0);
lean_inc(v_a_5785_);
lean_dec_ref(v___x_5784_);
lean_inc(v___y_5756_);
lean_inc_ref(v___y_5755_);
lean_inc(v___y_5754_);
lean_inc_ref(v___y_5753_);
v___x_5786_ = lean_whnf(v_a_5785_, v___y_5753_, v___y_5754_, v___y_5755_, v___y_5756_);
if (lean_obj_tag(v___x_5786_) == 0)
{
lean_object* v_a_5787_; 
v_a_5787_ = lean_ctor_get(v___x_5786_, 0);
lean_inc(v_a_5787_);
lean_dec_ref(v___x_5786_);
if (lean_obj_tag(v_a_5787_) == 7)
{
lean_object* v_binderType_5788_; lean_object* v___x_5789_; lean_object* v___x_5790_; 
lean_inc_ref(v_toConstantVal_5758_);
lean_dec_ref(v_ctorVal_5748_);
v_binderType_5788_ = lean_ctor_get(v_a_5787_, 1);
lean_inc_ref(v_binderType_5788_);
lean_dec_ref(v_a_5787_);
v___x_5789_ = lean_box(0);
v___x_5790_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_binderType_5788_, v___x_5789_, v___y_5753_, v___y_5754_, v___y_5755_, v___y_5756_);
if (lean_obj_tag(v___x_5790_) == 0)
{
lean_object* v_a_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; 
v_a_5791_ = lean_ctor_get(v___x_5790_, 0);
lean_inc(v_a_5791_);
lean_dec_ref(v___x_5790_);
v___x_5792_ = l_Lean_Expr_mvarId_x21(v_a_5791_);
v___x_5793_ = l_Lean_MVarId_intros(v___x_5792_, v___y_5753_, v___y_5754_, v___y_5755_, v___y_5756_);
if (lean_obj_tag(v___x_5793_) == 0)
{
lean_object* v_a_5794_; lean_object* v_snd_5795_; lean_object* v_name_5796_; lean_object* v___x_5797_; 
v_a_5794_ = lean_ctor_get(v___x_5793_, 0);
lean_inc(v_a_5794_);
lean_dec_ref(v___x_5793_);
v_snd_5795_ = lean_ctor_get(v_a_5794_, 1);
lean_inc(v_snd_5795_);
lean_dec(v_a_5794_);
v_name_5796_ = lean_ctor_get(v_toConstantVal_5758_, 0);
lean_inc(v_name_5796_);
lean_dec_ref(v_toConstantVal_5758_);
v___x_5797_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_snd_5795_, v_name_5796_, v___y_5753_, v___y_5754_, v___y_5755_, v___y_5756_);
if (lean_obj_tag(v___x_5797_) == 0)
{
lean_object* v___x_5798_; lean_object* v___x_5799_; lean_object* v_a_5800_; lean_object* v___x_5802_; uint8_t v_isShared_5803_; uint8_t v_isSharedCheck_5827_; 
lean_dec_ref(v___x_5797_);
v___x_5798_ = l_Lean_Expr_app___override(v___x_5783_, v_a_5791_);
v___x_5799_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v___x_5798_, v___y_5754_);
v_a_5800_ = lean_ctor_get(v___x_5799_, 0);
v_isSharedCheck_5827_ = !lean_is_exclusive(v___x_5799_);
if (v_isSharedCheck_5827_ == 0)
{
v___x_5802_ = v___x_5799_;
v_isShared_5803_ = v_isSharedCheck_5827_;
goto v_resetjp_5801_;
}
else
{
lean_inc(v_a_5800_);
lean_dec(v___x_5799_);
v___x_5802_ = lean_box(0);
v_isShared_5803_ = v_isSharedCheck_5827_;
goto v_resetjp_5801_;
}
v_resetjp_5801_:
{
uint8_t v___x_5804_; uint8_t v___x_5805_; uint8_t v___x_5806_; lean_object* v___x_5807_; 
v___x_5804_ = 0;
v___x_5805_ = 1;
v___x_5806_ = 1;
v___x_5807_ = l_Lean_Meta_mkLambdaFVars(v_xs_5751_, v_a_5800_, v___x_5804_, v___x_5805_, v___x_5804_, v___x_5805_, v___x_5806_, v___y_5753_, v___y_5754_, v___y_5755_, v___y_5756_);
lean_dec_ref(v_xs_5751_);
if (lean_obj_tag(v___x_5807_) == 0)
{
lean_object* v_a_5808_; lean_object* v___x_5810_; uint8_t v_isShared_5811_; uint8_t v_isSharedCheck_5818_; 
v_a_5808_ = lean_ctor_get(v___x_5807_, 0);
v_isSharedCheck_5818_ = !lean_is_exclusive(v___x_5807_);
if (v_isSharedCheck_5818_ == 0)
{
v___x_5810_ = v___x_5807_;
v_isShared_5811_ = v_isSharedCheck_5818_;
goto v_resetjp_5809_;
}
else
{
lean_inc(v_a_5808_);
lean_dec(v___x_5807_);
v___x_5810_ = lean_box(0);
v_isShared_5811_ = v_isSharedCheck_5818_;
goto v_resetjp_5809_;
}
v_resetjp_5809_:
{
lean_object* v___x_5813_; 
if (v_isShared_5803_ == 0)
{
lean_ctor_set_tag(v___x_5802_, 1);
lean_ctor_set(v___x_5802_, 0, v_a_5808_);
v___x_5813_ = v___x_5802_;
goto v_reusejp_5812_;
}
else
{
lean_object* v_reuseFailAlloc_5817_; 
v_reuseFailAlloc_5817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5817_, 0, v_a_5808_);
v___x_5813_ = v_reuseFailAlloc_5817_;
goto v_reusejp_5812_;
}
v_reusejp_5812_:
{
lean_object* v___x_5815_; 
if (v_isShared_5811_ == 0)
{
lean_ctor_set(v___x_5810_, 0, v___x_5813_);
v___x_5815_ = v___x_5810_;
goto v_reusejp_5814_;
}
else
{
lean_object* v_reuseFailAlloc_5816_; 
v_reuseFailAlloc_5816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5816_, 0, v___x_5813_);
v___x_5815_ = v_reuseFailAlloc_5816_;
goto v_reusejp_5814_;
}
v_reusejp_5814_:
{
return v___x_5815_;
}
}
}
}
else
{
lean_object* v_a_5819_; lean_object* v___x_5821_; uint8_t v_isShared_5822_; uint8_t v_isSharedCheck_5826_; 
lean_del_object(v___x_5802_);
v_a_5819_ = lean_ctor_get(v___x_5807_, 0);
v_isSharedCheck_5826_ = !lean_is_exclusive(v___x_5807_);
if (v_isSharedCheck_5826_ == 0)
{
v___x_5821_ = v___x_5807_;
v_isShared_5822_ = v_isSharedCheck_5826_;
goto v_resetjp_5820_;
}
else
{
lean_inc(v_a_5819_);
lean_dec(v___x_5807_);
v___x_5821_ = lean_box(0);
v_isShared_5822_ = v_isSharedCheck_5826_;
goto v_resetjp_5820_;
}
v_resetjp_5820_:
{
lean_object* v___x_5824_; 
if (v_isShared_5822_ == 0)
{
v___x_5824_ = v___x_5821_;
goto v_reusejp_5823_;
}
else
{
lean_object* v_reuseFailAlloc_5825_; 
v_reuseFailAlloc_5825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5825_, 0, v_a_5819_);
v___x_5824_ = v_reuseFailAlloc_5825_;
goto v_reusejp_5823_;
}
v_reusejp_5823_:
{
return v___x_5824_;
}
}
}
}
}
else
{
lean_object* v_a_5828_; lean_object* v___x_5830_; uint8_t v_isShared_5831_; uint8_t v_isSharedCheck_5835_; 
lean_dec(v_a_5791_);
lean_dec_ref(v___x_5783_);
lean_dec_ref(v_xs_5751_);
v_a_5828_ = lean_ctor_get(v___x_5797_, 0);
v_isSharedCheck_5835_ = !lean_is_exclusive(v___x_5797_);
if (v_isSharedCheck_5835_ == 0)
{
v___x_5830_ = v___x_5797_;
v_isShared_5831_ = v_isSharedCheck_5835_;
goto v_resetjp_5829_;
}
else
{
lean_inc(v_a_5828_);
lean_dec(v___x_5797_);
v___x_5830_ = lean_box(0);
v_isShared_5831_ = v_isSharedCheck_5835_;
goto v_resetjp_5829_;
}
v_resetjp_5829_:
{
lean_object* v___x_5833_; 
if (v_isShared_5831_ == 0)
{
v___x_5833_ = v___x_5830_;
goto v_reusejp_5832_;
}
else
{
lean_object* v_reuseFailAlloc_5834_; 
v_reuseFailAlloc_5834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5834_, 0, v_a_5828_);
v___x_5833_ = v_reuseFailAlloc_5834_;
goto v_reusejp_5832_;
}
v_reusejp_5832_:
{
return v___x_5833_;
}
}
}
}
else
{
lean_object* v_a_5836_; lean_object* v___x_5838_; uint8_t v_isShared_5839_; uint8_t v_isSharedCheck_5843_; 
lean_dec(v_a_5791_);
lean_dec_ref(v___x_5783_);
lean_dec_ref(v_toConstantVal_5758_);
lean_dec_ref(v_xs_5751_);
v_a_5836_ = lean_ctor_get(v___x_5793_, 0);
v_isSharedCheck_5843_ = !lean_is_exclusive(v___x_5793_);
if (v_isSharedCheck_5843_ == 0)
{
v___x_5838_ = v___x_5793_;
v_isShared_5839_ = v_isSharedCheck_5843_;
goto v_resetjp_5837_;
}
else
{
lean_inc(v_a_5836_);
lean_dec(v___x_5793_);
v___x_5838_ = lean_box(0);
v_isShared_5839_ = v_isSharedCheck_5843_;
goto v_resetjp_5837_;
}
v_resetjp_5837_:
{
lean_object* v___x_5841_; 
if (v_isShared_5839_ == 0)
{
v___x_5841_ = v___x_5838_;
goto v_reusejp_5840_;
}
else
{
lean_object* v_reuseFailAlloc_5842_; 
v_reuseFailAlloc_5842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5842_, 0, v_a_5836_);
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
lean_object* v_a_5844_; lean_object* v___x_5846_; uint8_t v_isShared_5847_; uint8_t v_isSharedCheck_5851_; 
lean_dec_ref(v___x_5783_);
lean_dec_ref(v_toConstantVal_5758_);
lean_dec_ref(v_xs_5751_);
v_a_5844_ = lean_ctor_get(v___x_5790_, 0);
v_isSharedCheck_5851_ = !lean_is_exclusive(v___x_5790_);
if (v_isSharedCheck_5851_ == 0)
{
v___x_5846_ = v___x_5790_;
v_isShared_5847_ = v_isSharedCheck_5851_;
goto v_resetjp_5845_;
}
else
{
lean_inc(v_a_5844_);
lean_dec(v___x_5790_);
v___x_5846_ = lean_box(0);
v_isShared_5847_ = v_isSharedCheck_5851_;
goto v_resetjp_5845_;
}
v_resetjp_5845_:
{
lean_object* v___x_5849_; 
if (v_isShared_5847_ == 0)
{
v___x_5849_ = v___x_5846_;
goto v_reusejp_5848_;
}
else
{
lean_object* v_reuseFailAlloc_5850_; 
v_reuseFailAlloc_5850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5850_, 0, v_a_5844_);
v___x_5849_ = v_reuseFailAlloc_5850_;
goto v_reusejp_5848_;
}
v_reusejp_5848_:
{
return v___x_5849_;
}
}
}
}
else
{
lean_object* v___x_5852_; 
lean_dec(v_a_5787_);
lean_dec_ref(v___x_5783_);
lean_dec_ref(v_xs_5751_);
v___x_5852_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5748_, v___y_5753_, v___y_5754_, v___y_5755_, v___y_5756_);
return v___x_5852_;
}
}
else
{
lean_object* v_a_5853_; lean_object* v___x_5855_; uint8_t v_isShared_5856_; uint8_t v_isSharedCheck_5860_; 
lean_dec_ref(v___x_5783_);
lean_dec_ref(v_xs_5751_);
lean_dec_ref(v_ctorVal_5748_);
v_a_5853_ = lean_ctor_get(v___x_5786_, 0);
v_isSharedCheck_5860_ = !lean_is_exclusive(v___x_5786_);
if (v_isSharedCheck_5860_ == 0)
{
v___x_5855_ = v___x_5786_;
v_isShared_5856_ = v_isSharedCheck_5860_;
goto v_resetjp_5854_;
}
else
{
lean_inc(v_a_5853_);
lean_dec(v___x_5786_);
v___x_5855_ = lean_box(0);
v_isShared_5856_ = v_isSharedCheck_5860_;
goto v_resetjp_5854_;
}
v_resetjp_5854_:
{
lean_object* v___x_5858_; 
if (v_isShared_5856_ == 0)
{
v___x_5858_ = v___x_5855_;
goto v_reusejp_5857_;
}
else
{
lean_object* v_reuseFailAlloc_5859_; 
v_reuseFailAlloc_5859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5859_, 0, v_a_5853_);
v___x_5858_ = v_reuseFailAlloc_5859_;
goto v_reusejp_5857_;
}
v_reusejp_5857_:
{
return v___x_5858_;
}
}
}
}
else
{
lean_object* v_a_5861_; lean_object* v___x_5863_; uint8_t v_isShared_5864_; uint8_t v_isSharedCheck_5868_; 
lean_dec_ref(v___x_5783_);
lean_dec_ref(v_xs_5751_);
lean_dec_ref(v_ctorVal_5748_);
v_a_5861_ = lean_ctor_get(v___x_5784_, 0);
v_isSharedCheck_5868_ = !lean_is_exclusive(v___x_5784_);
if (v_isSharedCheck_5868_ == 0)
{
v___x_5863_ = v___x_5784_;
v_isShared_5864_ = v_isSharedCheck_5868_;
goto v_resetjp_5862_;
}
else
{
lean_inc(v_a_5861_);
lean_dec(v___x_5784_);
v___x_5863_ = lean_box(0);
v_isShared_5864_ = v_isSharedCheck_5868_;
goto v_resetjp_5862_;
}
v_resetjp_5862_:
{
lean_object* v___x_5866_; 
if (v_isShared_5864_ == 0)
{
v___x_5866_ = v___x_5863_;
goto v_reusejp_5865_;
}
else
{
lean_object* v_reuseFailAlloc_5867_; 
v_reuseFailAlloc_5867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5867_, 0, v_a_5861_);
v___x_5866_ = v_reuseFailAlloc_5867_;
goto v_reusejp_5865_;
}
v_reusejp_5865_:
{
return v___x_5866_;
}
}
}
}
else
{
lean_object* v_a_5869_; lean_object* v___x_5871_; uint8_t v_isShared_5872_; uint8_t v_isSharedCheck_5876_; 
lean_dec_ref(v_eqs_5773_);
lean_dec_ref(v_noConfusion_5767_);
lean_dec_ref(v_xs_5751_);
lean_dec_ref(v_ctorVal_5748_);
v_a_5869_ = lean_ctor_get(v___x_5776_, 0);
v_isSharedCheck_5876_ = !lean_is_exclusive(v___x_5776_);
if (v_isSharedCheck_5876_ == 0)
{
v___x_5871_ = v___x_5776_;
v_isShared_5872_ = v_isSharedCheck_5876_;
goto v_resetjp_5870_;
}
else
{
lean_inc(v_a_5869_);
lean_dec(v___x_5776_);
v___x_5871_ = lean_box(0);
v_isShared_5872_ = v_isSharedCheck_5876_;
goto v_resetjp_5870_;
}
v_resetjp_5870_:
{
lean_object* v___x_5874_; 
if (v_isShared_5872_ == 0)
{
v___x_5874_ = v___x_5871_;
goto v_reusejp_5873_;
}
else
{
lean_object* v_reuseFailAlloc_5875_; 
v_reuseFailAlloc_5875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5875_, 0, v_a_5869_);
v___x_5874_ = v_reuseFailAlloc_5875_;
goto v_reusejp_5873_;
}
v_reusejp_5873_:
{
return v___x_5874_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed(lean_object* v_ctorVal_5883_, lean_object* v_us_5884_, lean_object* v_numIndices_5885_, lean_object* v_xs_5886_, lean_object* v_type_5887_, lean_object* v___y_5888_, lean_object* v___y_5889_, lean_object* v___y_5890_, lean_object* v___y_5891_, lean_object* v___y_5892_){
_start:
{
lean_object* v_res_5893_; 
v_res_5893_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(v_ctorVal_5883_, v_us_5884_, v_numIndices_5885_, v_xs_5886_, v_type_5887_, v___y_5888_, v___y_5889_, v___y_5890_, v___y_5891_);
lean_dec(v___y_5891_);
lean_dec_ref(v___y_5890_);
lean_dec(v___y_5889_);
lean_dec_ref(v___y_5888_);
lean_dec(v_numIndices_5885_);
return v_res_5893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(lean_object* v_ctorVal_5894_, lean_object* v_typeInfo_5895_, lean_object* v_a_5896_, lean_object* v_a_5897_, lean_object* v_a_5898_, lean_object* v_a_5899_){
_start:
{
lean_object* v_thmType_5901_; lean_object* v_us_5902_; lean_object* v_numIndices_5903_; lean_object* v___f_5904_; uint8_t v___x_5905_; lean_object* v___x_5906_; 
v_thmType_5901_ = lean_ctor_get(v_typeInfo_5895_, 0);
lean_inc_ref(v_thmType_5901_);
v_us_5902_ = lean_ctor_get(v_typeInfo_5895_, 1);
lean_inc(v_us_5902_);
v_numIndices_5903_ = lean_ctor_get(v_typeInfo_5895_, 2);
lean_inc(v_numIndices_5903_);
lean_dec_ref(v_typeInfo_5895_);
v___f_5904_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5904_, 0, v_ctorVal_5894_);
lean_closure_set(v___f_5904_, 1, v_us_5902_);
lean_closure_set(v___f_5904_, 2, v_numIndices_5903_);
v___x_5905_ = 0;
v___x_5906_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_thmType_5901_, v___f_5904_, v___x_5905_, v___x_5905_, v_a_5896_, v_a_5897_, v_a_5898_, v_a_5899_);
return v___x_5906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___boxed(lean_object* v_ctorVal_5907_, lean_object* v_typeInfo_5908_, lean_object* v_a_5909_, lean_object* v_a_5910_, lean_object* v_a_5911_, lean_object* v_a_5912_, lean_object* v_a_5913_){
_start:
{
lean_object* v_res_5914_; 
v_res_5914_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5907_, v_typeInfo_5908_, v_a_5909_, v_a_5910_, v_a_5911_, v_a_5912_);
lean_dec(v_a_5912_);
lean_dec_ref(v_a_5911_);
lean_dec(v_a_5910_);
lean_dec_ref(v_a_5909_);
return v_res_5914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHInjectiveTheoremNameFor(lean_object* v_ctorName_5917_){
_start:
{
lean_object* v___x_5918_; lean_object* v___x_5919_; 
v___x_5918_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_5919_ = l_Lean_Name_str___override(v_ctorName_5917_, v___x_5918_);
return v___x_5919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object* v_thmName_5920_, lean_object* v_ctorVal_5921_, lean_object* v_a_5922_, lean_object* v_a_5923_, lean_object* v_a_5924_, lean_object* v_a_5925_){
_start:
{
lean_object* v___x_5927_; 
lean_inc_ref(v_ctorVal_5921_);
v___x_5927_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5921_, v_a_5922_, v_a_5923_, v_a_5924_, v_a_5925_);
if (lean_obj_tag(v___x_5927_) == 0)
{
lean_object* v_a_5928_; lean_object* v___x_5930_; uint8_t v_isShared_5931_; uint8_t v_isSharedCheck_5989_; 
v_a_5928_ = lean_ctor_get(v___x_5927_, 0);
v_isSharedCheck_5989_ = !lean_is_exclusive(v___x_5927_);
if (v_isSharedCheck_5989_ == 0)
{
v___x_5930_ = v___x_5927_;
v_isShared_5931_ = v_isSharedCheck_5989_;
goto v_resetjp_5929_;
}
else
{
lean_inc(v_a_5928_);
lean_dec(v___x_5927_);
v___x_5930_ = lean_box(0);
v_isShared_5931_ = v_isSharedCheck_5989_;
goto v_resetjp_5929_;
}
v_resetjp_5929_:
{
if (lean_obj_tag(v_a_5928_) == 1)
{
lean_object* v_val_5932_; lean_object* v___x_5933_; 
lean_del_object(v___x_5930_);
v_val_5932_ = lean_ctor_get(v_a_5928_, 0);
lean_inc_n(v_val_5932_, 2);
lean_dec_ref(v_a_5928_);
lean_inc_ref(v_ctorVal_5921_);
v___x_5933_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5921_, v_val_5932_, v_a_5922_, v_a_5923_, v_a_5924_, v_a_5925_);
if (lean_obj_tag(v___x_5933_) == 0)
{
lean_object* v_a_5934_; lean_object* v___x_5936_; uint8_t v_isShared_5937_; uint8_t v_isSharedCheck_5976_; 
v_a_5934_ = lean_ctor_get(v___x_5933_, 0);
v_isSharedCheck_5976_ = !lean_is_exclusive(v___x_5933_);
if (v_isSharedCheck_5976_ == 0)
{
v___x_5936_ = v___x_5933_;
v_isShared_5937_ = v_isSharedCheck_5976_;
goto v_resetjp_5935_;
}
else
{
lean_inc(v_a_5934_);
lean_dec(v___x_5933_);
v___x_5936_ = lean_box(0);
v_isShared_5937_ = v_isSharedCheck_5976_;
goto v_resetjp_5935_;
}
v_resetjp_5935_:
{
if (lean_obj_tag(v_a_5934_) == 1)
{
lean_object* v_toConstantVal_5938_; lean_object* v_val_5939_; lean_object* v___x_5941_; uint8_t v_isShared_5942_; uint8_t v_isSharedCheck_5971_; 
v_toConstantVal_5938_ = lean_ctor_get(v_ctorVal_5921_, 0);
lean_inc_ref(v_toConstantVal_5938_);
lean_dec_ref(v_ctorVal_5921_);
v_val_5939_ = lean_ctor_get(v_a_5934_, 0);
v_isSharedCheck_5971_ = !lean_is_exclusive(v_a_5934_);
if (v_isSharedCheck_5971_ == 0)
{
v___x_5941_ = v_a_5934_;
v_isShared_5942_ = v_isSharedCheck_5971_;
goto v_resetjp_5940_;
}
else
{
lean_inc(v_val_5939_);
lean_dec(v_a_5934_);
v___x_5941_ = lean_box(0);
v_isShared_5942_ = v_isSharedCheck_5971_;
goto v_resetjp_5940_;
}
v_resetjp_5940_:
{
lean_object* v_levelParams_5943_; lean_object* v___x_5945_; uint8_t v_isShared_5946_; uint8_t v_isSharedCheck_5968_; 
v_levelParams_5943_ = lean_ctor_get(v_toConstantVal_5938_, 1);
v_isSharedCheck_5968_ = !lean_is_exclusive(v_toConstantVal_5938_);
if (v_isSharedCheck_5968_ == 0)
{
lean_object* v_unused_5969_; lean_object* v_unused_5970_; 
v_unused_5969_ = lean_ctor_get(v_toConstantVal_5938_, 2);
lean_dec(v_unused_5969_);
v_unused_5970_ = lean_ctor_get(v_toConstantVal_5938_, 0);
lean_dec(v_unused_5970_);
v___x_5945_ = v_toConstantVal_5938_;
v_isShared_5946_ = v_isSharedCheck_5968_;
goto v_resetjp_5944_;
}
else
{
lean_inc(v_levelParams_5943_);
lean_dec(v_toConstantVal_5938_);
v___x_5945_ = lean_box(0);
v_isShared_5946_ = v_isSharedCheck_5968_;
goto v_resetjp_5944_;
}
v_resetjp_5944_:
{
lean_object* v_thmType_5947_; lean_object* v___x_5949_; uint8_t v_isShared_5950_; uint8_t v_isSharedCheck_5965_; 
v_thmType_5947_ = lean_ctor_get(v_val_5932_, 0);
v_isSharedCheck_5965_ = !lean_is_exclusive(v_val_5932_);
if (v_isSharedCheck_5965_ == 0)
{
lean_object* v_unused_5966_; lean_object* v_unused_5967_; 
v_unused_5966_ = lean_ctor_get(v_val_5932_, 2);
lean_dec(v_unused_5966_);
v_unused_5967_ = lean_ctor_get(v_val_5932_, 1);
lean_dec(v_unused_5967_);
v___x_5949_ = v_val_5932_;
v_isShared_5950_ = v_isSharedCheck_5965_;
goto v_resetjp_5948_;
}
else
{
lean_inc(v_thmType_5947_);
lean_dec(v_val_5932_);
v___x_5949_ = lean_box(0);
v_isShared_5950_ = v_isSharedCheck_5965_;
goto v_resetjp_5948_;
}
v_resetjp_5948_:
{
lean_object* v___x_5952_; 
lean_inc(v_thmName_5920_);
if (v_isShared_5946_ == 0)
{
lean_ctor_set(v___x_5945_, 2, v_thmType_5947_);
lean_ctor_set(v___x_5945_, 0, v_thmName_5920_);
v___x_5952_ = v___x_5945_;
goto v_reusejp_5951_;
}
else
{
lean_object* v_reuseFailAlloc_5964_; 
v_reuseFailAlloc_5964_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5964_, 0, v_thmName_5920_);
lean_ctor_set(v_reuseFailAlloc_5964_, 1, v_levelParams_5943_);
lean_ctor_set(v_reuseFailAlloc_5964_, 2, v_thmType_5947_);
v___x_5952_ = v_reuseFailAlloc_5964_;
goto v_reusejp_5951_;
}
v_reusejp_5951_:
{
lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5956_; 
v___x_5953_ = lean_box(0);
v___x_5954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5954_, 0, v_thmName_5920_);
lean_ctor_set(v___x_5954_, 1, v___x_5953_);
if (v_isShared_5950_ == 0)
{
lean_ctor_set(v___x_5949_, 2, v___x_5954_);
lean_ctor_set(v___x_5949_, 1, v_val_5939_);
lean_ctor_set(v___x_5949_, 0, v___x_5952_);
v___x_5956_ = v___x_5949_;
goto v_reusejp_5955_;
}
else
{
lean_object* v_reuseFailAlloc_5963_; 
v_reuseFailAlloc_5963_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5963_, 0, v___x_5952_);
lean_ctor_set(v_reuseFailAlloc_5963_, 1, v_val_5939_);
lean_ctor_set(v_reuseFailAlloc_5963_, 2, v___x_5954_);
v___x_5956_ = v_reuseFailAlloc_5963_;
goto v_reusejp_5955_;
}
v_reusejp_5955_:
{
lean_object* v___x_5958_; 
if (v_isShared_5942_ == 0)
{
lean_ctor_set(v___x_5941_, 0, v___x_5956_);
v___x_5958_ = v___x_5941_;
goto v_reusejp_5957_;
}
else
{
lean_object* v_reuseFailAlloc_5962_; 
v_reuseFailAlloc_5962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5962_, 0, v___x_5956_);
v___x_5958_ = v_reuseFailAlloc_5962_;
goto v_reusejp_5957_;
}
v_reusejp_5957_:
{
lean_object* v___x_5960_; 
if (v_isShared_5937_ == 0)
{
lean_ctor_set(v___x_5936_, 0, v___x_5958_);
v___x_5960_ = v___x_5936_;
goto v_reusejp_5959_;
}
else
{
lean_object* v_reuseFailAlloc_5961_; 
v_reuseFailAlloc_5961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5961_, 0, v___x_5958_);
v___x_5960_ = v_reuseFailAlloc_5961_;
goto v_reusejp_5959_;
}
v_reusejp_5959_:
{
return v___x_5960_;
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
lean_object* v___x_5972_; lean_object* v___x_5974_; 
lean_dec(v_a_5934_);
lean_dec(v_val_5932_);
lean_dec_ref(v_ctorVal_5921_);
lean_dec(v_thmName_5920_);
v___x_5972_ = lean_box(0);
if (v_isShared_5937_ == 0)
{
lean_ctor_set(v___x_5936_, 0, v___x_5972_);
v___x_5974_ = v___x_5936_;
goto v_reusejp_5973_;
}
else
{
lean_object* v_reuseFailAlloc_5975_; 
v_reuseFailAlloc_5975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5975_, 0, v___x_5972_);
v___x_5974_ = v_reuseFailAlloc_5975_;
goto v_reusejp_5973_;
}
v_reusejp_5973_:
{
return v___x_5974_;
}
}
}
}
else
{
lean_object* v_a_5977_; lean_object* v___x_5979_; uint8_t v_isShared_5980_; uint8_t v_isSharedCheck_5984_; 
lean_dec(v_val_5932_);
lean_dec_ref(v_ctorVal_5921_);
lean_dec(v_thmName_5920_);
v_a_5977_ = lean_ctor_get(v___x_5933_, 0);
v_isSharedCheck_5984_ = !lean_is_exclusive(v___x_5933_);
if (v_isSharedCheck_5984_ == 0)
{
v___x_5979_ = v___x_5933_;
v_isShared_5980_ = v_isSharedCheck_5984_;
goto v_resetjp_5978_;
}
else
{
lean_inc(v_a_5977_);
lean_dec(v___x_5933_);
v___x_5979_ = lean_box(0);
v_isShared_5980_ = v_isSharedCheck_5984_;
goto v_resetjp_5978_;
}
v_resetjp_5978_:
{
lean_object* v___x_5982_; 
if (v_isShared_5980_ == 0)
{
v___x_5982_ = v___x_5979_;
goto v_reusejp_5981_;
}
else
{
lean_object* v_reuseFailAlloc_5983_; 
v_reuseFailAlloc_5983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5983_, 0, v_a_5977_);
v___x_5982_ = v_reuseFailAlloc_5983_;
goto v_reusejp_5981_;
}
v_reusejp_5981_:
{
return v___x_5982_;
}
}
}
}
else
{
lean_object* v___x_5985_; lean_object* v___x_5987_; 
lean_dec(v_a_5928_);
lean_dec_ref(v_ctorVal_5921_);
lean_dec(v_thmName_5920_);
v___x_5985_ = lean_box(0);
if (v_isShared_5931_ == 0)
{
lean_ctor_set(v___x_5930_, 0, v___x_5985_);
v___x_5987_ = v___x_5930_;
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
lean_dec_ref(v_ctorVal_5921_);
lean_dec(v_thmName_5920_);
v_a_5990_ = lean_ctor_get(v___x_5927_, 0);
v_isSharedCheck_5997_ = !lean_is_exclusive(v___x_5927_);
if (v_isSharedCheck_5997_ == 0)
{
v___x_5992_ = v___x_5927_;
v_isShared_5993_ = v_isSharedCheck_5997_;
goto v_resetjp_5991_;
}
else
{
lean_inc(v_a_5990_);
lean_dec(v___x_5927_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object* v_thmName_5998_, lean_object* v_ctorVal_5999_, lean_object* v_a_6000_, lean_object* v_a_6001_, lean_object* v_a_6002_, lean_object* v_a_6003_, lean_object* v_a_6004_){
_start:
{
lean_object* v_res_6005_; 
v_res_6005_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_thmName_5998_, v_ctorVal_5999_, v_a_6000_, v_a_6001_, v_a_6002_, v_a_6003_);
lean_dec(v_a_6003_);
lean_dec_ref(v_a_6002_);
lean_dec(v_a_6001_);
lean_dec_ref(v_a_6000_);
return v_res_6005_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(lean_object* v_env_6006_, lean_object* v_n_6007_){
_start:
{
if (lean_obj_tag(v_n_6007_) == 1)
{
lean_object* v_pre_6008_; lean_object* v_str_6009_; lean_object* v___x_6010_; uint8_t v___x_6011_; 
v_pre_6008_ = lean_ctor_get(v_n_6007_, 0);
lean_inc(v_pre_6008_);
v_str_6009_ = lean_ctor_get(v_n_6007_, 1);
lean_inc_ref(v_str_6009_);
lean_dec_ref(v_n_6007_);
v___x_6010_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6011_ = lean_string_dec_eq(v_str_6009_, v___x_6010_);
lean_dec_ref(v_str_6009_);
if (v___x_6011_ == 0)
{
lean_dec(v_pre_6008_);
lean_dec_ref(v_env_6006_);
return v___x_6011_;
}
else
{
uint8_t v___x_6012_; lean_object* v___x_6013_; 
v___x_6012_ = 0;
v___x_6013_ = l_Lean_Environment_find_x3f(v_env_6006_, v_pre_6008_, v___x_6012_);
if (lean_obj_tag(v___x_6013_) == 1)
{
lean_object* v_val_6014_; 
v_val_6014_ = lean_ctor_get(v___x_6013_, 0);
lean_inc(v_val_6014_);
lean_dec_ref(v___x_6013_);
if (lean_obj_tag(v_val_6014_) == 6)
{
lean_dec_ref(v_val_6014_);
return v___x_6011_;
}
else
{
lean_dec(v_val_6014_);
return v___x_6012_;
}
}
else
{
lean_dec(v___x_6013_);
return v___x_6012_;
}
}
}
else
{
uint8_t v___x_6015_; 
lean_dec(v_n_6007_);
lean_dec_ref(v_env_6006_);
v___x_6015_ = 0;
return v___x_6015_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_env_6016_, lean_object* v_n_6017_){
_start:
{
uint8_t v_res_6018_; lean_object* v_r_6019_; 
v_res_6018_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(v_env_6016_, v_n_6017_);
v_r_6019_ = lean_box(v_res_6018_);
return v_r_6019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6022_; lean_object* v___x_6023_; 
v___f_6022_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_));
v___x_6023_ = l_Lean_registerReservedNamePredicate(v___f_6022_);
return v___x_6023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_a_6024_){
_start:
{
lean_object* v_res_6025_; 
v_res_6025_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
return v_res_6025_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_thm_6026_, lean_object* v___y_6027_){
_start:
{
lean_object* v___x_6029_; lean_object* v_env_6030_; lean_object* v_toConstantVal_6031_; lean_object* v_value_6032_; lean_object* v_all_6033_; uint8_t v___y_6035_; lean_object* v_type_6043_; uint8_t v___x_6044_; 
v___x_6029_ = lean_st_ref_get(v___y_6027_);
v_env_6030_ = lean_ctor_get(v___x_6029_, 0);
lean_inc_ref_n(v_env_6030_, 2);
lean_dec(v___x_6029_);
v_toConstantVal_6031_ = lean_ctor_get(v_thm_6026_, 0);
v_value_6032_ = lean_ctor_get(v_thm_6026_, 1);
v_all_6033_ = lean_ctor_get(v_thm_6026_, 2);
v_type_6043_ = lean_ctor_get(v_toConstantVal_6031_, 2);
v___x_6044_ = l_Lean_Environment_hasUnsafe(v_env_6030_, v_type_6043_);
if (v___x_6044_ == 0)
{
uint8_t v___x_6045_; 
v___x_6045_ = l_Lean_Environment_hasUnsafe(v_env_6030_, v_value_6032_);
v___y_6035_ = v___x_6045_;
goto v___jp_6034_;
}
else
{
lean_dec_ref(v_env_6030_);
v___y_6035_ = v___x_6044_;
goto v___jp_6034_;
}
v___jp_6034_:
{
if (v___y_6035_ == 0)
{
lean_object* v___x_6036_; lean_object* v___x_6037_; 
v___x_6036_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6036_, 0, v_thm_6026_);
v___x_6037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6037_, 0, v___x_6036_);
return v___x_6037_;
}
else
{
lean_object* v___x_6038_; uint8_t v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; 
lean_inc(v_all_6033_);
lean_inc_ref(v_value_6032_);
lean_inc_ref(v_toConstantVal_6031_);
lean_dec_ref(v_thm_6026_);
v___x_6038_ = lean_box(0);
v___x_6039_ = 0;
v___x_6040_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6040_, 0, v_toConstantVal_6031_);
lean_ctor_set(v___x_6040_, 1, v_value_6032_);
lean_ctor_set(v___x_6040_, 2, v___x_6038_);
lean_ctor_set(v___x_6040_, 3, v_all_6033_);
lean_ctor_set_uint8(v___x_6040_, sizeof(void*)*4, v___x_6039_);
v___x_6041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6041_, 0, v___x_6040_);
v___x_6042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6042_, 0, v___x_6041_);
return v___x_6042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_thm_6046_, lean_object* v___y_6047_, lean_object* v___y_6048_){
_start:
{
lean_object* v_res_6049_; 
v_res_6049_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6046_, v___y_6047_);
lean_dec(v___y_6047_);
return v_res_6049_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(lean_object* v_thm_6050_, lean_object* v___y_6051_, lean_object* v___y_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_){
_start:
{
lean_object* v___x_6056_; 
v___x_6056_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6050_, v___y_6054_);
return v___x_6056_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_thm_6057_, lean_object* v___y_6058_, lean_object* v___y_6059_, lean_object* v___y_6060_, lean_object* v___y_6061_, lean_object* v___y_6062_){
_start:
{
lean_object* v_res_6063_; 
v_res_6063_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(v_thm_6057_, v___y_6058_, v___y_6059_, v___y_6060_, v___y_6061_);
lean_dec(v___y_6061_);
lean_dec_ref(v___y_6060_);
lean_dec(v___y_6059_);
lean_dec_ref(v___y_6058_);
return v_res_6063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v_val_6064_, uint8_t v___x_6065_, lean_object* v___y_6066_, lean_object* v___y_6067_, lean_object* v___y_6068_, lean_object* v___y_6069_){
_start:
{
lean_object* v___x_6071_; lean_object* v_a_6072_; lean_object* v___x_6073_; 
v___x_6071_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_val_6064_, v___y_6069_);
v_a_6072_ = lean_ctor_get(v___x_6071_, 0);
lean_inc(v_a_6072_);
lean_dec_ref(v___x_6071_);
v___x_6073_ = l_Lean_addDecl(v_a_6072_, v___x_6065_, v___y_6068_, v___y_6069_);
return v___x_6073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_val_6074_, lean_object* v___x_6075_, lean_object* v___y_6076_, lean_object* v___y_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_, lean_object* v___y_6080_){
_start:
{
uint8_t v___x_2122__boxed_6081_; lean_object* v_res_6082_; 
v___x_2122__boxed_6081_ = lean_unbox(v___x_6075_);
v_res_6082_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v_val_6074_, v___x_2122__boxed_6081_, v___y_6076_, v___y_6077_, v___y_6078_, v___y_6079_);
lean_dec(v___y_6079_);
lean_dec_ref(v___y_6078_);
lean_dec(v___y_6077_);
lean_dec_ref(v___y_6076_);
return v_res_6082_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; 
v___x_6085_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6086_ = lean_unsigned_to_nat(0u);
v___x_6087_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_6087_, 0, v___x_6086_);
lean_ctor_set(v___x_6087_, 1, v___x_6086_);
lean_ctor_set(v___x_6087_, 2, v___x_6086_);
lean_ctor_set(v___x_6087_, 3, v___x_6085_);
lean_ctor_set(v___x_6087_, 4, v___x_6085_);
lean_ctor_set(v___x_6087_, 5, v___x_6085_);
lean_ctor_set(v___x_6087_, 6, v___x_6085_);
lean_ctor_set(v___x_6087_, 7, v___x_6085_);
lean_ctor_set(v___x_6087_, 8, v___x_6085_);
return v___x_6087_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6088_; lean_object* v___x_6089_; 
v___x_6088_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6089_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6089_, 0, v___x_6088_);
lean_ctor_set(v___x_6089_, 1, v___x_6088_);
lean_ctor_set(v___x_6089_, 2, v___x_6088_);
lean_ctor_set(v___x_6089_, 3, v___x_6088_);
lean_ctor_set(v___x_6089_, 4, v___x_6088_);
lean_ctor_set(v___x_6089_, 5, v___x_6088_);
return v___x_6089_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6090_; lean_object* v___x_6091_; 
v___x_6090_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6091_, 0, v___x_6090_);
lean_ctor_set(v___x_6091_, 1, v___x_6090_);
lean_ctor_set(v___x_6091_, 2, v___x_6090_);
lean_ctor_set(v___x_6091_, 3, v___x_6090_);
lean_ctor_set(v___x_6091_, 4, v___x_6090_);
return v___x_6091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v___x_6092_, lean_object* v_name_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_){
_start:
{
if (lean_obj_tag(v_name_6093_) == 1)
{
lean_object* v_pre_6105_; lean_object* v_str_6106_; lean_object* v___x_6107_; uint8_t v___x_6108_; 
v_pre_6105_ = lean_ctor_get(v_name_6093_, 0);
lean_inc(v_pre_6105_);
v_str_6106_ = lean_ctor_get(v_name_6093_, 1);
v___x_6107_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6108_ = lean_string_dec_eq(v_str_6106_, v___x_6107_);
if (v___x_6108_ == 0)
{
lean_dec_ref(v_name_6093_);
lean_dec(v_pre_6105_);
lean_dec(v___x_6092_);
goto v___jp_6101_;
}
else
{
lean_object* v___x_6109_; lean_object* v_env_6110_; uint8_t v___x_6111_; lean_object* v___x_6112_; 
v___x_6109_ = lean_st_ref_get(v___y_6095_);
v_env_6110_ = lean_ctor_get(v___x_6109_, 0);
lean_inc_ref(v_env_6110_);
lean_dec(v___x_6109_);
v___x_6111_ = 0;
lean_inc(v_pre_6105_);
v___x_6112_ = l_Lean_Environment_find_x3f(v_env_6110_, v_pre_6105_, v___x_6111_);
if (lean_obj_tag(v___x_6112_) == 1)
{
lean_object* v_val_6113_; 
v_val_6113_ = lean_ctor_get(v___x_6112_, 0);
lean_inc(v_val_6113_);
lean_dec_ref(v___x_6112_);
if (lean_obj_tag(v_val_6113_) == 6)
{
lean_object* v_val_6114_; lean_object* v___x_6116_; uint8_t v_isShared_6117_; uint8_t v_isSharedCheck_6164_; 
v_val_6114_ = lean_ctor_get(v_val_6113_, 0);
v_isSharedCheck_6164_ = !lean_is_exclusive(v_val_6113_);
if (v_isSharedCheck_6164_ == 0)
{
v___x_6116_ = v_val_6113_;
v_isShared_6117_ = v_isSharedCheck_6164_;
goto v_resetjp_6115_;
}
else
{
lean_inc(v_val_6114_);
lean_dec(v_val_6113_);
v___x_6116_ = lean_box(0);
v_isShared_6117_ = v_isSharedCheck_6164_;
goto v_resetjp_6115_;
}
v_resetjp_6115_:
{
uint8_t v___x_6118_; uint8_t v___x_6119_; uint8_t v___x_6120_; lean_object* v___x_6121_; uint64_t v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; uint8_t v_a_6136_; lean_object* v___x_6142_; 
v___x_6118_ = 1;
v___x_6119_ = 0;
v___x_6120_ = 2;
v___x_6121_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_6121_, 0, v___x_6111_);
lean_ctor_set_uint8(v___x_6121_, 1, v___x_6111_);
lean_ctor_set_uint8(v___x_6121_, 2, v___x_6111_);
lean_ctor_set_uint8(v___x_6121_, 3, v___x_6111_);
lean_ctor_set_uint8(v___x_6121_, 4, v___x_6111_);
lean_ctor_set_uint8(v___x_6121_, 5, v___x_6108_);
lean_ctor_set_uint8(v___x_6121_, 6, v___x_6108_);
lean_ctor_set_uint8(v___x_6121_, 7, v___x_6111_);
lean_ctor_set_uint8(v___x_6121_, 8, v___x_6108_);
lean_ctor_set_uint8(v___x_6121_, 9, v___x_6118_);
lean_ctor_set_uint8(v___x_6121_, 10, v___x_6119_);
lean_ctor_set_uint8(v___x_6121_, 11, v___x_6108_);
lean_ctor_set_uint8(v___x_6121_, 12, v___x_6108_);
lean_ctor_set_uint8(v___x_6121_, 13, v___x_6108_);
lean_ctor_set_uint8(v___x_6121_, 14, v___x_6120_);
lean_ctor_set_uint8(v___x_6121_, 15, v___x_6108_);
lean_ctor_set_uint8(v___x_6121_, 16, v___x_6108_);
lean_ctor_set_uint8(v___x_6121_, 17, v___x_6108_);
lean_ctor_set_uint8(v___x_6121_, 18, v___x_6108_);
v___x_6122_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6121_);
v___x_6123_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_6123_, 0, v___x_6121_);
lean_ctor_set_uint64(v___x_6123_, sizeof(void*)*1, v___x_6122_);
v___x_6124_ = lean_unsigned_to_nat(0u);
v___x_6125_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_6126_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_6127_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6128_ = lean_box(0);
lean_inc(v___x_6092_);
v___x_6129_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6129_, 0, v___x_6123_);
lean_ctor_set(v___x_6129_, 1, v___x_6092_);
lean_ctor_set(v___x_6129_, 2, v___x_6126_);
lean_ctor_set(v___x_6129_, 3, v___x_6127_);
lean_ctor_set(v___x_6129_, 4, v___x_6128_);
lean_ctor_set(v___x_6129_, 5, v___x_6124_);
lean_ctor_set(v___x_6129_, 6, v___x_6128_);
lean_ctor_set_uint8(v___x_6129_, sizeof(void*)*7, v___x_6111_);
lean_ctor_set_uint8(v___x_6129_, sizeof(void*)*7 + 1, v___x_6111_);
lean_ctor_set_uint8(v___x_6129_, sizeof(void*)*7 + 2, v___x_6111_);
lean_ctor_set_uint8(v___x_6129_, sizeof(void*)*7 + 3, v___x_6108_);
v___x_6130_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6131_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6132_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6133_, 0, v___x_6130_);
lean_ctor_set(v___x_6133_, 1, v___x_6131_);
lean_ctor_set(v___x_6133_, 2, v___x_6092_);
lean_ctor_set(v___x_6133_, 3, v___x_6125_);
lean_ctor_set(v___x_6133_, 4, v___x_6132_);
v___x_6134_ = lean_st_mk_ref(v___x_6133_);
lean_inc_ref(v_name_6093_);
v___x_6142_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_name_6093_, v_val_6114_, v___x_6129_, v___x_6134_, v___y_6094_, v___y_6095_);
if (lean_obj_tag(v___x_6142_) == 0)
{
lean_object* v_a_6143_; 
v_a_6143_ = lean_ctor_get(v___x_6142_, 0);
lean_inc(v_a_6143_);
lean_dec_ref(v___x_6142_);
if (lean_obj_tag(v_a_6143_) == 1)
{
lean_object* v_val_6144_; lean_object* v___x_6145_; lean_object* v___f_6146_; lean_object* v___x_6147_; 
v_val_6144_ = lean_ctor_get(v_a_6143_, 0);
lean_inc(v_val_6144_);
lean_dec_ref(v_a_6143_);
v___x_6145_ = lean_box(v___x_6111_);
v___f_6146_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed), 7, 2);
lean_closure_set(v___f_6146_, 0, v_val_6144_);
lean_closure_set(v___f_6146_, 1, v___x_6145_);
v___x_6147_ = l_Lean_Meta_realizeConst(v_pre_6105_, v_name_6093_, v___f_6146_, v___x_6129_, v___x_6134_, v___y_6094_, v___y_6095_);
lean_dec_ref(v___x_6129_);
if (lean_obj_tag(v___x_6147_) == 0)
{
lean_dec_ref(v___x_6147_);
v_a_6136_ = v___x_6108_;
goto v___jp_6135_;
}
else
{
lean_object* v_a_6148_; lean_object* v___x_6150_; uint8_t v_isShared_6151_; uint8_t v_isSharedCheck_6155_; 
lean_dec(v___x_6134_);
lean_del_object(v___x_6116_);
v_a_6148_ = lean_ctor_get(v___x_6147_, 0);
v_isSharedCheck_6155_ = !lean_is_exclusive(v___x_6147_);
if (v_isSharedCheck_6155_ == 0)
{
v___x_6150_ = v___x_6147_;
v_isShared_6151_ = v_isSharedCheck_6155_;
goto v_resetjp_6149_;
}
else
{
lean_inc(v_a_6148_);
lean_dec(v___x_6147_);
v___x_6150_ = lean_box(0);
v_isShared_6151_ = v_isSharedCheck_6155_;
goto v_resetjp_6149_;
}
v_resetjp_6149_:
{
lean_object* v___x_6153_; 
if (v_isShared_6151_ == 0)
{
v___x_6153_ = v___x_6150_;
goto v_reusejp_6152_;
}
else
{
lean_object* v_reuseFailAlloc_6154_; 
v_reuseFailAlloc_6154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6154_, 0, v_a_6148_);
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
lean_dec(v_a_6143_);
lean_dec_ref(v___x_6129_);
lean_dec_ref(v_name_6093_);
lean_dec(v_pre_6105_);
v_a_6136_ = v___x_6111_;
goto v___jp_6135_;
}
}
else
{
lean_object* v_a_6156_; lean_object* v___x_6158_; uint8_t v_isShared_6159_; uint8_t v_isSharedCheck_6163_; 
lean_dec(v___x_6134_);
lean_dec_ref(v___x_6129_);
lean_del_object(v___x_6116_);
lean_dec_ref(v_name_6093_);
lean_dec(v_pre_6105_);
v_a_6156_ = lean_ctor_get(v___x_6142_, 0);
v_isSharedCheck_6163_ = !lean_is_exclusive(v___x_6142_);
if (v_isSharedCheck_6163_ == 0)
{
v___x_6158_ = v___x_6142_;
v_isShared_6159_ = v_isSharedCheck_6163_;
goto v_resetjp_6157_;
}
else
{
lean_inc(v_a_6156_);
lean_dec(v___x_6142_);
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
v___jp_6135_:
{
lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6140_; 
v___x_6137_ = lean_st_ref_get(v___x_6134_);
lean_dec(v___x_6134_);
lean_dec(v___x_6137_);
v___x_6138_ = lean_box(v_a_6136_);
if (v_isShared_6117_ == 0)
{
lean_ctor_set_tag(v___x_6116_, 0);
lean_ctor_set(v___x_6116_, 0, v___x_6138_);
v___x_6140_ = v___x_6116_;
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
lean_dec(v_val_6113_);
lean_dec_ref(v_name_6093_);
lean_dec(v_pre_6105_);
lean_dec(v___x_6092_);
goto v___jp_6097_;
}
}
else
{
lean_dec(v___x_6112_);
lean_dec_ref(v_name_6093_);
lean_dec(v_pre_6105_);
lean_dec(v___x_6092_);
goto v___jp_6097_;
}
}
}
else
{
lean_dec(v_name_6093_);
lean_dec(v___x_6092_);
goto v___jp_6101_;
}
v___jp_6097_:
{
uint8_t v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; 
v___x_6098_ = 0;
v___x_6099_ = lean_box(v___x_6098_);
v___x_6100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6100_, 0, v___x_6099_);
return v___x_6100_;
}
v___jp_6101_:
{
uint8_t v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; 
v___x_6102_ = 0;
v___x_6103_ = lean_box(v___x_6102_);
v___x_6104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6103_);
return v___x_6104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v___x_6165_, lean_object* v_name_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_){
_start:
{
lean_object* v_res_6170_; 
v_res_6170_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v___x_6165_, v_name_6166_, v___y_6167_, v___y_6168_);
lean_dec(v___y_6168_);
lean_dec_ref(v___y_6167_);
return v_res_6170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6174_; lean_object* v___x_6175_; 
v___f_6174_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6175_ = l_Lean_registerReservedNameAction(v___f_6174_);
return v___x_6175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_a_6176_){
_start:
{
lean_object* v_res_6177_; 
v_res_6177_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
return v_res_6177_;
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
