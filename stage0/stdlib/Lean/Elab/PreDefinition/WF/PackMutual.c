// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.PackMutual
// Imports: public import Lean.Meta.ArgsPacker public import Lean.Elab.PreDefinition.WF.Eqns
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
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_pack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_uncurryType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAsAxiom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_uncurry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_curryProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
lean_object* l_Lean_Meta_ArgsPacker_numFuncs(lean_object*);
uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object*);
uint8_t l_Lean_Meta_ArgsPacker_onlyOneUnary(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_withAppN___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Failed to eta-expand partial application"};
static const lean_object* l_Lean_Elab_WF_withAppN___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_WF_withAppN___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_WF_withAppN___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_withAppN___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_WF_withAppN___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_withAppN___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0 = (const lean_object*)&l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_packCalls_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_packCalls_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_WF_packCalls___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_WF_packCalls___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_WF_packCalls___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_packCalls___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Elab.PreDefinition.WF.PackMutual"};
static const lean_object* l_Lean_Elab_WF_packCalls___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_WF_packCalls___lam__2___closed__0_value;
static const lean_string_object l_Lean_Elab_WF_packCalls___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Elab.WF.packCalls"};
static const lean_object* l_Lean_Elab_WF_packCalls___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_WF_packCalls___lam__2___closed__1_value;
static const lean_string_object l_Lean_Elab_WF_packCalls___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "assertion violation: fidx < fixedParamPerms.perms.size\n      "};
static const lean_object* l_Lean_Elab_WF_packCalls___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_WF_packCalls___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_Elab_WF_packCalls___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_packCalls___lam__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0 = (const lean_object*)&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0_value;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_WF_packCalls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_WF_packCalls___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_WF_packCalls___closed__0 = (const lean_object*)&l_Lean_Elab_WF_packCalls___closed__0_value;
static lean_once_cell_t l_Lean_Elab_WF_packCalls___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_packCalls___closed__1;
static const lean_string_object l_Lean_Elab_WF_packCalls___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Not a forall: "};
static const lean_object* l_Lean_Elab_WF_packCalls___closed__2 = (const lean_object*)&l_Lean_Elab_WF_packCalls___closed__2_value;
static lean_once_cell_t l_Lean_Elab_WF_packCalls___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_packCalls___closed__3;
static const lean_string_object l_Lean_Elab_WF_packCalls___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_Elab_WF_packCalls___closed__4 = (const lean_object*)&l_Lean_Elab_WF_packCalls___closed__4_value;
static lean_once_cell_t l_Lean_Elab_WF_packCalls___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_packCalls___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_mutualName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_unary"};
static const lean_object* l_Lean_Elab_WF_mutualName___closed__0 = (const lean_object*)&l_Lean_Elab_WF_mutualName___closed__0_value;
static const lean_ctor_object l_Lean_Elab_WF_mutualName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_mutualName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 103, 179, 87, 16, 42, 175, 175)}};
static const lean_object* l_Lean_Elab_WF_mutualName___closed__1 = (const lean_object*)&l_Lean_Elab_WF_mutualName___closed__1_value;
static const lean_string_object l_Lean_Elab_WF_mutualName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_mutual"};
static const lean_object* l_Lean_Elab_WF_mutualName___closed__2 = (const lean_object*)&l_Lean_Elab_WF_mutualName___closed__2_value;
static const lean_ctor_object l_Lean_Elab_WF_mutualName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_mutualName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(60, 96, 167, 116, 153, 200, 47, 59)}};
static const lean_object* l_Lean_Elab_WF_mutualName___closed__3 = (const lean_object*)&l_Lean_Elab_WF_mutualName___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Elab.WF.varyingVarNames"};
static const lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "assertion violation: xs.size = arity\n    "};
static const lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2;
static const lean_string_object l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "assertion violation: fixedParamPerms.perms[preDefIdx]!.size = arity\n    "};
static const lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3_value;
static lean_once_cell_t l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4;
static const lean_array_object l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_WF_varyingVarNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_WF_varyingVarNames___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_WF_varyingVarNames___closed__0 = (const lean_object*)&l_Lean_Elab_WF_varyingVarNames___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Elab.WF.preDefsFromUnaryNonRec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "assertion violation: arity = params.size\n        "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wf"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(235, 76, 232, 241, 91, 21, 77, 227)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0(v_k_10_, v_b_11_, v_c_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(lean_object* v_type_19_, lean_object* v_maxFVars_x3f_20_, lean_object* v_k_21_, uint8_t v_cleanupAnnotations_22_, uint8_t v_whnfType_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v___f_29_; lean_object* v___x_30_; 
v___f_29_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_29_, 0, v_k_21_);
v___x_30_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_19_, v_maxFVars_x3f_20_, v___f_29_, v_cleanupAnnotations_22_, v_whnfType_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_38_; 
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_38_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_36_; 
if (v_isShared_34_ == 0)
{
v___x_36_ = v___x_33_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_a_31_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
else
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
v_a_39_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_30_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_30_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___boxed(lean_object* v_type_47_, lean_object* v_maxFVars_x3f_48_, lean_object* v_k_49_, lean_object* v_cleanupAnnotations_50_, lean_object* v_whnfType_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_57_; uint8_t v_whnfType_boxed_58_; lean_object* v_res_59_; 
v_cleanupAnnotations_boxed_57_ = lean_unbox(v_cleanupAnnotations_50_);
v_whnfType_boxed_58_ = lean_unbox(v_whnfType_51_);
v_res_59_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_47_, v_maxFVars_x3f_48_, v_k_49_, v_cleanupAnnotations_boxed_57_, v_whnfType_boxed_58_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1(lean_object* v_00_u03b1_60_, lean_object* v_type_61_, lean_object* v_maxFVars_x3f_62_, lean_object* v_k_63_, uint8_t v_cleanupAnnotations_64_, uint8_t v_whnfType_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_61_, v_maxFVars_x3f_62_, v_k_63_, v_cleanupAnnotations_64_, v_whnfType_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___boxed(lean_object* v_00_u03b1_72_, lean_object* v_type_73_, lean_object* v_maxFVars_x3f_74_, lean_object* v_k_75_, lean_object* v_cleanupAnnotations_76_, lean_object* v_whnfType_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_83_; uint8_t v_whnfType_boxed_84_; lean_object* v_res_85_; 
v_cleanupAnnotations_boxed_83_ = lean_unbox(v_cleanupAnnotations_76_);
v_whnfType_boxed_84_ = lean_unbox(v_whnfType_77_);
v_res_85_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1(v_00_u03b1_72_, v_type_73_, v_maxFVars_x3f_74_, v_k_75_, v_cleanupAnnotations_boxed_83_, v_whnfType_boxed_84_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(lean_object* v_msgData_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v___x_92_; lean_object* v_env_93_; uint8_t v___x_94_; lean_object* v_env_95_; lean_object* v___x_96_; lean_object* v_toCold_97_; lean_object* v_mctx_98_; lean_object* v_lctx_99_; lean_object* v_options_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_92_ = lean_st_ref_get(v___y_90_);
v_env_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc_ref(v_env_93_);
lean_dec(v___x_92_);
v___x_94_ = 0;
v_env_95_ = l_Lean_Environment_setRecordingDeps(v_env_93_, v___x_94_);
v___x_96_ = lean_st_ref_get(v___y_88_);
v_toCold_97_ = lean_ctor_get(v___y_89_, 0);
v_mctx_98_ = lean_ctor_get(v___x_96_, 0);
lean_inc_ref(v_mctx_98_);
lean_dec(v___x_96_);
v_lctx_99_ = lean_ctor_get(v___y_87_, 2);
v_options_100_ = lean_ctor_get(v_toCold_97_, 2);
lean_inc_ref(v_options_100_);
lean_inc_ref(v_lctx_99_);
v___x_101_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_101_, 0, v_env_95_);
lean_ctor_set(v___x_101_, 1, v_mctx_98_);
lean_ctor_set(v___x_101_, 2, v_lctx_99_);
lean_ctor_set(v___x_101_, 3, v_options_100_);
v___x_102_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v_msgData_86_);
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0___boxed(lean_object* v_msgData_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msgData_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(lean_object* v_msg_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_ref_117_; lean_object* v___x_118_; lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_127_; 
v_ref_117_ = lean_ctor_get(v___y_114_, 2);
v___x_118_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msg_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
v_a_119_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_127_ == 0)
{
v___x_121_ = v___x_118_;
v_isShared_122_ = v_isSharedCheck_127_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___x_118_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_127_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___x_125_; 
lean_inc(v_ref_117_);
v___x_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_123_, 0, v_ref_117_);
lean_ctor_set(v___x_123_, 1, v_a_119_);
if (v_isShared_122_ == 0)
{
lean_ctor_set_tag(v___x_121_, 1);
lean_ctor_set(v___x_121_, 0, v___x_123_);
v___x_125_ = v___x_121_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg___boxed(lean_object* v_msg_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v_msg_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
return v_res_134_;
}
}
static lean_object* _init_l_Lean_Elab_WF_withAppN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l_Lean_Elab_WF_withAppN___lam__0___closed__0));
v___x_137_ = l_Lean_stringToMessageData(v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___lam__0(lean_object* v_args_138_, lean_object* v_k_139_, uint8_t v___x_140_, lean_object* v_missing_141_, lean_object* v_xs_142_, lean_object* v_x_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = lean_array_get_size(v_xs_142_);
v___x_157_ = lean_nat_dec_lt(v___x_156_, v_missing_141_);
if (v___x_157_ == 0)
{
goto v___jp_149_;
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
lean_dec_ref(v_k_139_);
lean_dec_ref(v_args_138_);
v___x_158_ = lean_obj_once(&l_Lean_Elab_WF_withAppN___lam__0___closed__1, &l_Lean_Elab_WF_withAppN___lam__0___closed__1_once, _init_l_Lean_Elab_WF_withAppN___lam__0___closed__1);
v___x_159_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v___x_158_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
v_a_160_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_159_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
v___jp_149_:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = l_Array_append___redArg(v_args_138_, v_xs_142_);
lean_inc(v___y_147_);
lean_inc_ref(v___y_146_);
lean_inc(v___y_145_);
lean_inc_ref(v___y_144_);
v___x_151_ = lean_apply_6(v_k_139_, v___x_150_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, lean_box(0));
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; uint8_t v___x_153_; uint8_t v___x_154_; lean_object* v___x_155_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref_known(v___x_151_, 1);
v___x_153_ = 1;
v___x_154_ = 1;
v___x_155_ = l_Lean_Meta_mkLambdaFVars(v_xs_142_, v_a_152_, v___x_140_, v___x_153_, v___x_140_, v___x_153_, v___x_154_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
return v___x_155_;
}
else
{
return v___x_151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___lam__0___boxed(lean_object* v_args_168_, lean_object* v_k_169_, lean_object* v___x_170_, lean_object* v_missing_171_, lean_object* v_xs_172_, lean_object* v_x_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
uint8_t v___x_2251__boxed_179_; lean_object* v_res_180_; 
v___x_2251__boxed_179_ = lean_unbox(v___x_170_);
v_res_180_ = l_Lean_Elab_WF_withAppN___lam__0(v_args_168_, v_k_169_, v___x_2251__boxed_179_, v_missing_171_, v_xs_172_, v_x_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec_ref(v_x_173_);
lean_dec_ref(v_xs_172_);
lean_dec(v_missing_171_);
return v_res_180_;
}
}
static lean_object* _init_l_Lean_Elab_WF_withAppN___closed__0(void){
_start:
{
lean_object* v___x_181_; lean_object* v_dummy_182_; 
v___x_181_ = lean_box(0);
v_dummy_182_ = l_Lean_Expr_sort___override(v___x_181_);
return v_dummy_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN(lean_object* v_n_183_, lean_object* v_e_184_, lean_object* v_k_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_dummy_191_; lean_object* v_nargs_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v_args_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v_dummy_191_ = lean_obj_once(&l_Lean_Elab_WF_withAppN___closed__0, &l_Lean_Elab_WF_withAppN___closed__0_once, _init_l_Lean_Elab_WF_withAppN___closed__0);
v_nargs_192_ = l_Lean_Expr_getAppNumArgs(v_e_184_);
lean_inc(v_nargs_192_);
v___x_193_ = lean_mk_array(v_nargs_192_, v_dummy_191_);
v___x_194_ = lean_unsigned_to_nat(1u);
v___x_195_ = lean_nat_sub(v_nargs_192_, v___x_194_);
lean_dec(v_nargs_192_);
lean_inc_ref(v_e_184_);
v_args_196_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_184_, v___x_193_, v___x_195_);
v___x_197_ = lean_array_get_size(v_args_196_);
v___x_198_ = lean_nat_dec_le(v_n_183_, v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v_missing_199_; lean_object* v___x_200_; lean_object* v___f_201_; lean_object* v___x_202_; 
v_missing_199_ = lean_nat_sub(v_n_183_, v___x_197_);
lean_dec(v_n_183_);
v___x_200_ = lean_box(v___x_198_);
lean_inc(v_missing_199_);
v___f_201_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_withAppN___lam__0___boxed), 11, 4);
lean_closure_set(v___f_201_, 0, v_args_196_);
lean_closure_set(v___f_201_, 1, v_k_185_);
lean_closure_set(v___f_201_, 2, v___x_200_);
lean_closure_set(v___f_201_, 3, v_missing_199_);
lean_inc(v_a_189_);
lean_inc_ref(v_a_188_);
lean_inc(v_a_187_);
lean_inc_ref(v_a_186_);
v___x_202_ = lean_infer_type(v_e_184_, v_a_186_, v_a_187_, v_a_188_, v_a_189_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_211_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_211_ == 0)
{
v___x_205_ = v___x_202_;
v_isShared_206_ = v_isSharedCheck_211_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_202_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_211_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
lean_ctor_set_tag(v___x_205_, 1);
lean_ctor_set(v___x_205_, 0, v_missing_199_);
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_missing_199_);
v___x_208_ = v_reuseFailAlloc_210_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_a_203_, v___x_208_, v___f_201_, v___x_198_, v___x_198_, v_a_186_, v_a_187_, v_a_188_, v_a_189_);
return v___x_209_;
}
}
}
else
{
lean_dec_ref(v___f_201_);
lean_dec(v_missing_199_);
return v___x_202_;
}
}
else
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec_ref(v_e_184_);
v___x_212_ = lean_unsigned_to_nat(0u);
lean_inc(v_n_183_);
lean_inc_ref(v_args_196_);
v___x_213_ = l_Array_toSubarray___redArg(v_args_196_, v___x_212_, v_n_183_);
v___x_214_ = l_Subarray_copy___redArg(v___x_213_);
lean_inc(v_a_189_);
lean_inc_ref(v_a_188_);
lean_inc(v_a_187_);
lean_inc_ref(v_a_186_);
v___x_215_ = lean_apply_6(v_k_185_, v___x_214_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, lean_box(0));
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_230_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_230_ == 0)
{
v___x_218_ = v___x_215_;
v_isShared_219_ = v_isSharedCheck_230_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_215_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_230_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v_lower_221_; lean_object* v_upper_222_; uint8_t v___x_229_; 
v___x_229_ = lean_nat_dec_le(v_n_183_, v___x_212_);
if (v___x_229_ == 0)
{
v_lower_221_ = v_n_183_;
v_upper_222_ = v___x_197_;
goto v___jp_220_;
}
else
{
lean_dec(v_n_183_);
v_lower_221_ = v___x_212_;
v_upper_222_ = v___x_197_;
goto v___jp_220_;
}
v___jp_220_:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_223_ = l_Array_toSubarray___redArg(v_args_196_, v_lower_221_, v_upper_222_);
v___x_224_ = l_Subarray_copy___redArg(v___x_223_);
v___x_225_ = l_Lean_mkAppN(v_a_216_, v___x_224_);
lean_dec_ref(v___x_224_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_225_);
v___x_227_ = v___x_218_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
else
{
lean_dec_ref(v_args_196_);
lean_dec(v_n_183_);
return v___x_215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___boxed(lean_object* v_n_231_, lean_object* v_e_232_, lean_object* v_k_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Elab_WF_withAppN(v_n_231_, v_e_232_, v_k_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0(lean_object* v_00_u03b1_240_, lean_object* v_msg_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v_msg_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___boxed(lean_object* v_00_u03b1_248_, lean_object* v_msg_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0(v_00_u03b1_248_, v_msg_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_packCalls_spec__1(lean_object* v_msg_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v___f_263_; lean_object* v___x_1209__overap_264_; lean_object* v___x_265_; 
v___f_263_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1209__overap_264_ = lean_panic_fn_borrowed(v___f_263_, v_msg_257_);
lean_inc(v___y_261_);
lean_inc_ref(v___y_260_);
lean_inc(v___y_259_);
lean_inc_ref(v___y_258_);
v___x_265_ = lean_apply_5(v___x_1209__overap_264_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, lean_box(0));
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_packCalls_spec__1___boxed(lean_object* v_msg_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_panic___at___00Lean_Elab_WF_packCalls_spec__1(v_msg_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__0(lean_object* v_x_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__0___closed__0));
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__0___boxed(lean_object* v_x_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Elab_WF_packCalls___lam__0(v_x_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec_ref(v_x_283_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__1(lean_object* v___x_290_, lean_object* v_argsPacker_291_, lean_object* v___x_292_, lean_object* v_val_293_, lean_object* v_newF_294_, lean_object* v_args_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_290_, v_args_295_);
v___x_302_ = l_Lean_Meta_ArgsPacker_pack(v_argsPacker_291_, v___x_292_, v_val_293_, v___x_301_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec_ref(v___x_301_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_311_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_311_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_311_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_311_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_307_ = l_Lean_Expr_app___override(v_newF_294_, v_a_303_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_307_);
v___x_309_ = v___x_305_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
else
{
lean_dec_ref(v_newF_294_);
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__1___boxed(lean_object* v___x_312_, lean_object* v_argsPacker_313_, lean_object* v___x_314_, lean_object* v_val_315_, lean_object* v_newF_316_, lean_object* v_args_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Elab_WF_packCalls___lam__1(v___x_312_, v_argsPacker_313_, v___x_314_, v_val_315_, v_newF_316_, v_args_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec_ref(v_args_317_);
lean_dec_ref(v_argsPacker_313_);
lean_dec_ref(v___x_312_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2(lean_object* v_xs_324_, lean_object* v_v_325_, lean_object* v_i_326_){
_start:
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = lean_array_get_size(v_xs_324_);
v___x_328_ = lean_nat_dec_lt(v_i_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
lean_dec(v_i_326_);
v___x_329_ = lean_box(0);
return v___x_329_;
}
else
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = lean_array_fget_borrowed(v_xs_324_, v_i_326_);
v___x_331_ = lean_name_eq(v___x_330_, v_v_325_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_unsigned_to_nat(1u);
v___x_333_ = lean_nat_add(v_i_326_, v___x_332_);
lean_dec(v_i_326_);
v_i_326_ = v___x_333_;
goto _start;
}
else
{
lean_object* v___x_335_; 
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v_i_326_);
return v___x_335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2___boxed(lean_object* v_xs_336_, lean_object* v_v_337_, lean_object* v_i_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2(v_xs_336_, v_v_337_, v_i_338_);
lean_dec(v_v_337_);
lean_dec_ref(v_xs_336_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0(lean_object* v_xs_340_, lean_object* v_v_341_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2(v_xs_340_, v_v_341_, v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0___boxed(lean_object* v_xs_344_, lean_object* v_v_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0(v_xs_344_, v_v_345_);
lean_dec(v_v_345_);
lean_dec_ref(v_xs_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(lean_object* v_xs_347_, lean_object* v_v_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0(v_xs_347_, v_v_348_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v___x_350_; 
v___x_350_ = lean_box(0);
return v___x_350_;
}
else
{
lean_object* v_val_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v_val_351_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_349_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_val_351_);
lean_dec(v___x_349_);
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
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_val_351_);
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
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0___boxed(lean_object* v_xs_359_, lean_object* v_v_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(v_xs_359_, v_v_360_);
lean_dec(v_v_360_);
lean_dec_ref(v_xs_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(lean_object* v_val_362_, lean_object* v___x_363_, size_t v_sz_364_, size_t v_i_365_, lean_object* v_bs_366_){
_start:
{
uint8_t v___x_367_; 
v___x_367_ = lean_usize_dec_lt(v_i_365_, v_sz_364_);
if (v___x_367_ == 0)
{
return v_bs_366_;
}
else
{
lean_object* v_v_368_; lean_object* v___x_369_; lean_object* v_bs_x27_370_; uint8_t v___y_372_; 
v_v_368_ = lean_array_uget(v_bs_366_, v_i_365_);
v___x_369_ = lean_unsigned_to_nat(0u);
v_bs_x27_370_ = lean_array_uset(v_bs_366_, v_i_365_, v___x_369_);
if (lean_obj_tag(v_v_368_) == 0)
{
uint8_t v___x_378_; 
v___x_378_ = 0;
v___y_372_ = v___x_378_;
goto v___jp_371_;
}
else
{
uint8_t v___x_379_; 
lean_dec_ref_known(v_v_368_, 1);
v___x_379_ = lean_nat_dec_lt(v_val_362_, v___x_363_);
v___y_372_ = v___x_379_;
goto v___jp_371_;
}
v___jp_371_:
{
size_t v___x_373_; size_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_373_ = ((size_t)1ULL);
v___x_374_ = lean_usize_add(v_i_365_, v___x_373_);
v___x_375_ = lean_box(v___y_372_);
v___x_376_ = lean_array_uset(v_bs_x27_370_, v_i_365_, v___x_375_);
v_i_365_ = v___x_374_;
v_bs_366_ = v___x_376_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2___boxed(lean_object* v_val_380_, lean_object* v___x_381_, lean_object* v_sz_382_, lean_object* v_i_383_, lean_object* v_bs_384_){
_start:
{
size_t v_sz_boxed_385_; size_t v_i_boxed_386_; lean_object* v_res_387_; 
v_sz_boxed_385_ = lean_unbox_usize(v_sz_382_);
lean_dec(v_sz_382_);
v_i_boxed_386_ = lean_unbox_usize(v_i_383_);
lean_dec(v_i_383_);
v_res_387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(v_val_380_, v___x_381_, v_sz_boxed_385_, v_i_boxed_386_, v_bs_384_);
lean_dec(v___x_381_);
lean_dec(v_val_380_);
return v_res_387_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___lam__2___closed__3(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_391_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__2));
v___x_392_ = lean_unsigned_to_nat(6u);
v___x_393_ = lean_unsigned_to_nat(55u);
v___x_394_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__1));
v___x_395_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_396_ = l_mkPanicMessageWithDecl(v___x_395_, v___x_394_, v___x_393_, v___x_392_, v___x_391_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__2(lean_object* v_funNames_397_, lean_object* v_fixedParamPerms_398_, lean_object* v___x_399_, lean_object* v_argsPacker_400_, lean_object* v___x_401_, lean_object* v_newF_402_, lean_object* v_e_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = l_Lean_Expr_getAppFn(v_e_403_);
v___x_410_ = l_Lean_Expr_isConst(v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec_ref(v___x_409_);
lean_dec_ref(v_newF_402_);
lean_dec_ref(v___x_401_);
lean_dec_ref(v_argsPacker_400_);
v___x_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_411_, 0, v_e_403_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
else
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = l_Lean_Expr_constName_x21(v___x_409_);
lean_dec_ref(v___x_409_);
v___x_414_ = l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(v_funNames_397_, v___x_413_);
lean_dec(v___x_413_);
if (lean_obj_tag(v___x_414_) == 1)
{
lean_object* v_val_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_450_; 
v_val_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_450_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_450_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_val_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_450_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v_perms_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v_perms_419_ = lean_ctor_get(v_fixedParamPerms_398_, 1);
v___x_420_ = lean_array_get_size(v_perms_419_);
v___x_421_ = lean_nat_dec_lt(v_val_415_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; 
lean_del_object(v___x_417_);
lean_dec(v_val_415_);
lean_dec_ref(v_e_403_);
lean_dec_ref(v_newF_402_);
lean_dec_ref(v___x_401_);
lean_dec_ref(v_argsPacker_400_);
v___x_422_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__3, &l_Lean_Elab_WF_packCalls___lam__2___closed__3_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__3);
v___x_423_ = l_panic___at___00Lean_Elab_WF_packCalls_spec__1(v___x_422_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
return v___x_423_;
}
else
{
lean_object* v___x_424_; lean_object* v___f_425_; size_t v_sz_426_; size_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_424_ = lean_array_get_borrowed(v___x_399_, v_perms_419_, v_val_415_);
lean_inc(v_val_415_);
lean_inc_n(v___x_424_, 2);
v___f_425_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packCalls___lam__1___boxed), 11, 5);
lean_closure_set(v___f_425_, 0, v___x_424_);
lean_closure_set(v___f_425_, 1, v_argsPacker_400_);
lean_closure_set(v___f_425_, 2, v___x_401_);
lean_closure_set(v___f_425_, 3, v_val_415_);
lean_closure_set(v___f_425_, 4, v_newF_402_);
v_sz_426_ = lean_array_size(v___x_424_);
v___x_427_ = ((size_t)0ULL);
v___x_428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(v_val_415_, v___x_420_, v_sz_426_, v___x_427_, v___x_424_);
lean_dec(v_val_415_);
v___x_429_ = lean_array_get_size(v___x_428_);
lean_dec_ref(v___x_428_);
v___x_430_ = l_Lean_Elab_WF_withAppN(v___x_429_, v_e_403_, v___f_425_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_441_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_441_ == 0)
{
v___x_433_ = v___x_430_;
v_isShared_434_ = v_isSharedCheck_441_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_430_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_441_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set_tag(v___x_417_, 0);
lean_ctor_set(v___x_417_, 0, v_a_431_);
v___x_436_ = v___x_417_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_440_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_438_; 
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_436_);
v___x_438_ = v___x_433_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_del_object(v___x_417_);
v_a_442_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_430_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_430_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
}
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; 
lean_dec(v___x_414_);
lean_dec_ref(v_newF_402_);
lean_dec_ref(v___x_401_);
lean_dec_ref(v_argsPacker_400_);
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v_e_403_);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
return v___x_452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__2___boxed(lean_object* v_funNames_453_, lean_object* v_fixedParamPerms_454_, lean_object* v___x_455_, lean_object* v_argsPacker_456_, lean_object* v___x_457_, lean_object* v_newF_458_, lean_object* v_e_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Elab_WF_packCalls___lam__2(v_funNames_453_, v_fixedParamPerms_454_, v___x_455_, v_argsPacker_456_, v___x_457_, v_newF_458_, v_e_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec_ref(v___x_455_);
lean_dec_ref(v_fixedParamPerms_454_);
lean_dec_ref(v_funNames_453_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_object* v_00_u03b1_466_, lean_object* v_x_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_apply_1(v_x_467_, lean_box(0));
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0___boxed(lean_object* v_00_u03b1_475_, lean_object* v_x_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(v_00_u03b1_475_, v_x_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v_res_482_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = l_Lean_maxRecDepthErrorMessage;
v___x_489_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3);
v___x_491_ = l_Lean_MessageData_ofFormat(v___x_490_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4);
v___x_493_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2));
v___x_494_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v___x_492_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(lean_object* v_ref_495_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v_ref_495_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___boxed(lean_object* v_ref_500_, lean_object* v___y_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(lean_object* v_x_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v___y_511_; lean_object* v_toCold_520_; lean_object* v_currRecDepth_521_; lean_object* v_ref_522_; uint16_t v_optionFlags_523_; uint8_t v_suppressElabErrors_524_; uint8_t v_isRecordingDeps_525_; lean_object* v_maxRecDepth_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v_toCold_520_ = lean_ctor_get(v___y_507_, 0);
v_currRecDepth_521_ = lean_ctor_get(v___y_507_, 1);
v_ref_522_ = lean_ctor_get(v___y_507_, 2);
v_optionFlags_523_ = lean_ctor_get_uint16(v___y_507_, sizeof(void*)*3);
v_suppressElabErrors_524_ = lean_ctor_get_uint8(v___y_507_, sizeof(void*)*3 + 2);
v_isRecordingDeps_525_ = lean_ctor_get_uint8(v___y_507_, sizeof(void*)*3 + 3);
v_maxRecDepth_531_ = lean_ctor_get(v_toCold_520_, 3);
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = lean_nat_dec_eq(v_maxRecDepth_531_, v___x_532_);
if (v___x_533_ == 0)
{
uint8_t v___x_534_; 
v___x_534_ = lean_nat_dec_eq(v_currRecDepth_521_, v_maxRecDepth_531_);
if (v___x_534_ == 0)
{
goto v___jp_526_;
}
else
{
lean_object* v___x_535_; 
lean_dec_ref(v_x_503_);
lean_inc(v_ref_522_);
v___x_535_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_522_);
v___y_511_ = v___x_535_;
goto v___jp_510_;
}
}
else
{
goto v___jp_526_;
}
v___jp_510_:
{
if (lean_obj_tag(v___y_511_) == 0)
{
return v___y_511_;
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
v_a_512_ = lean_ctor_get(v___y_511_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___y_511_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___y_511_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___y_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
v___jp_526_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_527_ = lean_unsigned_to_nat(1u);
v___x_528_ = lean_nat_add(v_currRecDepth_521_, v___x_527_);
lean_inc(v_ref_522_);
lean_inc_ref(v_toCold_520_);
v___x_529_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_529_, 0, v_toCold_520_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
lean_ctor_set(v___x_529_, 2, v_ref_522_);
lean_ctor_set_uint16(v___x_529_, sizeof(void*)*3, v_optionFlags_523_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*3 + 2, v_suppressElabErrors_524_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*3 + 3, v_isRecordingDeps_525_);
lean_inc(v___y_508_);
lean_inc(v___y_506_);
lean_inc_ref(v___y_505_);
lean_inc(v___y_504_);
v___x_530_ = lean_apply_6(v_x_503_, v___y_504_, v___y_505_, v___y_506_, v___x_529_, v___y_508_, lean_box(0));
v___y_511_ = v___x_530_;
goto v___jp_510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg___boxed(lean_object* v_x_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__2(lean_object* v___x_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_544_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__2___boxed(lean_object* v___x_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__2(v___x_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(lean_object* v_k_558_, lean_object* v___y_559_, lean_object* v_b_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___x_566_; 
lean_inc(v___y_564_);
lean_inc_ref(v___y_563_);
lean_inc(v___y_562_);
lean_inc_ref(v___y_561_);
lean_inc(v___y_559_);
v___x_566_ = lean_apply_7(v_k_558_, v_b_560_, v___y_559_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, lean_box(0));
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed(lean_object* v_k_567_, lean_object* v___y_568_, lean_object* v_b_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(v_k_567_, v___y_568_, v_b_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_568_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(lean_object* v_name_576_, lean_object* v_type_577_, lean_object* v_val_578_, lean_object* v_k_579_, uint8_t v_nondep_580_, uint8_t v_kind_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v___f_588_; lean_object* v___x_589_; 
lean_inc(v___y_582_);
v___f_588_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_588_, 0, v_k_579_);
lean_closure_set(v___f_588_, 1, v___y_582_);
v___x_589_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_576_, v_type_577_, v_val_578_, v___f_588_, v_nondep_580_, v_kind_581_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_589_) == 0)
{
return v___x_589_;
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_589_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg___boxed(lean_object* v_name_598_, lean_object* v_type_599_, lean_object* v_val_600_, lean_object* v_k_601_, lean_object* v_nondep_602_, lean_object* v_kind_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
uint8_t v_nondep_boxed_610_; uint8_t v_kind_boxed_611_; lean_object* v_res_612_; 
v_nondep_boxed_610_ = lean_unbox(v_nondep_602_);
v_kind_boxed_611_ = lean_unbox(v_kind_603_);
v_res_612_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_598_, v_type_599_, v_val_600_, v_k_601_, v_nondep_boxed_610_, v_kind_boxed_611_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(lean_object* v_name_613_, uint8_t v_bi_614_, lean_object* v_type_615_, lean_object* v_k_616_, uint8_t v_kind_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v___f_624_; lean_object* v___x_625_; 
lean_inc(v___y_618_);
v___f_624_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_624_, 0, v_k_616_);
lean_closure_set(v___f_624_, 1, v___y_618_);
v___x_625_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_613_, v_bi_614_, v_type_615_, v___f_624_, v_kind_617_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_625_) == 0)
{
return v___x_625_;
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_625_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_625_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___boxed(lean_object* v_name_634_, lean_object* v_bi_635_, lean_object* v_type_636_, lean_object* v_k_637_, lean_object* v_kind_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
uint8_t v_bi_boxed_645_; uint8_t v_kind_boxed_646_; lean_object* v_res_647_; 
v_bi_boxed_645_ = lean_unbox(v_bi_635_);
v_kind_boxed_646_ = lean_unbox(v_kind_638_);
v_res_647_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_634_, v_bi_boxed_645_, v_type_636_, v_k_637_, v_kind_boxed_646_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_object* v_00_u03b1_648_, lean_object* v_x_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_apply_1(v_x_649_, lean_box(0));
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0___boxed(lean_object* v_00_u03b1_657_, lean_object* v_x_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(v_00_u03b1_657_, v_x_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_spec__7___redArg(lean_object* v_a_665_, lean_object* v_x_666_){
_start:
{
if (lean_obj_tag(v_x_666_) == 0)
{
lean_object* v___x_667_; 
v___x_667_ = lean_box(0);
return v___x_667_;
}
else
{
lean_object* v_key_668_; lean_object* v_value_669_; lean_object* v_tail_670_; uint8_t v___x_671_; 
v_key_668_ = lean_ctor_get(v_x_666_, 0);
v_value_669_ = lean_ctor_get(v_x_666_, 1);
v_tail_670_ = lean_ctor_get(v_x_666_, 2);
v___x_671_ = l_Lean_ExprStructEq_beq(v_key_668_, v_a_665_);
if (v___x_671_ == 0)
{
v_x_666_ = v_tail_670_;
goto _start;
}
else
{
lean_object* v___x_673_; 
lean_inc(v_value_669_);
v___x_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_673_, 0, v_value_669_);
return v___x_673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_a_674_, lean_object* v_x_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_spec__7___redArg(v_a_674_, v_x_675_);
lean_dec(v_x_675_);
lean_dec_ref(v_a_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___redArg(lean_object* v_m_677_, lean_object* v_a_678_){
_start:
{
lean_object* v_buckets_679_; lean_object* v___x_680_; uint64_t v___x_681_; uint64_t v___x_682_; uint64_t v___x_683_; uint64_t v_fold_684_; uint64_t v___x_685_; uint64_t v___x_686_; uint64_t v___x_687_; size_t v___x_688_; size_t v___x_689_; size_t v___x_690_; size_t v___x_691_; size_t v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v_buckets_679_ = lean_ctor_get(v_m_677_, 1);
v___x_680_ = lean_array_get_size(v_buckets_679_);
v___x_681_ = l_Lean_ExprStructEq_hash(v_a_678_);
v___x_682_ = 32ULL;
v___x_683_ = lean_uint64_shift_right(v___x_681_, v___x_682_);
v_fold_684_ = lean_uint64_xor(v___x_681_, v___x_683_);
v___x_685_ = 16ULL;
v___x_686_ = lean_uint64_shift_right(v_fold_684_, v___x_685_);
v___x_687_ = lean_uint64_xor(v_fold_684_, v___x_686_);
v___x_688_ = lean_uint64_to_usize(v___x_687_);
v___x_689_ = lean_usize_of_nat(v___x_680_);
v___x_690_ = ((size_t)1ULL);
v___x_691_ = lean_usize_sub(v___x_689_, v___x_690_);
v___x_692_ = lean_usize_land(v___x_688_, v___x_691_);
v___x_693_ = lean_array_uget_borrowed(v_buckets_679_, v___x_692_);
v___x_694_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_spec__7___redArg(v_a_678_, v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_m_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___redArg(v_m_695_, v_a_696_);
lean_dec_ref(v_a_696_);
lean_dec_ref(v_m_695_);
return v_res_697_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(lean_object* v_a_698_, lean_object* v_x_699_){
_start:
{
if (lean_obj_tag(v_x_699_) == 0)
{
uint8_t v___x_700_; 
v___x_700_ = 0;
return v___x_700_;
}
else
{
lean_object* v_key_701_; lean_object* v_tail_702_; uint8_t v___x_703_; 
v_key_701_ = lean_ctor_get(v_x_699_, 0);
v_tail_702_ = lean_ctor_get(v_x_699_, 2);
v___x_703_ = l_Lean_ExprStructEq_beq(v_key_701_, v_a_698_);
if (v___x_703_ == 0)
{
v_x_699_ = v_tail_702_;
goto _start;
}
else
{
return v___x_703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg___boxed(lean_object* v_a_705_, lean_object* v_x_706_){
_start:
{
uint8_t v_res_707_; lean_object* v_r_708_; 
v_res_707_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_705_, v_x_706_);
lean_dec(v_x_706_);
lean_dec_ref(v_a_705_);
v_r_708_ = lean_box(v_res_707_);
return v_r_708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(lean_object* v_x_709_, lean_object* v_x_710_){
_start:
{
if (lean_obj_tag(v_x_710_) == 0)
{
return v_x_709_;
}
else
{
lean_object* v_key_711_; lean_object* v_value_712_; lean_object* v_tail_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_736_; 
v_key_711_ = lean_ctor_get(v_x_710_, 0);
v_value_712_ = lean_ctor_get(v_x_710_, 1);
v_tail_713_ = lean_ctor_get(v_x_710_, 2);
v_isSharedCheck_736_ = !lean_is_exclusive(v_x_710_);
if (v_isSharedCheck_736_ == 0)
{
v___x_715_ = v_x_710_;
v_isShared_716_ = v_isSharedCheck_736_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_tail_713_);
lean_inc(v_value_712_);
lean_inc(v_key_711_);
lean_dec(v_x_710_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_736_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; uint64_t v___x_718_; uint64_t v___x_719_; uint64_t v___x_720_; uint64_t v_fold_721_; uint64_t v___x_722_; uint64_t v___x_723_; uint64_t v___x_724_; size_t v___x_725_; size_t v___x_726_; size_t v___x_727_; size_t v___x_728_; size_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_717_ = lean_array_get_size(v_x_709_);
v___x_718_ = l_Lean_ExprStructEq_hash(v_key_711_);
v___x_719_ = 32ULL;
v___x_720_ = lean_uint64_shift_right(v___x_718_, v___x_719_);
v_fold_721_ = lean_uint64_xor(v___x_718_, v___x_720_);
v___x_722_ = 16ULL;
v___x_723_ = lean_uint64_shift_right(v_fold_721_, v___x_722_);
v___x_724_ = lean_uint64_xor(v_fold_721_, v___x_723_);
v___x_725_ = lean_uint64_to_usize(v___x_724_);
v___x_726_ = lean_usize_of_nat(v___x_717_);
v___x_727_ = ((size_t)1ULL);
v___x_728_ = lean_usize_sub(v___x_726_, v___x_727_);
v___x_729_ = lean_usize_land(v___x_725_, v___x_728_);
v___x_730_ = lean_array_uget_borrowed(v_x_709_, v___x_729_);
lean_inc(v___x_730_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 2, v___x_730_);
v___x_732_ = v___x_715_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_key_711_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_value_712_);
lean_ctor_set(v_reuseFailAlloc_735_, 2, v___x_730_);
v___x_732_ = v_reuseFailAlloc_735_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; 
v___x_733_ = lean_array_uset(v_x_709_, v___x_729_, v___x_732_);
v_x_709_ = v___x_733_;
v_x_710_ = v_tail_713_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(lean_object* v_i_737_, lean_object* v_source_738_, lean_object* v_target_739_){
_start:
{
lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_740_ = lean_array_get_size(v_source_738_);
v___x_741_ = lean_nat_dec_lt(v_i_737_, v___x_740_);
if (v___x_741_ == 0)
{
lean_dec_ref(v_source_738_);
lean_dec(v_i_737_);
return v_target_739_;
}
else
{
lean_object* v_es_742_; lean_object* v___x_743_; lean_object* v_source_744_; lean_object* v_target_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_es_742_ = lean_array_fget(v_source_738_, v_i_737_);
v___x_743_ = lean_box(0);
v_source_744_ = lean_array_fset(v_source_738_, v_i_737_, v___x_743_);
v_target_745_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(v_target_739_, v_es_742_);
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = lean_nat_add(v_i_737_, v___x_746_);
lean_dec(v_i_737_);
v_i_737_ = v___x_747_;
v_source_738_ = v_source_744_;
v_target_739_ = v_target_745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(lean_object* v_data_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v_nbuckets_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_750_ = lean_array_get_size(v_data_749_);
v___x_751_ = lean_unsigned_to_nat(2u);
v_nbuckets_752_ = lean_nat_mul(v___x_750_, v___x_751_);
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = lean_box(0);
v___x_755_ = lean_mk_array(v_nbuckets_752_, v___x_754_);
v___x_756_ = lean_array_propagate_mark(v_data_749_, v___x_755_);
v___x_757_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v___x_753_, v_data_749_, v___x_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(lean_object* v_a_758_, lean_object* v_b_759_, lean_object* v_x_760_){
_start:
{
if (lean_obj_tag(v_x_760_) == 0)
{
lean_dec(v_b_759_);
lean_dec_ref(v_a_758_);
return v_x_760_;
}
else
{
lean_object* v_key_761_; lean_object* v_value_762_; lean_object* v_tail_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_775_; 
v_key_761_ = lean_ctor_get(v_x_760_, 0);
v_value_762_ = lean_ctor_get(v_x_760_, 1);
v_tail_763_ = lean_ctor_get(v_x_760_, 2);
v_isSharedCheck_775_ = !lean_is_exclusive(v_x_760_);
if (v_isSharedCheck_775_ == 0)
{
v___x_765_ = v_x_760_;
v_isShared_766_ = v_isSharedCheck_775_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_tail_763_);
lean_inc(v_value_762_);
lean_inc(v_key_761_);
lean_dec(v_x_760_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_775_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
uint8_t v___x_767_; 
v___x_767_ = l_Lean_ExprStructEq_beq(v_key_761_, v_a_758_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_768_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_758_, v_b_759_, v_tail_763_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 2, v___x_768_);
v___x_770_ = v___x_765_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_key_761_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_value_762_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
else
{
lean_object* v___x_773_; 
lean_dec(v_value_762_);
lean_dec(v_key_761_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v_b_759_);
lean_ctor_set(v___x_765_, 0, v_a_758_);
v___x_773_ = v___x_765_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_758_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_b_759_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_tail_763_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(lean_object* v_m_776_, lean_object* v_a_777_, lean_object* v_b_778_){
_start:
{
lean_object* v_size_779_; lean_object* v_buckets_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_823_; 
v_size_779_ = lean_ctor_get(v_m_776_, 0);
v_buckets_780_ = lean_ctor_get(v_m_776_, 1);
v_isSharedCheck_823_ = !lean_is_exclusive(v_m_776_);
if (v_isSharedCheck_823_ == 0)
{
v___x_782_ = v_m_776_;
v_isShared_783_ = v_isSharedCheck_823_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_buckets_780_);
lean_inc(v_size_779_);
lean_dec(v_m_776_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_823_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; uint64_t v___x_785_; uint64_t v___x_786_; uint64_t v___x_787_; uint64_t v_fold_788_; uint64_t v___x_789_; uint64_t v___x_790_; uint64_t v___x_791_; size_t v___x_792_; size_t v___x_793_; size_t v___x_794_; size_t v___x_795_; size_t v___x_796_; lean_object* v_bkt_797_; uint8_t v___x_798_; 
v___x_784_ = lean_array_get_size(v_buckets_780_);
v___x_785_ = l_Lean_ExprStructEq_hash(v_a_777_);
v___x_786_ = 32ULL;
v___x_787_ = lean_uint64_shift_right(v___x_785_, v___x_786_);
v_fold_788_ = lean_uint64_xor(v___x_785_, v___x_787_);
v___x_789_ = 16ULL;
v___x_790_ = lean_uint64_shift_right(v_fold_788_, v___x_789_);
v___x_791_ = lean_uint64_xor(v_fold_788_, v___x_790_);
v___x_792_ = lean_uint64_to_usize(v___x_791_);
v___x_793_ = lean_usize_of_nat(v___x_784_);
v___x_794_ = ((size_t)1ULL);
v___x_795_ = lean_usize_sub(v___x_793_, v___x_794_);
v___x_796_ = lean_usize_land(v___x_792_, v___x_795_);
v_bkt_797_ = lean_array_uget_borrowed(v_buckets_780_, v___x_796_);
v___x_798_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_777_, v_bkt_797_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; lean_object* v_size_x27_800_; lean_object* v___x_801_; lean_object* v_buckets_x27_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_799_ = lean_unsigned_to_nat(1u);
v_size_x27_800_ = lean_nat_add(v_size_779_, v___x_799_);
lean_dec(v_size_779_);
lean_inc(v_bkt_797_);
v___x_801_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_801_, 0, v_a_777_);
lean_ctor_set(v___x_801_, 1, v_b_778_);
lean_ctor_set(v___x_801_, 2, v_bkt_797_);
v_buckets_x27_802_ = lean_array_uset(v_buckets_780_, v___x_796_, v___x_801_);
v___x_803_ = lean_unsigned_to_nat(4u);
v___x_804_ = lean_nat_mul(v_size_x27_800_, v___x_803_);
v___x_805_ = lean_unsigned_to_nat(3u);
v___x_806_ = lean_nat_div(v___x_804_, v___x_805_);
lean_dec(v___x_804_);
v___x_807_ = lean_array_get_size(v_buckets_x27_802_);
v___x_808_ = lean_nat_dec_le(v___x_806_, v___x_807_);
lean_dec(v___x_806_);
if (v___x_808_ == 0)
{
lean_object* v_val_809_; lean_object* v___x_811_; 
v_val_809_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_buckets_x27_802_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v_val_809_);
lean_ctor_set(v___x_782_, 0, v_size_x27_800_);
v___x_811_ = v___x_782_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_size_x27_800_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_val_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
else
{
lean_object* v___x_814_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v_buckets_x27_802_);
lean_ctor_set(v___x_782_, 0, v_size_x27_800_);
v___x_814_ = v___x_782_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_size_x27_800_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_buckets_x27_802_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
else
{
lean_object* v___x_816_; lean_object* v_buckets_x27_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
lean_inc(v_bkt_797_);
v___x_816_ = lean_box(0);
v_buckets_x27_817_ = lean_array_uset(v_buckets_780_, v___x_796_, v___x_816_);
v___x_818_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_777_, v_b_778_, v_bkt_797_);
v___x_819_ = lean_array_uset(v_buckets_x27_817_, v___x_796_, v___x_818_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v___x_819_);
v___x_821_ = v___x_782_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_size_779_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(lean_object* v_a_824_, lean_object* v_e_825_, lean_object* v_a_826_){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_828_ = lean_st_ref_take(v_a_824_);
v___x_829_ = lean_box(0);
v___x_830_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v___x_828_, v_e_825_, v_a_826_);
v___x_831_ = lean_st_ref_put(v_a_824_, v___x_830_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed(lean_object* v_a_832_, lean_object* v_e_833_, lean_object* v_a_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(v_a_832_, v_e_833_, v_a_834_);
lean_dec(v_a_832_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed(lean_object* v_fvars_837_, lean_object* v_pre_838_, lean_object* v_post_839_, lean_object* v_usedLetOnly_840_, lean_object* v_skipConstInApp_841_, lean_object* v_skipInstances_842_, lean_object* v_postApp_843_, lean_object* v_body_844_, lean_object* v_x_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
uint8_t v_usedLetOnly_boxed_852_; uint8_t v_skipConstInApp_boxed_853_; uint8_t v_skipInstances_boxed_854_; lean_object* v_res_855_; 
v_usedLetOnly_boxed_852_ = lean_unbox(v_usedLetOnly_840_);
v_skipConstInApp_boxed_853_ = lean_unbox(v_skipConstInApp_841_);
v_skipInstances_boxed_854_ = lean_unbox(v_skipInstances_842_);
v_res_855_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(v_fvars_837_, v_pre_838_, v_post_839_, v_usedLetOnly_boxed_852_, v_skipConstInApp_boxed_853_, v_skipInstances_boxed_854_, v_postApp_843_, v_body_844_, v_x_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(lean_object* v_fvars_859_, lean_object* v_pre_860_, lean_object* v_post_861_, uint8_t v_usedLetOnly_862_, uint8_t v_skipConstInApp_863_, uint8_t v_skipInstances_864_, lean_object* v_postApp_865_, lean_object* v_body_866_, lean_object* v_x_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_array_push(v_fvars_859_, v_x_867_);
v___x_875_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_860_, v_post_861_, v_usedLetOnly_862_, v_skipConstInApp_863_, v_skipInstances_864_, v_postApp_865_, v___x_874_, v_body_866_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed(lean_object* v_fvars_876_, lean_object* v_pre_877_, lean_object* v_post_878_, lean_object* v_usedLetOnly_879_, lean_object* v_skipConstInApp_880_, lean_object* v_skipInstances_881_, lean_object* v_postApp_882_, lean_object* v_body_883_, lean_object* v_x_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
uint8_t v_usedLetOnly_boxed_891_; uint8_t v_skipConstInApp_boxed_892_; uint8_t v_skipInstances_boxed_893_; lean_object* v_res_894_; 
v_usedLetOnly_boxed_891_ = lean_unbox(v_usedLetOnly_879_);
v_skipConstInApp_boxed_892_ = lean_unbox(v_skipConstInApp_880_);
v_skipInstances_boxed_893_ = lean_unbox(v_skipInstances_881_);
v_res_894_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(v_fvars_876_, v_pre_877_, v_post_878_, v_usedLetOnly_boxed_891_, v_skipConstInApp_boxed_892_, v_skipInstances_boxed_893_, v_postApp_882_, v_body_883_, v_x_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(lean_object* v_pre_895_, lean_object* v_post_896_, uint8_t v_usedLetOnly_897_, uint8_t v_skipConstInApp_898_, uint8_t v_skipInstances_899_, lean_object* v_postApp_900_, lean_object* v_e_901_, lean_object* v_a_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; 
lean_inc_ref(v_post_896_);
lean_inc(v___y_906_);
lean_inc_ref(v___y_905_);
lean_inc(v___y_904_);
lean_inc_ref(v___y_903_);
lean_inc_ref(v_e_901_);
v___x_908_ = lean_apply_6(v_post_896_, v_e_901_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, lean_box(0));
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_927_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_927_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_927_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_927_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
switch(lean_obj_tag(v_a_909_))
{
case 0:
{
lean_object* v_e_913_; lean_object* v___x_915_; 
lean_dec_ref(v_e_901_);
lean_dec_ref(v_postApp_900_);
lean_dec_ref(v_post_896_);
lean_dec_ref(v_pre_895_);
v_e_913_ = lean_ctor_get(v_a_909_, 0);
lean_inc_ref(v_e_913_);
lean_dec_ref_known(v_a_909_, 1);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v_e_913_);
v___x_915_ = v___x_911_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_e_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
case 1:
{
lean_object* v_e_917_; lean_object* v___x_918_; 
lean_del_object(v___x_911_);
lean_dec_ref(v_e_901_);
v_e_917_ = lean_ctor_get(v_a_909_, 0);
lean_inc_ref(v_e_917_);
lean_dec_ref_known(v_a_909_, 1);
v___x_918_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_895_, v_post_896_, v_usedLetOnly_897_, v_skipConstInApp_898_, v_skipInstances_899_, v_postApp_900_, v_e_917_, v_a_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
return v___x_918_;
}
default: 
{
lean_object* v_e_x3f_919_; 
lean_dec_ref(v_postApp_900_);
lean_dec_ref(v_post_896_);
lean_dec_ref(v_pre_895_);
v_e_x3f_919_ = lean_ctor_get(v_a_909_, 0);
lean_inc(v_e_x3f_919_);
lean_dec_ref_known(v_a_909_, 1);
if (lean_obj_tag(v_e_x3f_919_) == 0)
{
lean_object* v___x_921_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v_e_901_);
v___x_921_ = v___x_911_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_e_901_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
else
{
lean_object* v_val_923_; lean_object* v___x_925_; 
lean_dec_ref(v_e_901_);
v_val_923_ = lean_ctor_get(v_e_x3f_919_, 0);
lean_inc(v_val_923_);
lean_dec_ref_known(v_e_x3f_919_, 1);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v_val_923_);
v___x_925_ = v___x_911_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_val_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec_ref(v_e_901_);
lean_dec_ref(v_postApp_900_);
lean_dec_ref(v_post_896_);
lean_dec_ref(v_pre_895_);
v_a_928_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_908_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_908_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(lean_object* v_pre_936_, lean_object* v_post_937_, uint8_t v_usedLetOnly_938_, uint8_t v_skipConstInApp_939_, uint8_t v_skipInstances_940_, lean_object* v_postApp_941_, lean_object* v_fvars_942_, lean_object* v_e_943_, lean_object* v_a_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
if (lean_obj_tag(v_e_943_) == 6)
{
lean_object* v_binderName_950_; lean_object* v_binderType_951_; lean_object* v_body_952_; uint8_t v_binderInfo_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___f_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_binderName_950_ = lean_ctor_get(v_e_943_, 0);
lean_inc(v_binderName_950_);
v_binderType_951_ = lean_ctor_get(v_e_943_, 1);
lean_inc_ref(v_binderType_951_);
v_body_952_ = lean_ctor_get(v_e_943_, 2);
lean_inc_ref(v_body_952_);
v_binderInfo_953_ = lean_ctor_get_uint8(v_e_943_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_943_, 3);
v___x_954_ = lean_box(v_usedLetOnly_938_);
v___x_955_ = lean_box(v_skipConstInApp_939_);
v___x_956_ = lean_box(v_skipInstances_940_);
lean_inc_ref(v_postApp_941_);
lean_inc_ref(v_post_937_);
lean_inc_ref(v_pre_936_);
lean_inc_ref(v_fvars_942_);
v___f_957_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed), 15, 8);
lean_closure_set(v___f_957_, 0, v_fvars_942_);
lean_closure_set(v___f_957_, 1, v_pre_936_);
lean_closure_set(v___f_957_, 2, v_post_937_);
lean_closure_set(v___f_957_, 3, v___x_954_);
lean_closure_set(v___f_957_, 4, v___x_955_);
lean_closure_set(v___f_957_, 5, v___x_956_);
lean_closure_set(v___f_957_, 6, v_postApp_941_);
lean_closure_set(v___f_957_, 7, v_body_952_);
v___x_958_ = lean_expr_instantiate_rev(v_binderType_951_, v_fvars_942_);
lean_dec_ref(v_fvars_942_);
lean_dec_ref(v_binderType_951_);
v___x_959_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_936_, v_post_937_, v_usedLetOnly_938_, v_skipConstInApp_939_, v_skipInstances_940_, v_postApp_941_, v___x_958_, v_a_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; uint8_t v___x_961_; lean_object* v___x_962_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref_known(v___x_959_, 1);
v___x_961_ = 0;
v___x_962_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_950_, v_binderInfo_953_, v_a_960_, v___f_957_, v___x_961_, v_a_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
return v___x_962_;
}
else
{
lean_dec_ref(v___f_957_);
lean_dec(v_binderName_950_);
return v___x_959_;
}
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_expr_instantiate_rev(v_e_943_, v_fvars_942_);
lean_dec_ref(v_e_943_);
lean_inc_ref(v_postApp_941_);
lean_inc_ref(v_post_937_);
lean_inc_ref(v_pre_936_);
v___x_964_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_936_, v_post_937_, v_usedLetOnly_938_, v_skipConstInApp_939_, v_skipInstances_940_, v_postApp_941_, v___x_963_, v_a_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; uint8_t v___x_966_; uint8_t v___x_967_; uint8_t v___x_968_; lean_object* v___x_969_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_964_, 1);
v___x_966_ = 0;
v___x_967_ = 1;
v___x_968_ = 1;
v___x_969_ = l_Lean_Meta_mkLambdaFVars(v_fvars_942_, v_a_965_, v___x_966_, v_usedLetOnly_938_, v___x_966_, v___x_967_, v___x_968_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec_ref(v_fvars_942_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_971_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_936_, v_post_937_, v_usedLetOnly_938_, v_skipConstInApp_939_, v_skipInstances_940_, v_postApp_941_, v_a_970_, v_a_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
return v___x_971_;
}
else
{
lean_dec_ref(v_postApp_941_);
lean_dec_ref(v_post_937_);
lean_dec_ref(v_pre_936_);
return v___x_969_;
}
}
else
{
lean_dec_ref(v_fvars_942_);
lean_dec_ref(v_postApp_941_);
lean_dec_ref(v_post_937_);
lean_dec_ref(v_pre_936_);
return v___x_964_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(lean_object* v_fvars_972_, lean_object* v_pre_973_, lean_object* v_post_974_, uint8_t v_usedLetOnly_975_, uint8_t v_skipConstInApp_976_, uint8_t v_skipInstances_977_, lean_object* v_postApp_978_, lean_object* v_body_979_, lean_object* v_x_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_array_push(v_fvars_972_, v_x_980_);
v___x_988_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_973_, v_post_974_, v_usedLetOnly_975_, v_skipConstInApp_976_, v_skipInstances_977_, v_postApp_978_, v___x_987_, v_body_979_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_989_, lean_object* v_pre_990_, lean_object* v_post_991_, lean_object* v_usedLetOnly_992_, lean_object* v_skipConstInApp_993_, lean_object* v_skipInstances_994_, lean_object* v_postApp_995_, lean_object* v_body_996_, lean_object* v_x_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
uint8_t v_usedLetOnly_boxed_1004_; uint8_t v_skipConstInApp_boxed_1005_; uint8_t v_skipInstances_boxed_1006_; lean_object* v_res_1007_; 
v_usedLetOnly_boxed_1004_ = lean_unbox(v_usedLetOnly_992_);
v_skipConstInApp_boxed_1005_ = lean_unbox(v_skipConstInApp_993_);
v_skipInstances_boxed_1006_ = lean_unbox(v_skipInstances_994_);
v_res_1007_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(v_fvars_989_, v_pre_990_, v_post_991_, v_usedLetOnly_boxed_1004_, v_skipConstInApp_boxed_1005_, v_skipInstances_boxed_1006_, v_postApp_995_, v_body_996_, v_x_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(lean_object* v_pre_1008_, lean_object* v_post_1009_, uint8_t v_usedLetOnly_1010_, uint8_t v_skipConstInApp_1011_, uint8_t v_skipInstances_1012_, lean_object* v_postApp_1013_, lean_object* v_fvars_1014_, lean_object* v_e_1015_, lean_object* v_a_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
if (lean_obj_tag(v_e_1015_) == 8)
{
lean_object* v_declName_1022_; lean_object* v_type_1023_; lean_object* v_value_1024_; lean_object* v_body_1025_; uint8_t v_nondep_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___f_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v_declName_1022_ = lean_ctor_get(v_e_1015_, 0);
lean_inc(v_declName_1022_);
v_type_1023_ = lean_ctor_get(v_e_1015_, 1);
lean_inc_ref(v_type_1023_);
v_value_1024_ = lean_ctor_get(v_e_1015_, 2);
lean_inc_ref(v_value_1024_);
v_body_1025_ = lean_ctor_get(v_e_1015_, 3);
lean_inc_ref(v_body_1025_);
v_nondep_1026_ = lean_ctor_get_uint8(v_e_1015_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1015_, 4);
v___x_1027_ = lean_box(v_usedLetOnly_1010_);
v___x_1028_ = lean_box(v_skipConstInApp_1011_);
v___x_1029_ = lean_box(v_skipInstances_1012_);
lean_inc_ref_n(v_postApp_1013_, 2);
lean_inc_ref_n(v_post_1009_, 2);
lean_inc_ref_n(v_pre_1008_, 2);
lean_inc_ref(v_fvars_1014_);
v___f_1030_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed), 15, 8);
lean_closure_set(v___f_1030_, 0, v_fvars_1014_);
lean_closure_set(v___f_1030_, 1, v_pre_1008_);
lean_closure_set(v___f_1030_, 2, v_post_1009_);
lean_closure_set(v___f_1030_, 3, v___x_1027_);
lean_closure_set(v___f_1030_, 4, v___x_1028_);
lean_closure_set(v___f_1030_, 5, v___x_1029_);
lean_closure_set(v___f_1030_, 6, v_postApp_1013_);
lean_closure_set(v___f_1030_, 7, v_body_1025_);
v___x_1031_ = lean_expr_instantiate_rev(v_type_1023_, v_fvars_1014_);
lean_dec_ref(v_type_1023_);
v___x_1032_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1008_, v_post_1009_, v_usedLetOnly_1010_, v_skipConstInApp_1011_, v_skipInstances_1012_, v_postApp_1013_, v___x_1031_, v_a_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___x_1032_, 1);
v___x_1034_ = lean_expr_instantiate_rev(v_value_1024_, v_fvars_1014_);
lean_dec_ref(v_fvars_1014_);
lean_dec_ref(v_value_1024_);
v___x_1035_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1008_, v_post_1009_, v_usedLetOnly_1010_, v_skipConstInApp_1011_, v_skipInstances_1012_, v_postApp_1013_, v___x_1034_, v_a_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; uint8_t v___x_1037_; lean_object* v___x_1038_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___x_1035_, 1);
v___x_1037_ = 0;
v___x_1038_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_declName_1022_, v_a_1033_, v_a_1036_, v___f_1030_, v_nondep_1026_, v___x_1037_, v_a_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
return v___x_1038_;
}
else
{
lean_dec(v_a_1033_);
lean_dec_ref(v___f_1030_);
lean_dec(v_declName_1022_);
return v___x_1035_;
}
}
else
{
lean_dec_ref(v___f_1030_);
lean_dec_ref(v_value_1024_);
lean_dec(v_declName_1022_);
lean_dec_ref(v_fvars_1014_);
lean_dec_ref(v_postApp_1013_);
lean_dec_ref(v_post_1009_);
lean_dec_ref(v_pre_1008_);
return v___x_1032_;
}
}
else
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_expr_instantiate_rev(v_e_1015_, v_fvars_1014_);
lean_dec_ref(v_e_1015_);
lean_inc_ref(v_postApp_1013_);
lean_inc_ref(v_post_1009_);
lean_inc_ref(v_pre_1008_);
v___x_1040_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1008_, v_post_1009_, v_usedLetOnly_1010_, v_skipConstInApp_1011_, v_skipInstances_1012_, v_postApp_1013_, v___x_1039_, v_a_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; uint8_t v___x_1042_; uint8_t v___x_1043_; lean_object* v___x_1044_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1040_, 1);
v___x_1042_ = 0;
v___x_1043_ = 1;
v___x_1044_ = l_Lean_Meta_mkLetFVars(v_fvars_1014_, v_a_1041_, v_usedLetOnly_1010_, v___x_1042_, v___x_1043_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec_ref(v_fvars_1014_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1046_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref_known(v___x_1044_, 1);
v___x_1046_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_1008_, v_post_1009_, v_usedLetOnly_1010_, v_skipConstInApp_1011_, v_skipInstances_1012_, v_postApp_1013_, v_a_1045_, v_a_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
return v___x_1046_;
}
else
{
lean_dec_ref(v_postApp_1013_);
lean_dec_ref(v_post_1009_);
lean_dec_ref(v_pre_1008_);
return v___x_1044_;
}
}
else
{
lean_dec_ref(v_fvars_1014_);
lean_dec_ref(v_postApp_1013_);
lean_dec_ref(v_post_1009_);
lean_dec_ref(v_pre_1008_);
return v___x_1040_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(lean_object* v_pre_1047_, lean_object* v_post_1048_, uint8_t v_usedLetOnly_1049_, uint8_t v_skipConstInApp_1050_, uint8_t v_skipInstances_1051_, lean_object* v_postApp_1052_, size_t v_sz_1053_, size_t v_i_1054_, lean_object* v_bs_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
uint8_t v___x_1062_; 
v___x_1062_ = lean_usize_dec_lt(v_i_1054_, v_sz_1053_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; 
lean_dec_ref(v_postApp_1052_);
lean_dec_ref(v_post_1048_);
lean_dec_ref(v_pre_1047_);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v_bs_1055_);
return v___x_1063_;
}
else
{
lean_object* v_v_1064_; lean_object* v___x_1065_; lean_object* v_bs_x27_1066_; lean_object* v___x_1067_; 
v_v_1064_ = lean_array_uget(v_bs_1055_, v_i_1054_);
v___x_1065_ = lean_unsigned_to_nat(0u);
v_bs_x27_1066_ = lean_array_uset(v_bs_1055_, v_i_1054_, v___x_1065_);
lean_inc_ref(v_postApp_1052_);
lean_inc_ref(v_post_1048_);
lean_inc_ref(v_pre_1047_);
v___x_1067_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1047_, v_post_1048_, v_usedLetOnly_1049_, v_skipConstInApp_1050_, v_skipInstances_1051_, v_postApp_1052_, v_v_1064_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; size_t v___x_1069_; size_t v___x_1070_; lean_object* v___x_1071_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1067_, 1);
v___x_1069_ = ((size_t)1ULL);
v___x_1070_ = lean_usize_add(v_i_1054_, v___x_1069_);
v___x_1071_ = lean_array_uset(v_bs_x27_1066_, v_i_1054_, v_a_1068_);
v_i_1054_ = v___x_1070_;
v_bs_1055_ = v___x_1071_;
goto _start;
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec_ref(v_bs_x27_1066_);
lean_dec_ref(v_postApp_1052_);
lean_dec_ref(v_post_1048_);
lean_dec_ref(v_pre_1047_);
v_a_1073_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1067_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1067_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__0(lean_object* v_pre_1081_, lean_object* v_post_1082_, uint8_t v_usedLetOnly_1083_, uint8_t v_skipConstInApp_1084_, uint8_t v_skipInstances_1085_, lean_object* v_postApp_1086_, lean_object* v___x_1087_, lean_object* v___y_1088_, lean_object* v_b_1089_, lean_object* v_a_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1081_, v_post_1082_, v_usedLetOnly_1083_, v_skipConstInApp_1084_, v_skipInstances_1085_, v_postApp_1086_, v___x_1087_, v___y_1088_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1106_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1099_ = v___x_1096_;
v_isShared_1100_ = v_isSharedCheck_1106_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1096_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1106_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
v___x_1101_ = lean_array_fset(v_b_1089_, v_a_1090_, v_a_1097_);
v___x_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1102_);
v___x_1104_ = v___x_1099_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec_ref(v_b_1089_);
v_a_1107_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1096_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1096_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__0___boxed(lean_object* v_pre_1115_, lean_object* v_post_1116_, lean_object* v_usedLetOnly_1117_, lean_object* v_skipConstInApp_1118_, lean_object* v_skipInstances_1119_, lean_object* v_postApp_1120_, lean_object* v___x_1121_, lean_object* v___y_1122_, lean_object* v_b_1123_, lean_object* v_a_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
uint8_t v_usedLetOnly_boxed_1130_; uint8_t v_skipConstInApp_boxed_1131_; uint8_t v_skipInstances_boxed_1132_; lean_object* v_res_1133_; 
v_usedLetOnly_boxed_1130_ = lean_unbox(v_usedLetOnly_1117_);
v_skipConstInApp_boxed_1131_ = lean_unbox(v_skipConstInApp_1118_);
v_skipInstances_boxed_1132_ = lean_unbox(v_skipInstances_1119_);
v_res_1133_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__0(v_pre_1115_, v_post_1116_, v_usedLetOnly_boxed_1130_, v_skipConstInApp_boxed_1131_, v_skipInstances_boxed_1132_, v_postApp_1120_, v___x_1121_, v___y_1122_, v_b_1123_, v_a_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v_a_1124_);
lean_dec(v___y_1122_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(lean_object* v_upperBound_1134_, lean_object* v___x_1135_, lean_object* v_pre_1136_, lean_object* v_post_1137_, uint8_t v_usedLetOnly_1138_, uint8_t v_skipConstInApp_1139_, uint8_t v_skipInstances_1140_, lean_object* v_postApp_1141_, lean_object* v_a_1142_, lean_object* v_b_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___y_1151_; uint8_t v___x_1174_; 
v___x_1174_ = lean_nat_dec_lt(v_a_1142_, v_upperBound_1134_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; 
lean_dec(v_a_1142_);
lean_dec_ref(v_postApp_1141_);
lean_dec_ref(v_post_1137_);
lean_dec_ref(v_pre_1136_);
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v_b_1143_);
return v___x_1175_;
}
else
{
lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1176_ = lean_array_fget_borrowed(v_b_1143_, v_a_1142_);
v___x_1177_ = lean_array_get_size(v___x_1135_);
v___x_1178_ = lean_nat_dec_lt(v_a_1142_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___f_1182_; 
lean_inc(v___x_1176_);
v___x_1179_ = lean_box(v_usedLetOnly_1138_);
v___x_1180_ = lean_box(v_skipConstInApp_1139_);
v___x_1181_ = lean_box(v_skipInstances_1140_);
lean_inc(v_a_1142_);
lean_inc(v___y_1144_);
lean_inc_ref(v_postApp_1141_);
lean_inc_ref(v_post_1137_);
lean_inc_ref(v_pre_1136_);
v___f_1182_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__0___boxed), 15, 10);
lean_closure_set(v___f_1182_, 0, v_pre_1136_);
lean_closure_set(v___f_1182_, 1, v_post_1137_);
lean_closure_set(v___f_1182_, 2, v___x_1179_);
lean_closure_set(v___f_1182_, 3, v___x_1180_);
lean_closure_set(v___f_1182_, 4, v___x_1181_);
lean_closure_set(v___f_1182_, 5, v_postApp_1141_);
lean_closure_set(v___f_1182_, 6, v___x_1176_);
lean_closure_set(v___f_1182_, 7, v___y_1144_);
lean_closure_set(v___f_1182_, 8, v_b_1143_);
lean_closure_set(v___f_1182_, 9, v_a_1142_);
v___y_1151_ = v___f_1182_;
goto v___jp_1150_;
}
else
{
lean_object* v___x_1183_; uint8_t v_isInstance_1184_; 
v___x_1183_ = lean_array_fget_borrowed(v___x_1135_, v_a_1142_);
v_isInstance_1184_ = lean_ctor_get_uint8(v___x_1183_, sizeof(void*)*1 + 4);
if (v_isInstance_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___f_1188_; 
lean_inc(v___x_1176_);
v___x_1185_ = lean_box(v_usedLetOnly_1138_);
v___x_1186_ = lean_box(v_skipConstInApp_1139_);
v___x_1187_ = lean_box(v_skipInstances_1140_);
lean_inc(v_a_1142_);
lean_inc(v___y_1144_);
lean_inc_ref(v_postApp_1141_);
lean_inc_ref(v_post_1137_);
lean_inc_ref(v_pre_1136_);
v___f_1188_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__0___boxed), 15, 10);
lean_closure_set(v___f_1188_, 0, v_pre_1136_);
lean_closure_set(v___f_1188_, 1, v_post_1137_);
lean_closure_set(v___f_1188_, 2, v___x_1185_);
lean_closure_set(v___f_1188_, 3, v___x_1186_);
lean_closure_set(v___f_1188_, 4, v___x_1187_);
lean_closure_set(v___f_1188_, 5, v_postApp_1141_);
lean_closure_set(v___f_1188_, 6, v___x_1176_);
lean_closure_set(v___f_1188_, 7, v___y_1144_);
lean_closure_set(v___f_1188_, 8, v_b_1143_);
lean_closure_set(v___f_1188_, 9, v_a_1142_);
v___y_1151_ = v___f_1188_;
goto v___jp_1150_;
}
else
{
lean_object* v___x_1189_; lean_object* v___f_1190_; 
v___x_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1189_, 0, v_b_1143_);
v___f_1190_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1190_, 0, v___x_1189_);
v___y_1151_ = v___f_1190_;
goto v___jp_1150_;
}
}
}
v___jp_1150_:
{
lean_object* v___x_1152_; 
lean_inc(v___y_1148_);
lean_inc_ref(v___y_1147_);
lean_inc(v___y_1146_);
lean_inc_ref(v___y_1145_);
v___x_1152_ = lean_apply_5(v___y_1151_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, lean_box(0));
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1165_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1155_ = v___x_1152_;
v_isShared_1156_ = v_isSharedCheck_1165_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1165_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
if (lean_obj_tag(v_a_1153_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; 
lean_dec(v_a_1142_);
lean_dec_ref(v_postApp_1141_);
lean_dec_ref(v_post_1137_);
lean_dec_ref(v_pre_1136_);
v_a_1157_ = lean_ctor_get(v_a_1153_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v_a_1153_, 1);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v_a_1157_);
v___x_1159_ = v___x_1155_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
lean_del_object(v___x_1155_);
v_a_1161_ = lean_ctor_get(v_a_1153_, 0);
lean_inc(v_a_1161_);
lean_dec_ref_known(v_a_1153_, 1);
v___x_1162_ = lean_unsigned_to_nat(1u);
v___x_1163_ = lean_nat_add(v_a_1142_, v___x_1162_);
lean_dec(v_a_1142_);
v_a_1142_ = v___x_1163_;
v_b_1143_ = v_a_1161_;
goto _start;
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_dec(v_a_1142_);
lean_dec_ref(v_postApp_1141_);
lean_dec_ref(v_post_1137_);
lean_dec_ref(v_pre_1136_);
v_a_1166_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1152_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1152_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(uint8_t v_skipInstances_1191_, lean_object* v_pre_1192_, lean_object* v_post_1193_, uint8_t v_usedLetOnly_1194_, uint8_t v_skipConstInApp_1195_, lean_object* v_postApp_1196_, lean_object* v___y_1197_, lean_object* v_x_1198_, lean_object* v_x_1199_, lean_object* v_x_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_f_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; 
if (lean_obj_tag(v_x_1198_) == 5)
{
lean_object* v_fn_1260_; lean_object* v_arg_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v_fn_1260_ = lean_ctor_get(v_x_1198_, 0);
lean_inc_ref(v_fn_1260_);
v_arg_1261_ = lean_ctor_get(v_x_1198_, 1);
lean_inc_ref(v_arg_1261_);
lean_dec_ref_known(v_x_1198_, 2);
v___x_1262_ = lean_array_set(v_x_1199_, v_x_1200_, v_arg_1261_);
v___x_1263_ = lean_unsigned_to_nat(1u);
v___x_1264_ = lean_nat_sub(v_x_1200_, v___x_1263_);
lean_dec(v_x_1200_);
v_x_1198_ = v_fn_1260_;
v_x_1199_ = v___x_1262_;
v_x_1200_ = v___x_1264_;
goto _start;
}
else
{
lean_dec(v_x_1200_);
if (v_skipConstInApp_1195_ == 0)
{
goto v___jp_1257_;
}
else
{
uint8_t v___x_1266_; 
v___x_1266_ = l_Lean_Expr_isConst(v_x_1198_);
if (v___x_1266_ == 0)
{
goto v___jp_1257_;
}
else
{
v_f_1208_ = v_x_1198_;
v___y_1209_ = v___y_1201_;
v___y_1210_ = v___y_1202_;
v___y_1211_ = v___y_1203_;
v___y_1212_ = v___y_1204_;
v___y_1213_ = v___y_1205_;
goto v___jp_1207_;
}
}
}
v___jp_1207_:
{
if (v_skipInstances_1191_ == 0)
{
size_t v_sz_1214_; size_t v___x_1215_; lean_object* v___x_1216_; 
v_sz_1214_ = lean_array_size(v_x_1199_);
v___x_1215_ = ((size_t)0ULL);
lean_inc_ref(v_postApp_1196_);
lean_inc_ref(v_post_1193_);
lean_inc_ref(v_pre_1192_);
v___x_1216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1192_, v_post_1193_, v_usedLetOnly_1194_, v_skipConstInApp_1195_, v_skipInstances_1191_, v_postApp_1196_, v_sz_1214_, v___x_1215_, v_x_1199_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref_known(v___x_1216_, 1);
v___x_1218_ = l_Lean_mkAppN(v_f_1208_, v_a_1217_);
lean_dec(v_a_1217_);
lean_inc_ref(v_postApp_1196_);
lean_inc(v___y_1213_);
lean_inc_ref(v___y_1212_);
lean_inc(v___y_1211_);
lean_inc_ref(v___y_1210_);
v___x_1219_ = lean_apply_7(v_postApp_1196_, v___y_1197_, v___x_1218_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, lean_box(0));
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1221_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v___x_1219_, 1);
v___x_1221_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_1192_, v_post_1193_, v_usedLetOnly_1194_, v_skipConstInApp_1195_, v_skipInstances_1191_, v_postApp_1196_, v_a_1220_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
return v___x_1221_;
}
else
{
lean_dec_ref(v_postApp_1196_);
lean_dec_ref(v_post_1193_);
lean_dec_ref(v_pre_1192_);
return v___x_1219_;
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec_ref(v_f_1208_);
lean_dec_ref(v___y_1197_);
lean_dec_ref(v_postApp_1196_);
lean_dec_ref(v_post_1193_);
lean_dec_ref(v_pre_1192_);
v_a_1222_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1216_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1216_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_array_get_size(v_x_1199_);
lean_inc_ref(v_f_1208_);
v___x_1231_ = l_Lean_Meta_getFunInfoNArgs(v_f_1208_, v___x_1230_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v_paramInfo_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
lean_dec_ref_known(v___x_1231_, 1);
v_paramInfo_1233_ = lean_ctor_get(v_a_1232_, 0);
lean_inc_ref(v_paramInfo_1233_);
lean_dec(v_a_1232_);
v___x_1234_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_postApp_1196_);
lean_inc_ref(v_post_1193_);
lean_inc_ref(v_pre_1192_);
v___x_1235_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v___x_1230_, v_paramInfo_1233_, v_pre_1192_, v_post_1193_, v_usedLetOnly_1194_, v_skipConstInApp_1195_, v_skipInstances_1191_, v_postApp_1196_, v___x_1234_, v_x_1199_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec_ref(v_paramInfo_1233_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1236_);
lean_dec_ref_known(v___x_1235_, 1);
v___x_1237_ = l_Lean_mkAppN(v_f_1208_, v_a_1236_);
lean_dec(v_a_1236_);
lean_inc_ref(v_postApp_1196_);
lean_inc(v___y_1213_);
lean_inc_ref(v___y_1212_);
lean_inc(v___y_1211_);
lean_inc_ref(v___y_1210_);
v___x_1238_ = lean_apply_7(v_postApp_1196_, v___y_1197_, v___x_1237_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, lean_box(0));
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1240_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref_known(v___x_1238_, 1);
v___x_1240_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_1192_, v_post_1193_, v_usedLetOnly_1194_, v_skipConstInApp_1195_, v_skipInstances_1191_, v_postApp_1196_, v_a_1239_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
return v___x_1240_;
}
else
{
lean_dec_ref(v_postApp_1196_);
lean_dec_ref(v_post_1193_);
lean_dec_ref(v_pre_1192_);
return v___x_1238_;
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec_ref(v_f_1208_);
lean_dec_ref(v___y_1197_);
lean_dec_ref(v_postApp_1196_);
lean_dec_ref(v_post_1193_);
lean_dec_ref(v_pre_1192_);
v_a_1241_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1235_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1235_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec_ref(v_f_1208_);
lean_dec_ref(v_x_1199_);
lean_dec_ref(v___y_1197_);
lean_dec_ref(v_postApp_1196_);
lean_dec_ref(v_post_1193_);
lean_dec_ref(v_pre_1192_);
v_a_1249_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1231_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1231_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
v___jp_1257_:
{
lean_object* v___x_1258_; 
lean_inc_ref(v_postApp_1196_);
lean_inc_ref(v_post_1193_);
lean_inc_ref(v_pre_1192_);
v___x_1258_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1192_, v_post_1193_, v_usedLetOnly_1194_, v_skipConstInApp_1195_, v_skipInstances_1191_, v_postApp_1196_, v_x_1198_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref_known(v___x_1258_, 1);
v_f_1208_ = v_a_1259_;
v___y_1209_ = v___y_1201_;
v___y_1210_ = v___y_1202_;
v___y_1211_ = v___y_1203_;
v___y_1212_ = v___y_1204_;
v___y_1213_ = v___y_1205_;
goto v___jp_1207_;
}
else
{
lean_dec_ref(v_x_1199_);
lean_dec_ref(v___y_1197_);
lean_dec_ref(v_postApp_1196_);
lean_dec_ref(v_post_1193_);
lean_dec_ref(v_pre_1192_);
return v___x_1258_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(lean_object* v___x_1267_, lean_object* v_pre_1268_, lean_object* v_e_1269_, lean_object* v_post_1270_, uint8_t v_usedLetOnly_1271_, uint8_t v_skipConstInApp_1272_, uint8_t v_skipInstances_1273_, lean_object* v_postApp_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_Core_checkSystem(v___x_1267_, v___y_1278_, v___y_1279_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v___x_1282_; 
lean_dec_ref_known(v___x_1281_, 1);
lean_inc_ref(v_pre_1268_);
lean_inc(v___y_1279_);
lean_inc_ref(v___y_1278_);
lean_inc(v___y_1277_);
lean_inc_ref(v___y_1276_);
lean_inc_ref(v_e_1269_);
v___x_1282_ = lean_apply_6(v_pre_1268_, v_e_1269_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, lean_box(0));
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1331_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1331_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1331_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___y_1288_; 
switch(lean_obj_tag(v_a_1283_))
{
case 0:
{
lean_object* v_e_1323_; lean_object* v___x_1325_; 
lean_dec_ref(v_postApp_1274_);
lean_dec_ref(v_post_1270_);
lean_dec_ref(v_e_1269_);
lean_dec_ref(v_pre_1268_);
v_e_1323_ = lean_ctor_get(v_a_1283_, 0);
lean_inc_ref(v_e_1323_);
lean_dec_ref_known(v_a_1283_, 1);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v_e_1323_);
v___x_1325_ = v___x_1285_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_e_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
case 1:
{
lean_object* v_e_1327_; lean_object* v___x_1328_; 
lean_del_object(v___x_1285_);
lean_dec_ref(v_e_1269_);
v_e_1327_ = lean_ctor_get(v_a_1283_, 0);
lean_inc_ref(v_e_1327_);
lean_dec_ref_known(v_a_1283_, 1);
v___x_1328_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v_postApp_1274_, v_e_1327_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1328_;
}
default: 
{
lean_object* v_e_x3f_1329_; 
lean_del_object(v___x_1285_);
v_e_x3f_1329_ = lean_ctor_get(v_a_1283_, 0);
lean_inc(v_e_x3f_1329_);
lean_dec_ref_known(v_a_1283_, 1);
if (lean_obj_tag(v_e_x3f_1329_) == 0)
{
v___y_1288_ = v_e_1269_;
goto v___jp_1287_;
}
else
{
lean_object* v_val_1330_; 
lean_dec_ref(v_e_1269_);
v_val_1330_ = lean_ctor_get(v_e_x3f_1329_, 0);
lean_inc(v_val_1330_);
lean_dec_ref_known(v_e_x3f_1329_, 1);
v___y_1288_ = v_val_1330_;
goto v___jp_1287_;
}
}
}
v___jp_1287_:
{
switch(lean_obj_tag(v___y_1288_))
{
case 7:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1290_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v_postApp_1274_, v___x_1289_, v___y_1288_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1290_;
}
case 6:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1292_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v_postApp_1274_, v___x_1291_, v___y_1288_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1292_;
}
case 8:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1294_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v_postApp_1274_, v___x_1293_, v___y_1288_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1294_;
}
case 5:
{
lean_object* v_dummy_1295_; lean_object* v_nargs_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v_dummy_1295_ = lean_obj_once(&l_Lean_Elab_WF_withAppN___closed__0, &l_Lean_Elab_WF_withAppN___closed__0_once, _init_l_Lean_Elab_WF_withAppN___closed__0);
v_nargs_1296_ = l_Lean_Expr_getAppNumArgs(v___y_1288_);
lean_inc(v_nargs_1296_);
v___x_1297_ = lean_mk_array(v_nargs_1296_, v_dummy_1295_);
v___x_1298_ = lean_unsigned_to_nat(1u);
v___x_1299_ = lean_nat_sub(v_nargs_1296_, v___x_1298_);
lean_dec(v_nargs_1296_);
lean_inc_ref(v___y_1288_);
v___x_1300_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_1273_, v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_postApp_1274_, v___y_1288_, v___y_1288_, v___x_1297_, v___x_1299_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1300_;
}
case 10:
{
lean_object* v_data_1301_; lean_object* v_expr_1302_; lean_object* v___x_1303_; 
v_data_1301_ = lean_ctor_get(v___y_1288_, 0);
v_expr_1302_ = lean_ctor_get(v___y_1288_, 1);
lean_inc_ref(v_expr_1302_);
lean_inc_ref(v_postApp_1274_);
lean_inc_ref(v_post_1270_);
lean_inc_ref(v_pre_1268_);
v___x_1303_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v_postApp_1274_, v_expr_1302_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; size_t v___x_1305_; size_t v___x_1306_; uint8_t v___x_1307_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1303_, 1);
v___x_1305_ = lean_ptr_addr(v_expr_1302_);
v___x_1306_ = lean_ptr_addr(v_a_1304_);
v___x_1307_ = lean_usize_dec_eq(v___x_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
lean_inc(v_data_1301_);
lean_dec_ref_known(v___y_1288_, 2);
v___x_1308_ = l_Lean_Expr_mdata___override(v_data_1301_, v_a_1304_);
v___x_1309_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v_postApp_1274_, v___x_1308_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1309_;
}
else
{
lean_object* v___x_1310_; 
lean_dec(v_a_1304_);
v___x_1310_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v_postApp_1274_, v___y_1288_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1310_;
}
}
else
{
lean_dec_ref_known(v___y_1288_, 2);
lean_dec_ref(v_postApp_1274_);
lean_dec_ref(v_post_1270_);
lean_dec_ref(v_pre_1268_);
return v___x_1303_;
}
}
case 11:
{
lean_object* v_typeName_1311_; lean_object* v_idx_1312_; lean_object* v_struct_1313_; lean_object* v___x_1314_; 
v_typeName_1311_ = lean_ctor_get(v___y_1288_, 0);
v_idx_1312_ = lean_ctor_get(v___y_1288_, 1);
v_struct_1313_ = lean_ctor_get(v___y_1288_, 2);
lean_inc_ref(v_struct_1313_);
lean_inc_ref(v_postApp_1274_);
lean_inc_ref(v_post_1270_);
lean_inc_ref(v_pre_1268_);
v___x_1314_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v_postApp_1274_, v_struct_1313_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; size_t v___x_1316_; size_t v___x_1317_; uint8_t v___x_1318_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1315_);
lean_dec_ref_known(v___x_1314_, 1);
v___x_1316_ = lean_ptr_addr(v_struct_1313_);
v___x_1317_ = lean_ptr_addr(v_a_1315_);
v___x_1318_ = lean_usize_dec_eq(v___x_1316_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
lean_inc(v_idx_1312_);
lean_inc(v_typeName_1311_);
lean_dec_ref_known(v___y_1288_, 3);
v___x_1319_ = l_Lean_Expr_proj___override(v_typeName_1311_, v_idx_1312_, v_a_1315_);
v___x_1320_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v_postApp_1274_, v___x_1319_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1320_;
}
else
{
lean_object* v___x_1321_; 
lean_dec(v_a_1315_);
v___x_1321_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v_postApp_1274_, v___y_1288_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1321_;
}
}
else
{
lean_dec_ref_known(v___y_1288_, 3);
lean_dec_ref(v_postApp_1274_);
lean_dec_ref(v_post_1270_);
lean_dec_ref(v_pre_1268_);
return v___x_1314_;
}
}
default: 
{
lean_object* v___x_1322_; 
v___x_1322_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v_postApp_1274_, v___y_1288_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1322_;
}
}
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_dec_ref(v_postApp_1274_);
lean_dec_ref(v_post_1270_);
lean_dec_ref(v_e_1269_);
lean_dec_ref(v_pre_1268_);
v_a_1332_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1282_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1282_);
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
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
lean_dec_ref(v_postApp_1274_);
lean_dec_ref(v_post_1270_);
lean_dec_ref(v_e_1269_);
lean_dec_ref(v_pre_1268_);
v_a_1340_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1281_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1281_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed(lean_object* v___x_1348_, lean_object* v_pre_1349_, lean_object* v_e_1350_, lean_object* v_post_1351_, lean_object* v_usedLetOnly_1352_, lean_object* v_skipConstInApp_1353_, lean_object* v_skipInstances_1354_, lean_object* v_postApp_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
uint8_t v_usedLetOnly_boxed_1362_; uint8_t v_skipConstInApp_boxed_1363_; uint8_t v_skipInstances_boxed_1364_; lean_object* v_res_1365_; 
v_usedLetOnly_boxed_1362_ = lean_unbox(v_usedLetOnly_1352_);
v_skipConstInApp_boxed_1363_ = lean_unbox(v_skipConstInApp_1353_);
v_skipInstances_boxed_1364_ = lean_unbox(v_skipInstances_1354_);
v_res_1365_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(v___x_1348_, v_pre_1349_, v_e_1350_, v_post_1351_, v_usedLetOnly_boxed_1362_, v_skipConstInApp_boxed_1363_, v_skipInstances_boxed_1364_, v_postApp_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(lean_object* v_pre_1366_, lean_object* v_post_1367_, uint8_t v_usedLetOnly_1368_, uint8_t v_skipConstInApp_1369_, uint8_t v_skipInstances_1370_, lean_object* v_postApp_1371_, lean_object* v_e_1372_, lean_object* v_a_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
lean_inc(v_a_1373_);
v___x_1379_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1379_, 0, lean_box(0));
lean_closure_set(v___x_1379_, 1, lean_box(0));
lean_closure_set(v___x_1379_, 2, v_a_1373_);
v___x_1380_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___x_1379_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1415_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1415_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1415_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___redArg(v_a_1381_, v_e_1372_);
lean_dec(v_a_1381_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___f_1390_; lean_object* v___x_1391_; 
lean_del_object(v___x_1383_);
v___x_1386_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0));
v___x_1387_ = lean_box(v_usedLetOnly_1368_);
v___x_1388_ = lean_box(v_skipConstInApp_1369_);
v___x_1389_ = lean_box(v_skipInstances_1370_);
lean_inc_ref(v_e_1372_);
v___f_1390_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed), 14, 8);
lean_closure_set(v___f_1390_, 0, v___x_1386_);
lean_closure_set(v___f_1390_, 1, v_pre_1366_);
lean_closure_set(v___f_1390_, 2, v_e_1372_);
lean_closure_set(v___f_1390_, 3, v_post_1367_);
lean_closure_set(v___f_1390_, 4, v___x_1387_);
lean_closure_set(v___f_1390_, 5, v___x_1388_);
lean_closure_set(v___f_1390_, 6, v___x_1389_);
lean_closure_set(v___f_1390_, 7, v_postApp_1371_);
v___x_1391_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v___f_1390_, v_a_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___f_1393_; lean_object* v___x_1394_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc_n(v_a_1392_, 2);
lean_dec_ref_known(v___x_1391_, 1);
lean_inc(v_a_1373_);
v___f_1393_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1393_, 0, v_a_1373_);
lean_closure_set(v___f_1393_, 1, v_e_1372_);
lean_closure_set(v___f_1393_, 2, v_a_1392_);
v___x_1394_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___f_1393_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; 
v_unused_1402_ = lean_ctor_get(v___x_1394_, 0);
lean_dec(v_unused_1402_);
v___x_1396_ = v___x_1394_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_dec(v___x_1394_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v_a_1392_);
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1392_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
lean_dec(v_a_1392_);
v_a_1403_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1394_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1394_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
else
{
lean_dec_ref(v_e_1372_);
return v___x_1391_;
}
}
else
{
lean_object* v_val_1411_; lean_object* v___x_1413_; 
lean_dec_ref(v_e_1372_);
lean_dec_ref(v_postApp_1371_);
lean_dec_ref(v_post_1367_);
lean_dec_ref(v_pre_1366_);
v_val_1411_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_val_1411_);
lean_dec_ref_known(v___x_1385_, 1);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v_val_1411_);
v___x_1413_ = v___x_1383_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_val_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec_ref(v_e_1372_);
lean_dec_ref(v_postApp_1371_);
lean_dec_ref(v_post_1367_);
lean_dec_ref(v_pre_1366_);
v_a_1416_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1380_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1380_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(lean_object* v_pre_1424_, lean_object* v_post_1425_, uint8_t v_usedLetOnly_1426_, uint8_t v_skipConstInApp_1427_, uint8_t v_skipInstances_1428_, lean_object* v_postApp_1429_, lean_object* v_fvars_1430_, lean_object* v_e_1431_, lean_object* v_a_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
if (lean_obj_tag(v_e_1431_) == 7)
{
lean_object* v_binderName_1438_; lean_object* v_binderType_1439_; lean_object* v_body_1440_; uint8_t v_binderInfo_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___f_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v_binderName_1438_ = lean_ctor_get(v_e_1431_, 0);
lean_inc(v_binderName_1438_);
v_binderType_1439_ = lean_ctor_get(v_e_1431_, 1);
lean_inc_ref(v_binderType_1439_);
v_body_1440_ = lean_ctor_get(v_e_1431_, 2);
lean_inc_ref(v_body_1440_);
v_binderInfo_1441_ = lean_ctor_get_uint8(v_e_1431_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1431_, 3);
v___x_1442_ = lean_box(v_usedLetOnly_1426_);
v___x_1443_ = lean_box(v_skipConstInApp_1427_);
v___x_1444_ = lean_box(v_skipInstances_1428_);
lean_inc_ref(v_postApp_1429_);
lean_inc_ref(v_post_1425_);
lean_inc_ref(v_pre_1424_);
lean_inc_ref(v_fvars_1430_);
v___f_1445_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed), 15, 8);
lean_closure_set(v___f_1445_, 0, v_fvars_1430_);
lean_closure_set(v___f_1445_, 1, v_pre_1424_);
lean_closure_set(v___f_1445_, 2, v_post_1425_);
lean_closure_set(v___f_1445_, 3, v___x_1442_);
lean_closure_set(v___f_1445_, 4, v___x_1443_);
lean_closure_set(v___f_1445_, 5, v___x_1444_);
lean_closure_set(v___f_1445_, 6, v_postApp_1429_);
lean_closure_set(v___f_1445_, 7, v_body_1440_);
v___x_1446_ = lean_expr_instantiate_rev(v_binderType_1439_, v_fvars_1430_);
lean_dec_ref(v_fvars_1430_);
lean_dec_ref(v_binderType_1439_);
v___x_1447_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1424_, v_post_1425_, v_usedLetOnly_1426_, v_skipConstInApp_1427_, v_skipInstances_1428_, v_postApp_1429_, v___x_1446_, v_a_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; uint8_t v___x_1449_; lean_object* v___x_1450_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1447_, 1);
v___x_1449_ = 0;
v___x_1450_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_1438_, v_binderInfo_1441_, v_a_1448_, v___f_1445_, v___x_1449_, v_a_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
return v___x_1450_;
}
else
{
lean_dec_ref(v___f_1445_);
lean_dec(v_binderName_1438_);
return v___x_1447_;
}
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_expr_instantiate_rev(v_e_1431_, v_fvars_1430_);
lean_dec_ref(v_e_1431_);
lean_inc_ref(v_postApp_1429_);
lean_inc_ref(v_post_1425_);
lean_inc_ref(v_pre_1424_);
v___x_1452_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1424_, v_post_1425_, v_usedLetOnly_1426_, v_skipConstInApp_1427_, v_skipInstances_1428_, v_postApp_1429_, v___x_1451_, v_a_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; uint8_t v___x_1454_; uint8_t v___x_1455_; uint8_t v___x_1456_; lean_object* v___x_1457_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_a_1453_);
lean_dec_ref_known(v___x_1452_, 1);
v___x_1454_ = 0;
v___x_1455_ = 1;
v___x_1456_ = 1;
v___x_1457_ = l_Lean_Meta_mkForallFVars(v_fvars_1430_, v_a_1453_, v___x_1454_, v_usedLetOnly_1426_, v___x_1455_, v___x_1456_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec_ref(v_fvars_1430_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1459_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v___x_1459_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_1424_, v_post_1425_, v_usedLetOnly_1426_, v_skipConstInApp_1427_, v_skipInstances_1428_, v_postApp_1429_, v_a_1458_, v_a_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
return v___x_1459_;
}
else
{
lean_dec_ref(v_postApp_1429_);
lean_dec_ref(v_post_1425_);
lean_dec_ref(v_pre_1424_);
return v___x_1457_;
}
}
else
{
lean_dec_ref(v_fvars_1430_);
lean_dec_ref(v_postApp_1429_);
lean_dec_ref(v_post_1425_);
lean_dec_ref(v_pre_1424_);
return v___x_1452_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(lean_object* v_fvars_1460_, lean_object* v_pre_1461_, lean_object* v_post_1462_, uint8_t v_usedLetOnly_1463_, uint8_t v_skipConstInApp_1464_, uint8_t v_skipInstances_1465_, lean_object* v_postApp_1466_, lean_object* v_body_1467_, lean_object* v_x_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = lean_array_push(v_fvars_1460_, v_x_1468_);
v___x_1476_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1461_, v_post_1462_, v_usedLetOnly_1463_, v_skipConstInApp_1464_, v_skipInstances_1465_, v_postApp_1466_, v___x_1475_, v_body_1467_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___boxed(lean_object* v_pre_1477_, lean_object* v_post_1478_, lean_object* v_usedLetOnly_1479_, lean_object* v_skipConstInApp_1480_, lean_object* v_skipInstances_1481_, lean_object* v_postApp_1482_, lean_object* v_e_1483_, lean_object* v_a_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
uint8_t v_usedLetOnly_boxed_1490_; uint8_t v_skipConstInApp_boxed_1491_; uint8_t v_skipInstances_boxed_1492_; lean_object* v_res_1493_; 
v_usedLetOnly_boxed_1490_ = lean_unbox(v_usedLetOnly_1479_);
v_skipConstInApp_boxed_1491_ = lean_unbox(v_skipConstInApp_1480_);
v_skipInstances_boxed_1492_ = lean_unbox(v_skipInstances_1481_);
v_res_1493_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_1477_, v_post_1478_, v_usedLetOnly_boxed_1490_, v_skipConstInApp_boxed_1491_, v_skipInstances_boxed_1492_, v_postApp_1482_, v_e_1483_, v_a_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v_a_1484_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7___boxed(lean_object* v_pre_1494_, lean_object* v_post_1495_, lean_object* v_usedLetOnly_1496_, lean_object* v_skipConstInApp_1497_, lean_object* v_skipInstances_1498_, lean_object* v_postApp_1499_, lean_object* v_sz_1500_, lean_object* v_i_1501_, lean_object* v_bs_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
uint8_t v_usedLetOnly_boxed_1509_; uint8_t v_skipConstInApp_boxed_1510_; uint8_t v_skipInstances_boxed_1511_; size_t v_sz_boxed_1512_; size_t v_i_boxed_1513_; lean_object* v_res_1514_; 
v_usedLetOnly_boxed_1509_ = lean_unbox(v_usedLetOnly_1496_);
v_skipConstInApp_boxed_1510_ = lean_unbox(v_skipConstInApp_1497_);
v_skipInstances_boxed_1511_ = lean_unbox(v_skipInstances_1498_);
v_sz_boxed_1512_ = lean_unbox_usize(v_sz_1500_);
lean_dec(v_sz_1500_);
v_i_boxed_1513_ = lean_unbox_usize(v_i_1501_);
lean_dec(v_i_1501_);
v_res_1514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1494_, v_post_1495_, v_usedLetOnly_boxed_1509_, v_skipConstInApp_boxed_1510_, v_skipInstances_boxed_1511_, v_postApp_1499_, v_sz_boxed_1512_, v_i_boxed_1513_, v_bs_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___boxed(lean_object* v_pre_1515_, lean_object* v_post_1516_, lean_object* v_usedLetOnly_1517_, lean_object* v_skipConstInApp_1518_, lean_object* v_skipInstances_1519_, lean_object* v_postApp_1520_, lean_object* v_e_1521_, lean_object* v_a_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
uint8_t v_usedLetOnly_boxed_1528_; uint8_t v_skipConstInApp_boxed_1529_; uint8_t v_skipInstances_boxed_1530_; lean_object* v_res_1531_; 
v_usedLetOnly_boxed_1528_ = lean_unbox(v_usedLetOnly_1517_);
v_skipConstInApp_boxed_1529_ = lean_unbox(v_skipConstInApp_1518_);
v_skipInstances_boxed_1530_ = lean_unbox(v_skipInstances_1519_);
v_res_1531_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1515_, v_post_1516_, v_usedLetOnly_boxed_1528_, v_skipConstInApp_boxed_1529_, v_skipInstances_boxed_1530_, v_postApp_1520_, v_e_1521_, v_a_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v_a_1522_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___boxed(lean_object* v_pre_1532_, lean_object* v_post_1533_, lean_object* v_usedLetOnly_1534_, lean_object* v_skipConstInApp_1535_, lean_object* v_skipInstances_1536_, lean_object* v_postApp_1537_, lean_object* v_fvars_1538_, lean_object* v_e_1539_, lean_object* v_a_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
uint8_t v_usedLetOnly_boxed_1546_; uint8_t v_skipConstInApp_boxed_1547_; uint8_t v_skipInstances_boxed_1548_; lean_object* v_res_1549_; 
v_usedLetOnly_boxed_1546_ = lean_unbox(v_usedLetOnly_1534_);
v_skipConstInApp_boxed_1547_ = lean_unbox(v_skipConstInApp_1535_);
v_skipInstances_boxed_1548_ = lean_unbox(v_skipInstances_1536_);
v_res_1549_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1532_, v_post_1533_, v_usedLetOnly_boxed_1546_, v_skipConstInApp_boxed_1547_, v_skipInstances_boxed_1548_, v_postApp_1537_, v_fvars_1538_, v_e_1539_, v_a_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v_a_1540_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___boxed(lean_object* v_pre_1550_, lean_object* v_post_1551_, lean_object* v_usedLetOnly_1552_, lean_object* v_skipConstInApp_1553_, lean_object* v_skipInstances_1554_, lean_object* v_postApp_1555_, lean_object* v_fvars_1556_, lean_object* v_e_1557_, lean_object* v_a_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
uint8_t v_usedLetOnly_boxed_1564_; uint8_t v_skipConstInApp_boxed_1565_; uint8_t v_skipInstances_boxed_1566_; lean_object* v_res_1567_; 
v_usedLetOnly_boxed_1564_ = lean_unbox(v_usedLetOnly_1552_);
v_skipConstInApp_boxed_1565_ = lean_unbox(v_skipConstInApp_1553_);
v_skipInstances_boxed_1566_ = lean_unbox(v_skipInstances_1554_);
v_res_1567_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1550_, v_post_1551_, v_usedLetOnly_boxed_1564_, v_skipConstInApp_boxed_1565_, v_skipInstances_boxed_1566_, v_postApp_1555_, v_fvars_1556_, v_e_1557_, v_a_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v_a_1558_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___boxed(lean_object* v_pre_1568_, lean_object* v_post_1569_, lean_object* v_usedLetOnly_1570_, lean_object* v_skipConstInApp_1571_, lean_object* v_skipInstances_1572_, lean_object* v_postApp_1573_, lean_object* v_fvars_1574_, lean_object* v_e_1575_, lean_object* v_a_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
uint8_t v_usedLetOnly_boxed_1582_; uint8_t v_skipConstInApp_boxed_1583_; uint8_t v_skipInstances_boxed_1584_; lean_object* v_res_1585_; 
v_usedLetOnly_boxed_1582_ = lean_unbox(v_usedLetOnly_1570_);
v_skipConstInApp_boxed_1583_ = lean_unbox(v_skipConstInApp_1571_);
v_skipInstances_boxed_1584_ = lean_unbox(v_skipInstances_1572_);
v_res_1585_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1568_, v_post_1569_, v_usedLetOnly_boxed_1582_, v_skipConstInApp_boxed_1583_, v_skipInstances_boxed_1584_, v_postApp_1573_, v_fvars_1574_, v_e_1575_, v_a_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v_a_1576_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___boxed(lean_object* v_upperBound_1586_, lean_object* v___x_1587_, lean_object* v_pre_1588_, lean_object* v_post_1589_, lean_object* v_usedLetOnly_1590_, lean_object* v_skipConstInApp_1591_, lean_object* v_skipInstances_1592_, lean_object* v_postApp_1593_, lean_object* v_a_1594_, lean_object* v_b_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
uint8_t v_usedLetOnly_boxed_1602_; uint8_t v_skipConstInApp_boxed_1603_; uint8_t v_skipInstances_boxed_1604_; lean_object* v_res_1605_; 
v_usedLetOnly_boxed_1602_ = lean_unbox(v_usedLetOnly_1590_);
v_skipConstInApp_boxed_1603_ = lean_unbox(v_skipConstInApp_1591_);
v_skipInstances_boxed_1604_ = lean_unbox(v_skipInstances_1592_);
v_res_1605_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_upperBound_1586_, v___x_1587_, v_pre_1588_, v_post_1589_, v_usedLetOnly_boxed_1602_, v_skipConstInApp_boxed_1603_, v_skipInstances_boxed_1604_, v_postApp_1593_, v_a_1594_, v_b_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___x_1587_);
lean_dec(v_upperBound_1586_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13___boxed(lean_object* v_skipInstances_1606_, lean_object* v_pre_1607_, lean_object* v_post_1608_, lean_object* v_usedLetOnly_1609_, lean_object* v_skipConstInApp_1610_, lean_object* v_postApp_1611_, lean_object* v___y_1612_, lean_object* v_x_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
uint8_t v_skipInstances_boxed_1622_; uint8_t v_usedLetOnly_boxed_1623_; uint8_t v_skipConstInApp_boxed_1624_; lean_object* v_res_1625_; 
v_skipInstances_boxed_1622_ = lean_unbox(v_skipInstances_1606_);
v_usedLetOnly_boxed_1623_ = lean_unbox(v_usedLetOnly_1609_);
v_skipConstInApp_boxed_1624_ = lean_unbox(v_skipConstInApp_1610_);
v_res_1625_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_boxed_1622_, v_pre_1607_, v_post_1608_, v_usedLetOnly_boxed_1623_, v_skipConstInApp_boxed_1624_, v_postApp_1611_, v___y_1612_, v_x_1613_, v_x_1614_, v_x_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__1(lean_object* v_x_1626_, lean_object* v_e_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1633_, 0, v_e_1627_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__1___boxed(lean_object* v_x_1634_, lean_object* v_e_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__1(v_x_1634_, v_e_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec_ref(v_x_1634_);
return v_res_1641_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1643_ = lean_box(0);
v___x_1644_ = lean_unsigned_to_nat(16u);
v___x_1645_ = lean_mk_array(v___x_1644_, v___x_1643_);
return v___x_1645_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1646_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1);
v___x_1647_ = lean_unsigned_to_nat(0u);
v___x_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
lean_ctor_set(v___x_1648_, 1, v___x_1646_);
return v___x_1648_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2);
v___x_1650_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1650_, 0, lean_box(0));
lean_closure_set(v___x_1650_, 1, lean_box(0));
lean_closure_set(v___x_1650_, 2, v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(lean_object* v_input_1651_, lean_object* v_pre_1652_, lean_object* v_post_1653_, uint8_t v_usedLetOnly_1654_, uint8_t v_skipConstInApp_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v___f_1661_; uint8_t v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v_a_1665_; lean_object* v___x_1666_; 
v___f_1661_ = ((lean_object*)(l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0));
v___x_1662_ = 0;
v___x_1663_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__3, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__3_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__3);
v___x_1664_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1663_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref(v___x_1664_);
v___x_1666_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1652_, v_post_1653_, v_usedLetOnly_1654_, v_skipConstInApp_1655_, v___x_1662_, v___f_1661_, v_input_1651_, v_a_1665_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref_known(v___x_1666_, 1);
v___x_1668_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1668_, 0, lean_box(0));
lean_closure_set(v___x_1668_, 1, lean_box(0));
lean_closure_set(v___x_1668_, 2, v_a_1665_);
v___x_1669_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1668_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; 
v_unused_1677_ = lean_ctor_get(v___x_1669_, 0);
lean_dec(v_unused_1677_);
v___x_1671_ = v___x_1669_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_dec(v___x_1669_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v_a_1667_);
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1667_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
else
{
lean_dec(v_a_1665_);
return v___x_1666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___boxed(lean_object* v_input_1678_, lean_object* v_pre_1679_, lean_object* v_post_1680_, lean_object* v_usedLetOnly_1681_, lean_object* v_skipConstInApp_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
uint8_t v_usedLetOnly_boxed_1688_; uint8_t v_skipConstInApp_boxed_1689_; lean_object* v_res_1690_; 
v_usedLetOnly_boxed_1688_ = lean_unbox(v_usedLetOnly_1681_);
v_skipConstInApp_boxed_1689_ = lean_unbox(v_skipConstInApp_1682_);
v_res_1690_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_input_1678_, v_pre_1679_, v_post_1680_, v_usedLetOnly_boxed_1688_, v_skipConstInApp_boxed_1689_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
return v_res_1690_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__1(void){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Array_instInhabited___redArg();
return v___x_1692_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__3(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__2));
v___x_1695_ = l_Lean_stringToMessageData(v___x_1694_);
return v___x_1695_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__5(void){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__4));
v___x_1698_ = l_Lean_stringToMessageData(v___x_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls(lean_object* v_fixedParamPerms_1699_, lean_object* v_argsPacker_1700_, lean_object* v_funNames_1701_, lean_object* v_newF_1702_, lean_object* v_e_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v___f_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___f_1709_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__0));
v___x_1710_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
lean_inc(v_a_1707_);
lean_inc_ref(v_a_1706_);
lean_inc(v_a_1705_);
lean_inc_ref(v_a_1704_);
lean_inc_ref(v_newF_1702_);
v___x_1711_ = lean_infer_type(v_newF_1702_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; uint8_t v___x_1723_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_a_1712_);
lean_dec_ref_known(v___x_1711_, 1);
v___x_1723_ = l_Lean_Expr_isForall(v_a_1712_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_dec_ref(v_e_1703_);
lean_dec_ref(v_funNames_1701_);
lean_dec_ref(v_argsPacker_1700_);
lean_dec_ref(v_fixedParamPerms_1699_);
v___x_1724_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__3, &l_Lean_Elab_WF_packCalls___closed__3_once, _init_l_Lean_Elab_WF_packCalls___closed__3);
v___x_1725_ = l_Lean_MessageData_ofExpr(v_newF_1702_);
v___x_1726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1724_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__5, &l_Lean_Elab_WF_packCalls___closed__5_once, _init_l_Lean_Elab_WF_packCalls___closed__5);
v___x_1728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1726_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = l_Lean_MessageData_ofExpr(v_a_1712_);
v___x_1730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1728_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
v___x_1731_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v___x_1730_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1731_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1731_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
else
{
v___y_1714_ = v_a_1704_;
v___y_1715_ = v_a_1705_;
v___y_1716_ = v_a_1706_;
v___y_1717_ = v_a_1707_;
goto v___jp_1713_;
}
v___jp_1713_:
{
lean_object* v___x_1718_; lean_object* v___f_1719_; uint8_t v___x_1720_; uint8_t v___x_1721_; lean_object* v___x_1722_; 
v___x_1718_ = l_Lean_Expr_bindingDomain_x21(v_a_1712_);
lean_dec(v_a_1712_);
v___f_1719_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packCalls___lam__2___boxed), 12, 6);
lean_closure_set(v___f_1719_, 0, v_funNames_1701_);
lean_closure_set(v___f_1719_, 1, v_fixedParamPerms_1699_);
lean_closure_set(v___f_1719_, 2, v___x_1710_);
lean_closure_set(v___f_1719_, 3, v_argsPacker_1700_);
lean_closure_set(v___f_1719_, 4, v___x_1718_);
lean_closure_set(v___f_1719_, 5, v_newF_1702_);
v___x_1720_ = 0;
v___x_1721_ = 1;
v___x_1722_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_e_1703_, v___f_1709_, v___f_1719_, v___x_1720_, v___x_1721_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
return v___x_1722_;
}
}
else
{
lean_dec_ref(v_e_1703_);
lean_dec_ref(v_newF_1702_);
lean_dec_ref(v_funNames_1701_);
lean_dec_ref(v_argsPacker_1700_);
lean_dec_ref(v_fixedParamPerms_1699_);
return v___x_1711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___boxed(lean_object* v_fixedParamPerms_1740_, lean_object* v_argsPacker_1741_, lean_object* v_funNames_1742_, lean_object* v_newF_1743_, lean_object* v_e_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_1740_, v_argsPacker_1741_, v_funNames_1742_, v_newF_1743_, v_e_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_);
lean_dec(v_a_1748_);
lean_dec_ref(v_a_1747_);
lean_dec(v_a_1746_);
lean_dec_ref(v_a_1745_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1751_, lean_object* v_m_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___redArg(v_m_1752_, v_a_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1755_, lean_object* v_m_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_00_u03b2_1755_, v_m_1756_, v_a_1757_);
lean_dec_ref(v_a_1757_);
lean_dec_ref(v_m_1756_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(lean_object* v_upperBound_1759_, lean_object* v___x_1760_, lean_object* v_pre_1761_, lean_object* v_post_1762_, uint8_t v_usedLetOnly_1763_, uint8_t v_skipConstInApp_1764_, uint8_t v_skipInstances_1765_, lean_object* v_postApp_1766_, lean_object* v___x_1767_, lean_object* v_inst_1768_, lean_object* v_R_1769_, lean_object* v_a_1770_, lean_object* v_b_1771_, lean_object* v_c_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_upperBound_1759_, v___x_1760_, v_pre_1761_, v_post_1762_, v_usedLetOnly_1763_, v_skipConstInApp_1764_, v_skipInstances_1765_, v_postApp_1766_, v_a_1770_, v_b_1771_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___boxed(lean_object** _args){
lean_object* v_upperBound_1780_ = _args[0];
lean_object* v___x_1781_ = _args[1];
lean_object* v_pre_1782_ = _args[2];
lean_object* v_post_1783_ = _args[3];
lean_object* v_usedLetOnly_1784_ = _args[4];
lean_object* v_skipConstInApp_1785_ = _args[5];
lean_object* v_skipInstances_1786_ = _args[6];
lean_object* v_postApp_1787_ = _args[7];
lean_object* v___x_1788_ = _args[8];
lean_object* v_inst_1789_ = _args[9];
lean_object* v_R_1790_ = _args[10];
lean_object* v_a_1791_ = _args[11];
lean_object* v_b_1792_ = _args[12];
lean_object* v_c_1793_ = _args[13];
lean_object* v___y_1794_ = _args[14];
lean_object* v___y_1795_ = _args[15];
lean_object* v___y_1796_ = _args[16];
lean_object* v___y_1797_ = _args[17];
lean_object* v___y_1798_ = _args[18];
lean_object* v___y_1799_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_1800_; uint8_t v_skipConstInApp_boxed_1801_; uint8_t v_skipInstances_boxed_1802_; lean_object* v_res_1803_; 
v_usedLetOnly_boxed_1800_ = lean_unbox(v_usedLetOnly_1784_);
v_skipConstInApp_boxed_1801_ = lean_unbox(v_skipConstInApp_1785_);
v_skipInstances_boxed_1802_ = lean_unbox(v_skipInstances_1786_);
v_res_1803_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(v_upperBound_1780_, v___x_1781_, v_pre_1782_, v_post_1783_, v_usedLetOnly_boxed_1800_, v_skipConstInApp_boxed_1801_, v_skipInstances_boxed_1802_, v_postApp_1787_, v___x_1788_, v_inst_1789_, v_R_1790_, v_a_1791_, v_b_1792_, v_c_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec(v___x_1788_);
lean_dec_ref(v___x_1781_);
lean_dec(v_upperBound_1780_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_1804_, lean_object* v_name_1805_, uint8_t v_bi_1806_, lean_object* v_type_1807_, lean_object* v_k_1808_, uint8_t v_kind_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_1805_, v_bi_1806_, v_type_1807_, v_k_1808_, v_kind_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_1817_, lean_object* v_name_1818_, lean_object* v_bi_1819_, lean_object* v_type_1820_, lean_object* v_k_1821_, lean_object* v_kind_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
uint8_t v_bi_boxed_1829_; uint8_t v_kind_boxed_1830_; lean_object* v_res_1831_; 
v_bi_boxed_1829_ = lean_unbox(v_bi_1819_);
v_kind_boxed_1830_ = lean_unbox(v_kind_1822_);
v_res_1831_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(v_00_u03b1_1817_, v_name_1818_, v_bi_boxed_1829_, v_type_1820_, v_k_1821_, v_kind_boxed_1830_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(lean_object* v_00_u03b1_1832_, lean_object* v_name_1833_, lean_object* v_type_1834_, lean_object* v_val_1835_, lean_object* v_k_1836_, uint8_t v_nondep_1837_, uint8_t v_kind_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_1833_, v_type_1834_, v_val_1835_, v_k_1836_, v_nondep_1837_, v_kind_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___boxed(lean_object* v_00_u03b1_1846_, lean_object* v_name_1847_, lean_object* v_type_1848_, lean_object* v_val_1849_, lean_object* v_k_1850_, lean_object* v_nondep_1851_, lean_object* v_kind_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
uint8_t v_nondep_boxed_1859_; uint8_t v_kind_boxed_1860_; lean_object* v_res_1861_; 
v_nondep_boxed_1859_ = lean_unbox(v_nondep_1851_);
v_kind_boxed_1860_ = lean_unbox(v_kind_1852_);
v_res_1861_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(v_00_u03b1_1846_, v_name_1847_, v_type_1848_, v_val_1849_, v_k_1850_, v_nondep_boxed_1859_, v_kind_boxed_1860_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(lean_object* v_00_u03b1_1862_, lean_object* v_ref_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_1863_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___boxed(lean_object* v_00_u03b1_1870_, lean_object* v_ref_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(v_00_u03b1_1870_, v_ref_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(lean_object* v_00_u03b1_1878_, lean_object* v_x_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___boxed(lean_object* v_00_u03b1_1887_, lean_object* v_x_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(v_00_u03b1_1887_, v_x_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15(lean_object* v_00_u03b2_1896_, lean_object* v_m_1897_, lean_object* v_a_1898_, lean_object* v_b_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v_m_1897_, v_a_1898_, v_b_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_1901_, lean_object* v_a_1902_, lean_object* v_x_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_spec__7___redArg(v_a_1902_, v_x_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b2_1905_, lean_object* v_a_1906_, lean_object* v_x_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_spec__7(v_00_u03b2_1905_, v_a_1906_, v_x_1907_);
lean_dec(v_x_1907_);
lean_dec_ref(v_a_1906_);
return v_res_1908_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(lean_object* v_00_u03b2_1909_, lean_object* v_a_1910_, lean_object* v_x_1911_){
_start:
{
uint8_t v___x_1912_; 
v___x_1912_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_1910_, v_x_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___boxed(lean_object* v_00_u03b2_1913_, lean_object* v_a_1914_, lean_object* v_x_1915_){
_start:
{
uint8_t v_res_1916_; lean_object* v_r_1917_; 
v_res_1916_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(v_00_u03b2_1913_, v_a_1914_, v_x_1915_);
lean_dec(v_x_1915_);
lean_dec_ref(v_a_1914_);
v_r_1917_ = lean_box(v_res_1916_);
return v_r_1917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21(lean_object* v_00_u03b2_1918_, lean_object* v_data_1919_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_data_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22(lean_object* v_00_u03b2_1921_, lean_object* v_a_1922_, lean_object* v_b_1923_, lean_object* v_x_1924_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_1922_, v_b_1923_, v_x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22(lean_object* v_00_u03b2_1926_, lean_object* v_i_1927_, lean_object* v_source_1928_, lean_object* v_target_1929_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v_i_1927_, v_source_1928_, v_target_1929_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23(lean_object* v_00_u03b2_1931_, lean_object* v_x_1932_, lean_object* v_x_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(v_x_1932_, v_x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName(lean_object* v_fixedParamPerms_1941_, lean_object* v_argsPacker_1942_, lean_object* v_preDefs_1943_){
_start:
{
lean_object* v___x_1944_; uint8_t v___x_1959_; 
v___x_1944_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1959_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_1941_);
if (v___x_1959_ == 0)
{
goto v___jp_1945_;
}
else
{
uint8_t v___x_1960_; 
v___x_1960_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_1942_);
if (v___x_1960_ == 0)
{
goto v___jp_1945_;
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v_declName_1963_; 
v___x_1961_ = lean_unsigned_to_nat(0u);
v___x_1962_ = lean_array_get_borrowed(v___x_1944_, v_preDefs_1943_, v___x_1961_);
v_declName_1963_ = lean_ctor_get(v___x_1962_, 3);
lean_inc(v_declName_1963_);
return v_declName_1963_;
}
}
v___jp_1945_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; 
v___x_1946_ = lean_unsigned_to_nat(1u);
v___x_1947_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_1942_);
v___x_1948_ = lean_nat_dec_lt(v___x_1946_, v___x_1947_);
lean_dec(v___x_1947_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v_declName_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1949_ = lean_unsigned_to_nat(0u);
v___x_1950_ = lean_array_get_borrowed(v___x_1944_, v_preDefs_1943_, v___x_1949_);
v_declName_1951_ = lean_ctor_get(v___x_1950_, 3);
v___x_1952_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__1));
lean_inc(v_declName_1951_);
v___x_1953_ = l_Lean_Name_append(v_declName_1951_, v___x_1952_);
return v___x_1953_;
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v_declName_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1954_ = lean_unsigned_to_nat(0u);
v___x_1955_ = lean_array_get_borrowed(v___x_1944_, v_preDefs_1943_, v___x_1954_);
v_declName_1956_ = lean_ctor_get(v___x_1955_, 3);
v___x_1957_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__3));
lean_inc(v_declName_1956_);
v___x_1958_ = l_Lean_Name_append(v_declName_1956_, v___x_1957_);
return v___x_1958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName___boxed(lean_object* v_fixedParamPerms_1964_, lean_object* v_argsPacker_1965_, lean_object* v_preDefs_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_1964_, v_argsPacker_1965_, v_preDefs_1966_);
lean_dec_ref(v_preDefs_1966_);
lean_dec_ref(v_argsPacker_1965_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(lean_object* v_k_1968_, lean_object* v_b_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v___x_1975_; 
lean_inc(v___y_1973_);
lean_inc_ref(v___y_1972_);
lean_inc(v___y_1971_);
lean_inc_ref(v___y_1970_);
v___x_1975_ = lean_apply_6(v_k_1968_, v_b_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, lean_box(0));
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed(lean_object* v_k_1976_, lean_object* v_b_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(v_k_1976_, v_b_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(lean_object* v_perm_1984_, lean_object* v_type_1985_, lean_object* v_k_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v___f_1992_; lean_object* v___x_1993_; 
v___f_1992_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1992_, 0, v_k_1986_);
v___x_1993_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_1984_, v_type_1985_, v___f_1992_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
v_a_2002_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1993_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1993_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___boxed(lean_object* v_perm_2010_, lean_object* v_type_2011_, lean_object* v_k_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_2010_, v_type_2011_, v_k_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(lean_object* v_00_u03b1_2019_, lean_object* v_perm_2020_, lean_object* v_type_2021_, lean_object* v_k_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_2020_, v_type_2021_, v_k_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___boxed(lean_object* v_00_u03b1_2029_, lean_object* v_perm_2030_, lean_object* v_type_2031_, lean_object* v_k_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(v_00_u03b1_2029_, v_perm_2030_, v_type_2031_, v_k_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(lean_object* v___x_2039_, lean_object* v_ys_2040_, size_t v_sz_2041_, size_t v_i_2042_, lean_object* v_bs_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
uint8_t v___x_2049_; 
v___x_2049_ = lean_usize_dec_lt(v_i_2042_, v_sz_2041_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; 
lean_dec_ref(v_ys_2040_);
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v_bs_2043_);
return v___x_2050_;
}
else
{
lean_object* v_v_2051_; lean_object* v_value_2052_; lean_object* v___x_2053_; lean_object* v_bs_x27_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v_v_2051_ = lean_array_uget_borrowed(v_bs_2043_, v_i_2042_);
v_value_2052_ = lean_ctor_get(v_v_2051_, 7);
lean_inc_ref(v_value_2052_);
v___x_2053_ = lean_unsigned_to_nat(0u);
v_bs_x27_2054_ = lean_array_uset(v_bs_2043_, v_i_2042_, v___x_2053_);
v___x_2055_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2056_ = lean_usize_to_nat(v_i_2042_);
v___x_2057_ = lean_array_get_borrowed(v___x_2055_, v___x_2039_, v___x_2056_);
lean_dec(v___x_2056_);
lean_inc_ref(v_ys_2040_);
lean_inc(v___x_2057_);
v___x_2058_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_2057_, v_value_2052_, v_ys_2040_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; size_t v___x_2060_; size_t v___x_2061_; lean_object* v___x_2062_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v___x_2060_ = ((size_t)1ULL);
v___x_2061_ = lean_usize_add(v_i_2042_, v___x_2060_);
v___x_2062_ = lean_array_uset(v_bs_x27_2054_, v_i_2042_, v_a_2059_);
v_i_2042_ = v___x_2061_;
v_bs_2043_ = v___x_2062_;
goto _start;
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec_ref(v_bs_x27_2054_);
lean_dec_ref(v_ys_2040_);
v_a_2064_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2058_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2058_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg___boxed(lean_object* v___x_2072_, lean_object* v_ys_2073_, lean_object* v_sz_2074_, lean_object* v_i_2075_, lean_object* v_bs_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
size_t v_sz_boxed_2082_; size_t v_i_boxed_2083_; lean_object* v_res_2084_; 
v_sz_boxed_2082_ = lean_unbox_usize(v_sz_2074_);
lean_dec(v_sz_2074_);
v_i_boxed_2083_ = lean_unbox_usize(v_i_2075_);
lean_dec(v_i_2075_);
v_res_2084_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2072_, v_ys_2073_, v_sz_boxed_2082_, v_i_boxed_2083_, v_bs_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec_ref(v___x_2072_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(lean_object* v___x_2085_, lean_object* v_ys_2086_, size_t v_sz_2087_, size_t v_i_2088_, lean_object* v_bs_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
uint8_t v___x_2095_; 
v___x_2095_ = lean_usize_dec_lt(v_i_2088_, v_sz_2087_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; 
lean_dec_ref(v_ys_2086_);
v___x_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2096_, 0, v_bs_2089_);
return v___x_2096_;
}
else
{
lean_object* v_v_2097_; lean_object* v_type_2098_; lean_object* v___x_2099_; lean_object* v_bs_x27_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v_v_2097_ = lean_array_uget_borrowed(v_bs_2089_, v_i_2088_);
v_type_2098_ = lean_ctor_get(v_v_2097_, 6);
lean_inc_ref(v_type_2098_);
v___x_2099_ = lean_unsigned_to_nat(0u);
v_bs_x27_2100_ = lean_array_uset(v_bs_2089_, v_i_2088_, v___x_2099_);
v___x_2101_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2102_ = lean_usize_to_nat(v_i_2088_);
v___x_2103_ = lean_array_get_borrowed(v___x_2101_, v___x_2085_, v___x_2102_);
lean_dec(v___x_2102_);
lean_inc_ref(v_ys_2086_);
lean_inc(v___x_2103_);
v___x_2104_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_2103_, v_type_2098_, v_ys_2086_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; size_t v___x_2106_; size_t v___x_2107_; lean_object* v___x_2108_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v___x_2104_, 1);
v___x_2106_ = ((size_t)1ULL);
v___x_2107_ = lean_usize_add(v_i_2088_, v___x_2106_);
v___x_2108_ = lean_array_uset(v_bs_x27_2100_, v_i_2088_, v_a_2105_);
v_i_2088_ = v___x_2107_;
v_bs_2089_ = v___x_2108_;
goto _start;
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec_ref(v_bs_x27_2100_);
lean_dec_ref(v_ys_2086_);
v_a_2110_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2104_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2104_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg___boxed(lean_object* v___x_2118_, lean_object* v_ys_2119_, lean_object* v_sz_2120_, lean_object* v_i_2121_, lean_object* v_bs_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
size_t v_sz_boxed_2128_; size_t v_i_boxed_2129_; lean_object* v_res_2130_; 
v_sz_boxed_2128_ = lean_unbox_usize(v_sz_2120_);
lean_dec(v_sz_2120_);
v_i_boxed_2129_ = lean_unbox_usize(v_i_2121_);
lean_dec(v_i_2121_);
v_res_2130_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2118_, v_ys_2119_, v_sz_boxed_2128_, v_i_boxed_2129_, v_bs_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec_ref(v___x_2118_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
if (lean_obj_tag(v_a_2131_) == 0)
{
lean_object* v___x_2133_; 
v___x_2133_ = l_List_reverse___redArg(v_a_2132_);
return v___x_2133_;
}
else
{
lean_object* v_head_2134_; lean_object* v_tail_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2144_; 
v_head_2134_ = lean_ctor_get(v_a_2131_, 0);
v_tail_2135_ = lean_ctor_get(v_a_2131_, 1);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_a_2131_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2137_ = v_a_2131_;
v_isShared_2138_ = v_isSharedCheck_2144_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_tail_2135_);
lean_inc(v_head_2134_);
lean_dec(v_a_2131_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2144_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2139_ = l_Lean_mkLevelParam(v_head_2134_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 1, v_a_2132_);
lean_ctor_set(v___x_2137_, 0, v___x_2139_);
v___x_2141_ = v___x_2137_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2139_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_a_2132_);
v___x_2141_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
v_a_2131_ = v_tail_2135_;
v_a_2132_ = v___x_2141_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(size_t v_sz_2145_, size_t v_i_2146_, lean_object* v_bs_2147_){
_start:
{
uint8_t v___x_2148_; 
v___x_2148_ = lean_usize_dec_lt(v_i_2146_, v_sz_2145_);
if (v___x_2148_ == 0)
{
return v_bs_2147_;
}
else
{
lean_object* v_v_2149_; lean_object* v_declName_2150_; lean_object* v___x_2151_; lean_object* v_bs_x27_2152_; size_t v___x_2153_; size_t v___x_2154_; lean_object* v___x_2155_; 
v_v_2149_ = lean_array_uget_borrowed(v_bs_2147_, v_i_2146_);
v_declName_2150_ = lean_ctor_get(v_v_2149_, 3);
lean_inc(v_declName_2150_);
v___x_2151_ = lean_unsigned_to_nat(0u);
v_bs_x27_2152_ = lean_array_uset(v_bs_2147_, v_i_2146_, v___x_2151_);
v___x_2153_ = ((size_t)1ULL);
v___x_2154_ = lean_usize_add(v_i_2146_, v___x_2153_);
v___x_2155_ = lean_array_uset(v_bs_x27_2152_, v_i_2146_, v_declName_2150_);
v_i_2146_ = v___x_2154_;
v_bs_2147_ = v___x_2155_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3___boxed(lean_object* v_sz_2157_, lean_object* v_i_2158_, lean_object* v_bs_2159_){
_start:
{
size_t v_sz_boxed_2160_; size_t v_i_boxed_2161_; lean_object* v_res_2162_; 
v_sz_boxed_2160_ = lean_unbox_usize(v_sz_2157_);
lean_dec(v_sz_2157_);
v_i_boxed_2161_ = lean_unbox_usize(v_i_2158_);
lean_dec(v_i_2158_);
v_res_2162_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_boxed_2160_, v_i_boxed_2161_, v_bs_2159_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0(lean_object* v_preDefs_2163_, lean_object* v_perms_2164_, lean_object* v_argsPacker_2165_, uint8_t v___x_2166_, lean_object* v_ref_2167_, uint8_t v_kind_2168_, lean_object* v_levelParams_2169_, lean_object* v_modifiers_2170_, lean_object* v_newFn_2171_, lean_object* v_binders_2172_, lean_object* v_numSectionVars_2173_, lean_object* v_value_2174_, lean_object* v_termination_2175_, lean_object* v_fixedParamPerms_2176_, lean_object* v_ys_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
size_t v_sz_2183_; size_t v___x_2184_; lean_object* v___x_2185_; 
v_sz_2183_ = lean_array_size(v_preDefs_2163_);
v___x_2184_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_2163_);
lean_inc_ref(v_ys_2177_);
v___x_2185_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v_perms_2164_, v_ys_2177_, v_sz_2183_, v___x_2184_, v_preDefs_2163_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___x_2187_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2185_, 1);
lean_inc_ref(v_preDefs_2163_);
lean_inc_ref(v_ys_2177_);
v___x_2187_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v_perms_2164_, v_ys_2177_, v_sz_2183_, v___x_2184_, v_preDefs_2163_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2189_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2188_);
lean_dec_ref_known(v___x_2187_, 1);
v___x_2189_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_2165_, v_a_2186_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
lean_dec(v_a_2186_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; uint8_t v___x_2191_; uint8_t v___x_2192_; lean_object* v___x_2193_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2189_, 1);
v___x_2191_ = 1;
v___x_2192_ = 1;
v___x_2193_ = l_Lean_Meta_mkForallFVars(v_ys_2177_, v_a_2190_, v___x_2166_, v___x_2191_, v___x_2191_, v___x_2192_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc_n(v_a_2194_, 2);
lean_dec_ref_known(v___x_2193_, 1);
lean_inc_ref(v_termination_2175_);
lean_inc(v_numSectionVars_2173_);
lean_inc(v_binders_2172_);
lean_inc(v_newFn_2171_);
lean_inc_ref(v_modifiers_2170_);
lean_inc(v_levelParams_2169_);
lean_inc(v_ref_2167_);
v___x_2195_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2195_, 0, v_ref_2167_);
lean_ctor_set(v___x_2195_, 1, v_levelParams_2169_);
lean_ctor_set(v___x_2195_, 2, v_modifiers_2170_);
lean_ctor_set(v___x_2195_, 3, v_newFn_2171_);
lean_ctor_set(v___x_2195_, 4, v_binders_2172_);
lean_ctor_set(v___x_2195_, 5, v_numSectionVars_2173_);
lean_ctor_set(v___x_2195_, 6, v_a_2194_);
lean_ctor_set(v___x_2195_, 7, v_value_2174_);
lean_ctor_set(v___x_2195_, 8, v_termination_2175_);
lean_ctor_set_uint8(v___x_2195_, sizeof(void*)*9, v_kind_2168_);
v___x_2196_ = l_Lean_Elab_addAsAxiom___redArg(v___x_2195_, v___y_2180_, v___y_2181_);
lean_dec_ref_known(v___x_2195_, 9);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
lean_dec_ref_known(v___x_2196_, 1);
v___x_2197_ = lean_box(0);
lean_inc(v_levelParams_2169_);
v___x_2198_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_2169_, v___x_2197_);
lean_inc(v_newFn_2171_);
v___x_2199_ = l_Lean_mkConst(v_newFn_2171_, v___x_2198_);
v___x_2200_ = l_Lean_mkAppN(v___x_2199_, v_ys_2177_);
v___x_2201_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_2165_, v_a_2188_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
lean_dec(v_a_2188_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2201_, 1);
v___x_2203_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_2183_, v___x_2184_, v_preDefs_2163_);
v___x_2204_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_2176_, v_argsPacker_2165_, v___x_2203_, v___x_2200_, v_a_2202_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2206_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec_ref_known(v___x_2204_, 1);
v___x_2206_ = l_Lean_Meta_mkLambdaFVars(v_ys_2177_, v_a_2205_, v___x_2166_, v___x_2191_, v___x_2166_, v___x_2191_, v___x_2192_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
lean_dec_ref(v_ys_2177_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2215_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2215_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2215_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2211_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2211_, 0, v_ref_2167_);
lean_ctor_set(v___x_2211_, 1, v_levelParams_2169_);
lean_ctor_set(v___x_2211_, 2, v_modifiers_2170_);
lean_ctor_set(v___x_2211_, 3, v_newFn_2171_);
lean_ctor_set(v___x_2211_, 4, v_binders_2172_);
lean_ctor_set(v___x_2211_, 5, v_numSectionVars_2173_);
lean_ctor_set(v___x_2211_, 6, v_a_2194_);
lean_ctor_set(v___x_2211_, 7, v_a_2207_);
lean_ctor_set(v___x_2211_, 8, v_termination_2175_);
lean_ctor_set_uint8(v___x_2211_, sizeof(void*)*9, v_kind_2168_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2211_);
v___x_2213_ = v___x_2209_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec(v_a_2194_);
lean_dec_ref(v_termination_2175_);
lean_dec(v_numSectionVars_2173_);
lean_dec(v_binders_2172_);
lean_dec(v_newFn_2171_);
lean_dec_ref(v_modifiers_2170_);
lean_dec(v_levelParams_2169_);
lean_dec(v_ref_2167_);
v_a_2216_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2206_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2206_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec(v_a_2194_);
lean_dec_ref(v_ys_2177_);
lean_dec_ref(v_termination_2175_);
lean_dec(v_numSectionVars_2173_);
lean_dec(v_binders_2172_);
lean_dec(v_newFn_2171_);
lean_dec_ref(v_modifiers_2170_);
lean_dec(v_levelParams_2169_);
lean_dec(v_ref_2167_);
v_a_2224_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2204_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2204_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec_ref(v___x_2200_);
lean_dec(v_a_2194_);
lean_dec_ref(v_ys_2177_);
lean_dec_ref(v_fixedParamPerms_2176_);
lean_dec_ref(v_termination_2175_);
lean_dec(v_numSectionVars_2173_);
lean_dec(v_binders_2172_);
lean_dec(v_newFn_2171_);
lean_dec_ref(v_modifiers_2170_);
lean_dec(v_levelParams_2169_);
lean_dec(v_ref_2167_);
lean_dec_ref(v_argsPacker_2165_);
lean_dec_ref(v_preDefs_2163_);
v_a_2232_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2201_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2201_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v_a_2194_);
lean_dec(v_a_2188_);
lean_dec_ref(v_ys_2177_);
lean_dec_ref(v_fixedParamPerms_2176_);
lean_dec_ref(v_termination_2175_);
lean_dec(v_numSectionVars_2173_);
lean_dec(v_binders_2172_);
lean_dec(v_newFn_2171_);
lean_dec_ref(v_modifiers_2170_);
lean_dec(v_levelParams_2169_);
lean_dec(v_ref_2167_);
lean_dec_ref(v_argsPacker_2165_);
lean_dec_ref(v_preDefs_2163_);
v_a_2240_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2196_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2196_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec(v_a_2188_);
lean_dec_ref(v_ys_2177_);
lean_dec_ref(v_fixedParamPerms_2176_);
lean_dec_ref(v_termination_2175_);
lean_dec_ref(v_value_2174_);
lean_dec(v_numSectionVars_2173_);
lean_dec(v_binders_2172_);
lean_dec(v_newFn_2171_);
lean_dec_ref(v_modifiers_2170_);
lean_dec(v_levelParams_2169_);
lean_dec(v_ref_2167_);
lean_dec_ref(v_argsPacker_2165_);
lean_dec_ref(v_preDefs_2163_);
v_a_2248_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2193_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2193_);
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
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec(v_a_2188_);
lean_dec_ref(v_ys_2177_);
lean_dec_ref(v_fixedParamPerms_2176_);
lean_dec_ref(v_termination_2175_);
lean_dec_ref(v_value_2174_);
lean_dec(v_numSectionVars_2173_);
lean_dec(v_binders_2172_);
lean_dec(v_newFn_2171_);
lean_dec_ref(v_modifiers_2170_);
lean_dec(v_levelParams_2169_);
lean_dec(v_ref_2167_);
lean_dec_ref(v_argsPacker_2165_);
lean_dec_ref(v_preDefs_2163_);
v_a_2256_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2189_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2189_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec(v_a_2186_);
lean_dec_ref(v_ys_2177_);
lean_dec_ref(v_fixedParamPerms_2176_);
lean_dec_ref(v_termination_2175_);
lean_dec_ref(v_value_2174_);
lean_dec(v_numSectionVars_2173_);
lean_dec(v_binders_2172_);
lean_dec(v_newFn_2171_);
lean_dec_ref(v_modifiers_2170_);
lean_dec(v_levelParams_2169_);
lean_dec(v_ref_2167_);
lean_dec_ref(v_argsPacker_2165_);
lean_dec_ref(v_preDefs_2163_);
v_a_2264_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2187_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2187_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec_ref(v_ys_2177_);
lean_dec_ref(v_fixedParamPerms_2176_);
lean_dec_ref(v_termination_2175_);
lean_dec_ref(v_value_2174_);
lean_dec(v_numSectionVars_2173_);
lean_dec(v_binders_2172_);
lean_dec(v_newFn_2171_);
lean_dec_ref(v_modifiers_2170_);
lean_dec(v_levelParams_2169_);
lean_dec(v_ref_2167_);
lean_dec_ref(v_argsPacker_2165_);
lean_dec_ref(v_preDefs_2163_);
v_a_2272_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2185_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2185_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0___boxed(lean_object** _args){
lean_object* v_preDefs_2280_ = _args[0];
lean_object* v_perms_2281_ = _args[1];
lean_object* v_argsPacker_2282_ = _args[2];
lean_object* v___x_2283_ = _args[3];
lean_object* v_ref_2284_ = _args[4];
lean_object* v_kind_2285_ = _args[5];
lean_object* v_levelParams_2286_ = _args[6];
lean_object* v_modifiers_2287_ = _args[7];
lean_object* v_newFn_2288_ = _args[8];
lean_object* v_binders_2289_ = _args[9];
lean_object* v_numSectionVars_2290_ = _args[10];
lean_object* v_value_2291_ = _args[11];
lean_object* v_termination_2292_ = _args[12];
lean_object* v_fixedParamPerms_2293_ = _args[13];
lean_object* v_ys_2294_ = _args[14];
lean_object* v___y_2295_ = _args[15];
lean_object* v___y_2296_ = _args[16];
lean_object* v___y_2297_ = _args[17];
lean_object* v___y_2298_ = _args[18];
lean_object* v___y_2299_ = _args[19];
_start:
{
uint8_t v___x_2509__boxed_2300_; uint8_t v_kind_boxed_2301_; lean_object* v_res_2302_; 
v___x_2509__boxed_2300_ = lean_unbox(v___x_2283_);
v_kind_boxed_2301_ = lean_unbox(v_kind_2285_);
v_res_2302_ = l_Lean_Elab_WF_packMutual___lam__0(v_preDefs_2280_, v_perms_2281_, v_argsPacker_2282_, v___x_2509__boxed_2300_, v_ref_2284_, v_kind_boxed_2301_, v_levelParams_2286_, v_modifiers_2287_, v_newFn_2288_, v_binders_2289_, v_numSectionVars_2290_, v_value_2291_, v_termination_2292_, v_fixedParamPerms_2293_, v_ys_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec_ref(v_perms_2281_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual(lean_object* v_fixedParamPerms_2303_, lean_object* v_argsPacker_2304_, lean_object* v_preDefs_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v_ref_2314_; uint8_t v_kind_2315_; lean_object* v_levelParams_2316_; lean_object* v_modifiers_2317_; lean_object* v_declName_2318_; lean_object* v_binders_2319_; lean_object* v_numSectionVars_2320_; lean_object* v_type_2321_; lean_object* v_value_2322_; lean_object* v_termination_2323_; lean_object* v_newFn_2324_; uint8_t v___x_2325_; 
v___x_2311_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_2312_ = lean_unsigned_to_nat(0u);
v___x_2313_ = lean_array_get_borrowed(v___x_2311_, v_preDefs_2305_, v___x_2312_);
v_ref_2314_ = lean_ctor_get(v___x_2313_, 0);
v_kind_2315_ = lean_ctor_get_uint8(v___x_2313_, sizeof(void*)*9);
v_levelParams_2316_ = lean_ctor_get(v___x_2313_, 1);
v_modifiers_2317_ = lean_ctor_get(v___x_2313_, 2);
v_declName_2318_ = lean_ctor_get(v___x_2313_, 3);
v_binders_2319_ = lean_ctor_get(v___x_2313_, 4);
v_numSectionVars_2320_ = lean_ctor_get(v___x_2313_, 5);
v_type_2321_ = lean_ctor_get(v___x_2313_, 6);
v_value_2322_ = lean_ctor_get(v___x_2313_, 7);
v_termination_2323_ = lean_ctor_get(v___x_2313_, 8);
lean_inc_ref(v_fixedParamPerms_2303_);
v_newFn_2324_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_2303_, v_argsPacker_2304_, v_preDefs_2305_);
v___x_2325_ = lean_name_eq(v_newFn_2324_, v_declName_2318_);
if (v___x_2325_ == 0)
{
lean_object* v_perms_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___f_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
lean_inc_ref(v_termination_2323_);
lean_inc_ref(v_value_2322_);
lean_inc_ref(v_type_2321_);
lean_inc(v_numSectionVars_2320_);
lean_inc(v_binders_2319_);
lean_inc_ref(v_modifiers_2317_);
lean_inc(v_levelParams_2316_);
lean_inc(v_ref_2314_);
v_perms_2326_ = lean_ctor_get(v_fixedParamPerms_2303_, 1);
lean_inc_ref_n(v_perms_2326_, 2);
v___x_2327_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2328_ = lean_box(v___x_2325_);
v___x_2329_ = lean_box(v_kind_2315_);
v___f_2330_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packMutual___lam__0___boxed), 20, 14);
lean_closure_set(v___f_2330_, 0, v_preDefs_2305_);
lean_closure_set(v___f_2330_, 1, v_perms_2326_);
lean_closure_set(v___f_2330_, 2, v_argsPacker_2304_);
lean_closure_set(v___f_2330_, 3, v___x_2328_);
lean_closure_set(v___f_2330_, 4, v_ref_2314_);
lean_closure_set(v___f_2330_, 5, v___x_2329_);
lean_closure_set(v___f_2330_, 6, v_levelParams_2316_);
lean_closure_set(v___f_2330_, 7, v_modifiers_2317_);
lean_closure_set(v___f_2330_, 8, v_newFn_2324_);
lean_closure_set(v___f_2330_, 9, v_binders_2319_);
lean_closure_set(v___f_2330_, 10, v_numSectionVars_2320_);
lean_closure_set(v___f_2330_, 11, v_value_2322_);
lean_closure_set(v___f_2330_, 12, v_termination_2323_);
lean_closure_set(v___f_2330_, 13, v_fixedParamPerms_2303_);
v___x_2331_ = lean_array_get(v___x_2327_, v_perms_2326_, v___x_2312_);
lean_dec_ref(v_perms_2326_);
v___x_2332_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v___x_2331_, v_type_2321_, v___f_2330_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
return v___x_2332_;
}
else
{
lean_object* v___x_2333_; 
lean_inc(v___x_2313_);
lean_dec(v_newFn_2324_);
lean_dec_ref(v_preDefs_2305_);
lean_dec_ref(v_argsPacker_2304_);
lean_dec_ref(v_fixedParamPerms_2303_);
v___x_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2313_);
return v___x_2333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___boxed(lean_object* v_fixedParamPerms_2334_, lean_object* v_argsPacker_2335_, lean_object* v_preDefs_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_Lean_Elab_WF_packMutual(v_fixedParamPerms_2334_, v_argsPacker_2335_, v_preDefs_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v_a_2340_);
lean_dec_ref(v_a_2339_);
lean_dec(v_a_2338_);
lean_dec_ref(v_a_2337_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(lean_object* v___x_2343_, lean_object* v_ys_2344_, lean_object* v_as_2345_, size_t v_sz_2346_, size_t v_i_2347_, lean_object* v_bs_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2343_, v_ys_2344_, v_sz_2346_, v_i_2347_, v_bs_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___boxed(lean_object* v___x_2355_, lean_object* v_ys_2356_, lean_object* v_as_2357_, lean_object* v_sz_2358_, lean_object* v_i_2359_, lean_object* v_bs_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
size_t v_sz_boxed_2366_; size_t v_i_boxed_2367_; lean_object* v_res_2368_; 
v_sz_boxed_2366_ = lean_unbox_usize(v_sz_2358_);
lean_dec(v_sz_2358_);
v_i_boxed_2367_ = lean_unbox_usize(v_i_2359_);
lean_dec(v_i_2359_);
v_res_2368_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(v___x_2355_, v_ys_2356_, v_as_2357_, v_sz_boxed_2366_, v_i_boxed_2367_, v_bs_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec_ref(v_as_2357_);
lean_dec_ref(v___x_2355_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(lean_object* v___x_2369_, lean_object* v_ys_2370_, lean_object* v_as_2371_, size_t v_sz_2372_, size_t v_i_2373_, lean_object* v_bs_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2369_, v_ys_2370_, v_sz_2372_, v_i_2373_, v_bs_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___boxed(lean_object* v___x_2381_, lean_object* v_ys_2382_, lean_object* v_as_2383_, lean_object* v_sz_2384_, lean_object* v_i_2385_, lean_object* v_bs_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
size_t v_sz_boxed_2392_; size_t v_i_boxed_2393_; lean_object* v_res_2394_; 
v_sz_boxed_2392_ = lean_unbox_usize(v_sz_2384_);
lean_dec(v_sz_2384_);
v_i_boxed_2393_ = lean_unbox_usize(v_i_2385_);
lean_dec(v_i_2385_);
v_res_2394_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(v___x_2381_, v_ys_2382_, v_as_2383_, v_sz_boxed_2392_, v_i_boxed_2393_, v_bs_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec_ref(v_as_2383_);
lean_dec_ref(v___x_2381_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(lean_object* v_e_2395_, lean_object* v_k_2396_, uint8_t v_cleanupAnnotations_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v___f_2403_; uint8_t v___x_2404_; uint8_t v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___f_2403_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2403_, 0, v_k_2396_);
v___x_2404_ = 1;
v___x_2405_ = 0;
v___x_2406_ = lean_box(0);
v___x_2407_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2395_, v___x_2404_, v___x_2405_, v___x_2404_, v___x_2405_, v___x_2406_, v___f_2403_, v_cleanupAnnotations_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v___x_2407_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2407_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
v_a_2416_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2407_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2407_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg___boxed(lean_object* v_e_2424_, lean_object* v_k_2425_, lean_object* v_cleanupAnnotations_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2432_; lean_object* v_res_2433_; 
v_cleanupAnnotations_boxed_2432_ = lean_unbox(v_cleanupAnnotations_2426_);
v_res_2433_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2424_, v_k_2425_, v_cleanupAnnotations_boxed_2432_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(lean_object* v_00_u03b1_2434_, lean_object* v_e_2435_, lean_object* v_k_2436_, uint8_t v_cleanupAnnotations_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2435_, v_k_2436_, v_cleanupAnnotations_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___boxed(lean_object* v_00_u03b1_2444_, lean_object* v_e_2445_, lean_object* v_k_2446_, lean_object* v_cleanupAnnotations_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2453_; lean_object* v_res_2454_; 
v_cleanupAnnotations_boxed_2453_ = lean_unbox(v_cleanupAnnotations_2447_);
v_res_2454_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(v_00_u03b1_2444_, v_e_2445_, v_k_2446_, v_cleanupAnnotations_boxed_2453_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(lean_object* v_msg_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v___f_2461_; lean_object* v___x_1649__overap_2462_; lean_object* v___x_2463_; 
v___f_2461_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1649__overap_2462_ = lean_panic_fn_borrowed(v___f_2461_, v_msg_2455_);
lean_inc(v___y_2459_);
lean_inc_ref(v___y_2458_);
lean_inc(v___y_2457_);
lean_inc_ref(v___y_2456_);
v___x_2463_ = lean_apply_5(v___x_1649__overap_2462_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, lean_box(0));
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1___boxed(lean_object* v_msg_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v_msg_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0(lean_object* v_xs_2471_, lean_object* v_x_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2478_ = lean_array_get_size(v_xs_2471_);
v___x_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0___boxed(lean_object* v_xs_2480_, lean_object* v_x_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Lean_Elab_WF_varyingVarNames___lam__0(v_xs_2480_, v_x_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec_ref(v_x_2481_);
lean_dec_ref(v_xs_2480_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(lean_object* v_as_2488_, size_t v_sz_2489_, size_t v_i_2490_, lean_object* v_b_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v_a_2497_; uint8_t v___x_2501_; 
v___x_2501_ = lean_usize_dec_lt(v_i_2490_, v_sz_2489_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; 
v___x_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2502_, 0, v_b_2491_);
return v___x_2502_;
}
else
{
lean_object* v_snd_2503_; lean_object* v_fst_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2548_; 
v_snd_2503_ = lean_ctor_get(v_b_2491_, 1);
v_fst_2504_ = lean_ctor_get(v_b_2491_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_b_2491_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2506_ = v_b_2491_;
v_isShared_2507_ = v_isSharedCheck_2548_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_snd_2503_);
lean_inc(v_fst_2504_);
lean_dec(v_b_2491_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2548_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v_array_2508_; lean_object* v_start_2509_; lean_object* v_stop_2510_; uint8_t v___x_2511_; 
v_array_2508_ = lean_ctor_get(v_snd_2503_, 0);
v_start_2509_ = lean_ctor_get(v_snd_2503_, 1);
v_stop_2510_ = lean_ctor_get(v_snd_2503_, 2);
v___x_2511_ = lean_nat_dec_lt(v_start_2509_, v_stop_2510_);
if (v___x_2511_ == 0)
{
lean_object* v___x_2513_; 
if (v_isShared_2507_ == 0)
{
v___x_2513_ = v___x_2506_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_fst_2504_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_snd_2503_);
v___x_2513_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
lean_object* v___x_2514_; 
v___x_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
return v___x_2514_;
}
}
else
{
lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2544_; 
lean_inc(v_stop_2510_);
lean_inc(v_start_2509_);
lean_inc_ref(v_array_2508_);
v_isSharedCheck_2544_ = !lean_is_exclusive(v_snd_2503_);
if (v_isSharedCheck_2544_ == 0)
{
lean_object* v_unused_2545_; lean_object* v_unused_2546_; lean_object* v_unused_2547_; 
v_unused_2545_ = lean_ctor_get(v_snd_2503_, 2);
lean_dec(v_unused_2545_);
v_unused_2546_ = lean_ctor_get(v_snd_2503_, 1);
lean_dec(v_unused_2546_);
v_unused_2547_ = lean_ctor_get(v_snd_2503_, 0);
lean_dec(v_unused_2547_);
v___x_2517_ = v_snd_2503_;
v_isShared_2518_ = v_isSharedCheck_2544_;
goto v_resetjp_2516_;
}
else
{
lean_dec(v_snd_2503_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2544_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2523_; 
v___x_2519_ = lean_array_fget(v_array_2508_, v_start_2509_);
v___x_2520_ = lean_unsigned_to_nat(1u);
v___x_2521_ = lean_nat_add(v_start_2509_, v___x_2520_);
lean_dec(v_start_2509_);
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 1, v___x_2521_);
v___x_2523_ = v___x_2517_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_array_2508_);
lean_ctor_set(v_reuseFailAlloc_2543_, 1, v___x_2521_);
lean_ctor_set(v_reuseFailAlloc_2543_, 2, v_stop_2510_);
v___x_2523_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v_a_2524_ = lean_array_uget_borrowed(v_as_2488_, v_i_2490_);
v___x_2525_ = l_Lean_Expr_fvarId_x21(v_a_2524_);
v___x_2526_ = l_Lean_FVarId_getUserName___redArg(v___x_2525_, v___y_2492_, v___y_2493_, v___y_2494_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2527_; lean_object* v___x_2528_; lean_object* v___x_2530_; 
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_a_2527_);
lean_dec_ref_known(v___x_2526_, 1);
v___x_2528_ = lean_array_push(v_fst_2504_, v_a_2527_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 1, v___x_2523_);
lean_ctor_set(v___x_2506_, 0, v___x_2528_);
v___x_2530_ = v___x_2506_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v___x_2523_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
v_a_2497_ = v___x_2530_;
goto v___jp_2496_;
}
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
lean_dec_ref(v___x_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_fst_2504_);
v_a_2532_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2526_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2526_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
else
{
lean_object* v___x_2541_; 
lean_dec_ref_known(v___x_2519_, 1);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 1, v___x_2523_);
v___x_2541_ = v___x_2506_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_fst_2504_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v___x_2523_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
v_a_2497_ = v___x_2541_;
goto v___jp_2496_;
}
}
}
}
}
}
}
v___jp_2496_:
{
size_t v___x_2498_; size_t v___x_2499_; 
v___x_2498_ = ((size_t)1ULL);
v___x_2499_ = lean_usize_add(v_i_2490_, v___x_2498_);
v_i_2490_ = v___x_2499_;
v_b_2491_ = v_a_2497_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg___boxed(lean_object* v_as_2549_, lean_object* v_sz_2550_, lean_object* v_i_2551_, lean_object* v_b_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
size_t v_sz_boxed_2557_; size_t v_i_boxed_2558_; lean_object* v_res_2559_; 
v_sz_boxed_2557_ = lean_unbox_usize(v_sz_2550_);
lean_dec(v_sz_2550_);
v_i_boxed_2558_ = lean_unbox_usize(v_i_2551_);
lean_dec(v_i_2551_);
v_res_2559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2549_, v_sz_boxed_2557_, v_i_boxed_2558_, v_b_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec_ref(v_as_2549_);
return v_res_2559_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2562_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1));
v___x_2563_ = lean_unsigned_to_nat(4u);
v___x_2564_ = lean_unsigned_to_nat(119u);
v___x_2565_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2566_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2567_ = l_mkPanicMessageWithDecl(v___x_2566_, v___x_2565_, v___x_2564_, v___x_2563_, v___x_2562_);
return v___x_2567_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2569_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3));
v___x_2570_ = lean_unsigned_to_nat(4u);
v___x_2571_ = lean_unsigned_to_nat(120u);
v___x_2572_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2573_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2574_ = l_mkPanicMessageWithDecl(v___x_2573_, v___x_2572_, v___x_2571_, v___x_2570_, v___x_2569_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1(lean_object* v_a_2577_, lean_object* v_fixedParamPerms_2578_, lean_object* v___x_2579_, lean_object* v_preDefIdx_2580_, lean_object* v_xs_2581_, lean_object* v_x_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2588_ = lean_array_get_size(v_xs_2581_);
v___x_2589_ = lean_nat_dec_eq(v___x_2588_, v_a_2577_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2590_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2);
v___x_2591_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2590_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
return v___x_2591_;
}
else
{
lean_object* v_perms_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; uint8_t v___x_2595_; 
v_perms_2592_ = lean_ctor_get(v_fixedParamPerms_2578_, 1);
v___x_2593_ = lean_array_get_borrowed(v___x_2579_, v_perms_2592_, v_preDefIdx_2580_);
v___x_2594_ = lean_array_get_size(v___x_2593_);
v___x_2595_ = lean_nat_dec_eq(v___x_2594_, v_a_2577_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4);
v___x_2597_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2596_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
return v___x_2597_;
}
else
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; size_t v_sz_2602_; size_t v___x_2603_; lean_object* v___x_2604_; 
v___x_2598_ = lean_unsigned_to_nat(0u);
v___x_2599_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5));
lean_inc(v___x_2593_);
v___x_2600_ = l_Array_toSubarray___redArg(v___x_2593_, v___x_2598_, v___x_2594_);
v___x_2601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2599_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
v_sz_2602_ = lean_array_size(v_xs_2581_);
v___x_2603_ = ((size_t)0ULL);
v___x_2604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_xs_2581_, v_sz_2602_, v___x_2603_, v___x_2601_, v___y_2583_, v___y_2585_, v___y_2586_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2613_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2607_ = v___x_2604_;
v_isShared_2608_ = v_isSharedCheck_2613_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2604_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2613_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v_fst_2609_; lean_object* v___x_2611_; 
v_fst_2609_ = lean_ctor_get(v_a_2605_, 0);
lean_inc(v_fst_2609_);
lean_dec(v_a_2605_);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v_fst_2609_);
v___x_2611_ = v___x_2607_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_fst_2609_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
v_a_2614_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2604_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2604_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___boxed(lean_object* v_a_2622_, lean_object* v_fixedParamPerms_2623_, lean_object* v___x_2624_, lean_object* v_preDefIdx_2625_, lean_object* v_xs_2626_, lean_object* v_x_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lean_Elab_WF_varyingVarNames___lam__1(v_a_2622_, v_fixedParamPerms_2623_, v___x_2624_, v_preDefIdx_2625_, v_xs_2626_, v_x_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec_ref(v_x_2627_);
lean_dec_ref(v_xs_2626_);
lean_dec(v_preDefIdx_2625_);
lean_dec_ref(v___x_2624_);
lean_dec_ref(v_fixedParamPerms_2623_);
lean_dec(v_a_2622_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object* v_fixedParamPerms_2635_, lean_object* v_preDefIdx_2636_, lean_object* v_preDef_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_){
_start:
{
lean_object* v_type_2643_; lean_object* v_value_2644_; lean_object* v___f_2645_; lean_object* v___x_2646_; uint8_t v___x_2647_; lean_object* v___x_2648_; 
v_type_2643_ = lean_ctor_get(v_preDef_2637_, 6);
lean_inc_ref(v_type_2643_);
v_value_2644_ = lean_ctor_get(v_preDef_2637_, 7);
lean_inc_ref(v_value_2644_);
lean_dec_ref(v_preDef_2637_);
v___f_2645_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___closed__0));
v___x_2646_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2647_ = 0;
v___x_2648_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_value_2644_, v___f_2645_, v___x_2647_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___f_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc_n(v_a_2649_, 2);
lean_dec_ref_known(v___x_2648_, 1);
v___f_2650_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_varyingVarNames___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2650_, 0, v_a_2649_);
lean_closure_set(v___f_2650_, 1, v_fixedParamPerms_2635_);
lean_closure_set(v___f_2650_, 2, v___x_2646_);
lean_closure_set(v___f_2650_, 3, v_preDefIdx_2636_);
v___x_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2651_, 0, v_a_2649_);
v___x_2652_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2643_, v___x_2651_, v___f_2650_, v___x_2647_, v___x_2647_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
return v___x_2652_;
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_dec_ref(v_type_2643_);
lean_dec(v_preDefIdx_2636_);
lean_dec_ref(v_fixedParamPerms_2635_);
v_a_2653_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2648_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2648_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___boxed(lean_object* v_fixedParamPerms_2661_, lean_object* v_preDefIdx_2662_, lean_object* v_preDef_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Lean_Elab_WF_varyingVarNames(v_fixedParamPerms_2661_, v_preDefIdx_2662_, v_preDef_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(lean_object* v_as_2670_, size_t v_sz_2671_, size_t v_i_2672_, lean_object* v_b_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2670_, v_sz_2671_, v_i_2672_, v_b_2673_, v___y_2674_, v___y_2676_, v___y_2677_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___boxed(lean_object* v_as_2680_, lean_object* v_sz_2681_, lean_object* v_i_2682_, lean_object* v_b_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
size_t v_sz_boxed_2689_; size_t v_i_boxed_2690_; lean_object* v_res_2691_; 
v_sz_boxed_2689_ = lean_unbox_usize(v_sz_2681_);
lean_dec(v_sz_2681_);
v_i_boxed_2690_ = lean_unbox_usize(v_i_2682_);
lean_dec(v_i_2682_);
v_res_2691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(v_as_2680_, v_sz_boxed_2689_, v_i_boxed_2690_, v_b_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec_ref(v_as_2680_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(lean_object* v_msg_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v___f_2698_; lean_object* v___x_1596__overap_2699_; lean_object* v___x_2700_; 
v___f_2698_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1596__overap_2699_ = lean_panic_fn_borrowed(v___f_2698_, v_msg_2692_);
lean_inc(v___y_2696_);
lean_inc_ref(v___y_2695_);
lean_inc(v___y_2694_);
lean_inc_ref(v___y_2693_);
v___x_2700_ = lean_apply_5(v___x_1596__overap_2699_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, lean_box(0));
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0___boxed(lean_object* v_msg_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v_msg_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
return v_res_2707_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2708_; double v___x_2709_; 
v___x_2708_ = lean_unsigned_to_nat(0u);
v___x_2709_ = lean_float_of_nat(v___x_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(lean_object* v_cls_2713_, lean_object* v_msg_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_ref_2720_; lean_object* v___x_2721_; lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2767_; 
v_ref_2720_ = lean_ctor_get(v___y_2717_, 2);
v___x_2721_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msg_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2724_ = v___x_2721_;
v_isShared_2725_ = v_isSharedCheck_2767_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2721_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2767_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2726_; lean_object* v_traceState_2727_; lean_object* v_env_2728_; lean_object* v_nextMacroScope_2729_; lean_object* v_ngen_2730_; lean_object* v_auxDeclNGen_2731_; lean_object* v_cache_2732_; lean_object* v_recordedDeps_2733_; lean_object* v_messages_2734_; lean_object* v_infoState_2735_; lean_object* v_snapshotTasks_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2766_; 
v___x_2726_ = lean_st_ref_take(v___y_2718_);
v_traceState_2727_ = lean_ctor_get(v___x_2726_, 4);
v_env_2728_ = lean_ctor_get(v___x_2726_, 0);
v_nextMacroScope_2729_ = lean_ctor_get(v___x_2726_, 1);
v_ngen_2730_ = lean_ctor_get(v___x_2726_, 2);
v_auxDeclNGen_2731_ = lean_ctor_get(v___x_2726_, 3);
v_cache_2732_ = lean_ctor_get(v___x_2726_, 5);
v_recordedDeps_2733_ = lean_ctor_get(v___x_2726_, 6);
v_messages_2734_ = lean_ctor_get(v___x_2726_, 7);
v_infoState_2735_ = lean_ctor_get(v___x_2726_, 8);
v_snapshotTasks_2736_ = lean_ctor_get(v___x_2726_, 9);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2738_ = v___x_2726_;
v_isShared_2739_ = v_isSharedCheck_2766_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_snapshotTasks_2736_);
lean_inc(v_infoState_2735_);
lean_inc(v_messages_2734_);
lean_inc(v_recordedDeps_2733_);
lean_inc(v_cache_2732_);
lean_inc(v_traceState_2727_);
lean_inc(v_auxDeclNGen_2731_);
lean_inc(v_ngen_2730_);
lean_inc(v_nextMacroScope_2729_);
lean_inc(v_env_2728_);
lean_dec(v___x_2726_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2766_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
uint64_t v_tid_2740_; lean_object* v_traces_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2765_; 
v_tid_2740_ = lean_ctor_get_uint64(v_traceState_2727_, sizeof(void*)*1);
v_traces_2741_ = lean_ctor_get(v_traceState_2727_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v_traceState_2727_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2743_ = v_traceState_2727_;
v_isShared_2744_ = v_isSharedCheck_2765_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_traces_2741_);
lean_dec(v_traceState_2727_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2765_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; double v___x_2747_; uint8_t v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2756_; 
v___x_2745_ = lean_box(0);
v___x_2746_ = lean_box(0);
v___x_2747_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0);
v___x_2748_ = 0;
v___x_2749_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1));
v___x_2750_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2750_, 0, v_cls_2713_);
lean_ctor_set(v___x_2750_, 1, v___x_2746_);
lean_ctor_set(v___x_2750_, 2, v___x_2749_);
lean_ctor_set_float(v___x_2750_, sizeof(void*)*3, v___x_2747_);
lean_ctor_set_float(v___x_2750_, sizeof(void*)*3 + 8, v___x_2747_);
lean_ctor_set_uint8(v___x_2750_, sizeof(void*)*3 + 16, v___x_2748_);
v___x_2751_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2));
v___x_2752_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2750_);
lean_ctor_set(v___x_2752_, 1, v_a_2722_);
lean_ctor_set(v___x_2752_, 2, v___x_2751_);
lean_inc(v_ref_2720_);
v___x_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2753_, 0, v_ref_2720_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = l_Lean_PersistentArray_push___redArg(v_traces_2741_, v___x_2753_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 0, v___x_2754_);
v___x_2756_ = v___x_2743_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2754_);
lean_ctor_set_uint64(v_reuseFailAlloc_2764_, sizeof(void*)*1, v_tid_2740_);
v___x_2756_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
lean_object* v___x_2758_; 
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 4, v___x_2756_);
v___x_2758_ = v___x_2738_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_env_2728_);
lean_ctor_set(v_reuseFailAlloc_2763_, 1, v_nextMacroScope_2729_);
lean_ctor_set(v_reuseFailAlloc_2763_, 2, v_ngen_2730_);
lean_ctor_set(v_reuseFailAlloc_2763_, 3, v_auxDeclNGen_2731_);
lean_ctor_set(v_reuseFailAlloc_2763_, 4, v___x_2756_);
lean_ctor_set(v_reuseFailAlloc_2763_, 5, v_cache_2732_);
lean_ctor_set(v_reuseFailAlloc_2763_, 6, v_recordedDeps_2733_);
lean_ctor_set(v_reuseFailAlloc_2763_, 7, v_messages_2734_);
lean_ctor_set(v_reuseFailAlloc_2763_, 8, v_infoState_2735_);
lean_ctor_set(v_reuseFailAlloc_2763_, 9, v_snapshotTasks_2736_);
v___x_2758_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
lean_object* v___x_2759_; lean_object* v___x_2761_; 
v___x_2759_ = lean_st_ref_put(v___y_2718_, v___x_2758_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 0, v___x_2745_);
v___x_2761_ = v___x_2724_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2745_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___boxed(lean_object* v_cls_2768_, lean_object* v_msg_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v_cls_2768_, v_msg_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
return v_res_2775_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1));
v___x_2779_ = lean_unsigned_to_nat(8u);
v___x_2780_ = lean_unsigned_to_nat(135u);
v___x_2781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0));
v___x_2782_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2783_ = l_mkPanicMessageWithDecl(v___x_2782_, v___x_2781_, v___x_2780_, v___x_2779_, v___x_2778_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(lean_object* v___x_2784_, lean_object* v_unaryPreDefNonRec_2785_, lean_object* v___x_2786_, lean_object* v_us_2787_, lean_object* v_argsPacker_2788_, lean_object* v___x_2789_, lean_object* v_params_2790_, lean_object* v_x_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v___x_2797_; uint8_t v___x_2798_; 
v___x_2797_ = lean_array_get_size(v_params_2790_);
v___x_2798_ = lean_nat_dec_eq(v___x_2784_, v___x_2797_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
lean_dec(v___x_2789_);
lean_dec(v_us_2787_);
lean_dec_ref(v_unaryPreDefNonRec_2785_);
v___x_2799_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2);
v___x_2800_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v___x_2799_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
return v___x_2800_;
}
else
{
lean_object* v_declName_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_declName_2801_ = lean_ctor_get(v_unaryPreDefNonRec_2785_, 3);
lean_inc(v_declName_2801_);
lean_dec_ref(v_unaryPreDefNonRec_2785_);
v___x_2802_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v___x_2786_, v_params_2790_);
v___x_2803_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_2786_, v_params_2790_);
v___x_2804_ = l_Lean_mkConst(v_declName_2801_, v_us_2787_);
v___x_2805_ = l_Lean_mkAppN(v___x_2804_, v___x_2802_);
lean_dec_ref(v___x_2802_);
v___x_2806_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_2788_, v___x_2805_, v___x_2789_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; uint8_t v___x_2810_; lean_object* v___x_2811_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
v___x_2808_ = l_Lean_Expr_beta(v_a_2807_, v___x_2803_);
v___x_2809_ = 0;
v___x_2810_ = 1;
v___x_2811_ = l_Lean_Meta_mkLambdaFVars(v_params_2790_, v___x_2808_, v___x_2809_, v___x_2798_, v___x_2809_, v___x_2798_, v___x_2810_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
return v___x_2811_;
}
else
{
lean_dec_ref(v___x_2803_);
return v___x_2806_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed(lean_object* v___x_2812_, lean_object* v_unaryPreDefNonRec_2813_, lean_object* v___x_2814_, lean_object* v_us_2815_, lean_object* v_argsPacker_2816_, lean_object* v___x_2817_, lean_object* v_params_2818_, lean_object* v_x_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(v___x_2812_, v_unaryPreDefNonRec_2813_, v___x_2814_, v_us_2815_, v_argsPacker_2816_, v___x_2817_, v_params_2818_, v_x_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec_ref(v_x_2819_);
lean_dec_ref(v_params_2818_);
lean_dec_ref(v_argsPacker_2816_);
lean_dec_ref(v___x_2814_);
lean_dec(v___x_2812_);
return v_res_2825_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2836_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2837_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5));
v___x_2838_ = l_Lean_Name_append(v___x_2837_, v___x_2836_);
return v___x_2838_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7));
v___x_2841_ = l_Lean_stringToMessageData(v___x_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(lean_object* v_fixedParamPerms_2842_, lean_object* v_unaryPreDefNonRec_2843_, lean_object* v_us_2844_, lean_object* v_argsPacker_2845_, size_t v_sz_2846_, size_t v_i_2847_, lean_object* v_bs_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
uint8_t v___x_2854_; 
v___x_2854_ = lean_usize_dec_lt(v_i_2847_, v_sz_2846_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; 
lean_dec_ref(v_argsPacker_2845_);
lean_dec(v_us_2844_);
lean_dec_ref(v_unaryPreDefNonRec_2843_);
v___x_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2855_, 0, v_bs_2848_);
return v___x_2855_;
}
else
{
lean_object* v_v_2856_; lean_object* v_perms_2857_; lean_object* v_ref_2858_; uint8_t v_kind_2859_; lean_object* v_levelParams_2860_; lean_object* v_modifiers_2861_; lean_object* v_declName_2862_; lean_object* v_binders_2863_; lean_object* v_numSectionVars_2864_; lean_object* v_type_2865_; lean_object* v_termination_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2918_; 
v_v_2856_ = lean_array_uget(v_bs_2848_, v_i_2847_);
v_perms_2857_ = lean_ctor_get(v_fixedParamPerms_2842_, 1);
v_ref_2858_ = lean_ctor_get(v_v_2856_, 0);
v_kind_2859_ = lean_ctor_get_uint8(v_v_2856_, sizeof(void*)*9);
v_levelParams_2860_ = lean_ctor_get(v_v_2856_, 1);
v_modifiers_2861_ = lean_ctor_get(v_v_2856_, 2);
v_declName_2862_ = lean_ctor_get(v_v_2856_, 3);
v_binders_2863_ = lean_ctor_get(v_v_2856_, 4);
v_numSectionVars_2864_ = lean_ctor_get(v_v_2856_, 5);
v_type_2865_ = lean_ctor_get(v_v_2856_, 6);
v_termination_2866_ = lean_ctor_get(v_v_2856_, 8);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_v_2856_);
if (v_isSharedCheck_2918_ == 0)
{
lean_object* v_unused_2919_; 
v_unused_2919_ = lean_ctor_get(v_v_2856_, 7);
lean_dec(v_unused_2919_);
v___x_2868_ = v_v_2856_;
v_isShared_2869_ = v_isSharedCheck_2918_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_termination_2866_);
lean_inc(v_type_2865_);
lean_inc(v_numSectionVars_2864_);
lean_inc(v_binders_2863_);
lean_inc(v_declName_2862_);
lean_inc(v_modifiers_2861_);
lean_inc(v_levelParams_2860_);
lean_inc(v_ref_2858_);
lean_dec(v_v_2856_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2918_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; lean_object* v_bs_x27_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___f_2876_; lean_object* v___x_2877_; uint8_t v___x_2878_; lean_object* v___x_2879_; 
v___x_2870_ = lean_unsigned_to_nat(0u);
v_bs_x27_2871_ = lean_array_uset(v_bs_2848_, v_i_2847_, v___x_2870_);
v___x_2872_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2873_ = lean_usize_to_nat(v_i_2847_);
v___x_2874_ = lean_array_get_borrowed(v___x_2872_, v_perms_2857_, v___x_2873_);
v___x_2875_ = lean_array_get_size(v___x_2874_);
lean_inc_ref(v_argsPacker_2845_);
lean_inc(v_us_2844_);
lean_inc(v___x_2874_);
lean_inc_ref(v_unaryPreDefNonRec_2843_);
v___f_2876_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2876_, 0, v___x_2875_);
lean_closure_set(v___f_2876_, 1, v_unaryPreDefNonRec_2843_);
lean_closure_set(v___f_2876_, 2, v___x_2874_);
lean_closure_set(v___f_2876_, 3, v_us_2844_);
lean_closure_set(v___f_2876_, 4, v_argsPacker_2845_);
lean_closure_set(v___f_2876_, 5, v___x_2873_);
v___x_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2875_);
v___x_2878_ = 0;
lean_inc_ref(v_type_2865_);
v___x_2879_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2865_, v___x_2877_, v___f_2876_, v___x_2878_, v___x_2878_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v_toCold_2889_; lean_object* v_options_2890_; uint8_t v_hasTrace_2891_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
lean_dec_ref_known(v___x_2879_, 1);
v_toCold_2889_ = lean_ctor_get(v___y_2851_, 0);
v_options_2890_ = lean_ctor_get(v_toCold_2889_, 2);
v_hasTrace_2891_ = lean_ctor_get_uint8(v_options_2890_, sizeof(void*)*1);
if (v_hasTrace_2891_ == 0)
{
goto v___jp_2881_;
}
else
{
lean_object* v_inheritedTraceOptions_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; 
v_inheritedTraceOptions_2892_ = lean_ctor_get(v_toCold_2889_, 11);
v___x_2893_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2894_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6);
v___x_2895_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2892_, v_options_2890_, v___x_2894_);
if (v___x_2895_ == 0)
{
goto v___jp_2881_;
}
else
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
lean_inc(v_declName_2862_);
v___x_2896_ = l_Lean_MessageData_ofName(v_declName_2862_);
v___x_2897_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8);
v___x_2898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2896_);
lean_ctor_set(v___x_2898_, 1, v___x_2897_);
lean_inc(v_a_2880_);
v___x_2899_ = l_Lean_MessageData_ofExpr(v_a_2880_);
v___x_2900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2898_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
v___x_2901_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v___x_2893_, v___x_2900_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_dec_ref_known(v___x_2901_, 1);
goto v___jp_2881_;
}
else
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
lean_dec(v_a_2880_);
lean_dec_ref(v_bs_x27_2871_);
lean_del_object(v___x_2868_);
lean_dec_ref(v_termination_2866_);
lean_dec_ref(v_type_2865_);
lean_dec(v_numSectionVars_2864_);
lean_dec(v_binders_2863_);
lean_dec(v_declName_2862_);
lean_dec_ref(v_modifiers_2861_);
lean_dec(v_levelParams_2860_);
lean_dec(v_ref_2858_);
lean_dec_ref(v_argsPacker_2845_);
lean_dec(v_us_2844_);
lean_dec_ref(v_unaryPreDefNonRec_2843_);
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2901_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2901_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
}
v___jp_2881_:
{
lean_object* v___x_2883_; 
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 7, v_a_2880_);
v___x_2883_ = v___x_2868_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_ref_2858_);
lean_ctor_set(v_reuseFailAlloc_2888_, 1, v_levelParams_2860_);
lean_ctor_set(v_reuseFailAlloc_2888_, 2, v_modifiers_2861_);
lean_ctor_set(v_reuseFailAlloc_2888_, 3, v_declName_2862_);
lean_ctor_set(v_reuseFailAlloc_2888_, 4, v_binders_2863_);
lean_ctor_set(v_reuseFailAlloc_2888_, 5, v_numSectionVars_2864_);
lean_ctor_set(v_reuseFailAlloc_2888_, 6, v_type_2865_);
lean_ctor_set(v_reuseFailAlloc_2888_, 7, v_a_2880_);
lean_ctor_set(v_reuseFailAlloc_2888_, 8, v_termination_2866_);
lean_ctor_set_uint8(v_reuseFailAlloc_2888_, sizeof(void*)*9, v_kind_2859_);
v___x_2883_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
size_t v___x_2884_; size_t v___x_2885_; lean_object* v___x_2886_; 
v___x_2884_ = ((size_t)1ULL);
v___x_2885_ = lean_usize_add(v_i_2847_, v___x_2884_);
v___x_2886_ = lean_array_uset(v_bs_x27_2871_, v_i_2847_, v___x_2883_);
v_i_2847_ = v___x_2885_;
v_bs_2848_ = v___x_2886_;
goto _start;
}
}
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_dec_ref(v_bs_x27_2871_);
lean_del_object(v___x_2868_);
lean_dec_ref(v_termination_2866_);
lean_dec_ref(v_type_2865_);
lean_dec(v_numSectionVars_2864_);
lean_dec(v_binders_2863_);
lean_dec(v_declName_2862_);
lean_dec_ref(v_modifiers_2861_);
lean_dec(v_levelParams_2860_);
lean_dec(v_ref_2858_);
lean_dec_ref(v_argsPacker_2845_);
lean_dec(v_us_2844_);
lean_dec_ref(v_unaryPreDefNonRec_2843_);
v_a_2910_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2879_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2879_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_2920_, lean_object* v_unaryPreDefNonRec_2921_, lean_object* v_us_2922_, lean_object* v_argsPacker_2923_, lean_object* v_sz_2924_, lean_object* v_i_2925_, lean_object* v_bs_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
size_t v_sz_boxed_2932_; size_t v_i_boxed_2933_; lean_object* v_res_2934_; 
v_sz_boxed_2932_ = lean_unbox_usize(v_sz_2924_);
lean_dec(v_sz_2924_);
v_i_boxed_2933_ = lean_unbox_usize(v_i_2925_);
lean_dec(v_i_2925_);
v_res_2934_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2920_, v_unaryPreDefNonRec_2921_, v_us_2922_, v_argsPacker_2923_, v_sz_boxed_2932_, v_i_boxed_2933_, v_bs_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec_ref(v_fixedParamPerms_2920_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(lean_object* v_unaryPreDefNonRec_2935_, lean_object* v_preDefs_2936_, lean_object* v_fixedParamPerms_2937_, lean_object* v_us_2938_, lean_object* v_argsPacker_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
lean_object* v___x_2945_; 
v___x_2945_ = l_Lean_Elab_addAsAxiom___redArg(v_unaryPreDefNonRec_2935_, v___y_2942_, v___y_2943_);
if (lean_obj_tag(v___x_2945_) == 0)
{
size_t v_sz_2946_; size_t v___x_2947_; lean_object* v___x_2948_; 
lean_dec_ref_known(v___x_2945_, 1);
v_sz_2946_ = lean_array_size(v_preDefs_2936_);
v___x_2947_ = ((size_t)0ULL);
v___x_2948_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2937_, v_unaryPreDefNonRec_2935_, v_us_2938_, v_argsPacker_2939_, v_sz_2946_, v___x_2947_, v_preDefs_2936_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
return v___x_2948_;
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec_ref(v_argsPacker_2939_);
lean_dec(v_us_2938_);
lean_dec_ref(v_preDefs_2936_);
lean_dec_ref(v_unaryPreDefNonRec_2935_);
v_a_2949_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2945_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2945_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed(lean_object* v_unaryPreDefNonRec_2957_, lean_object* v_preDefs_2958_, lean_object* v_fixedParamPerms_2959_, lean_object* v_us_2960_, lean_object* v_argsPacker_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(v_unaryPreDefNonRec_2957_, v_preDefs_2958_, v_fixedParamPerms_2959_, v_us_2960_, v_argsPacker_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec_ref(v_fixedParamPerms_2959_);
return v_res_2967_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2968_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2969_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0);
v___x_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
return v___x_2970_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2971_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
v___x_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
return v___x_2972_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
v___x_2974_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
lean_ctor_set(v___x_2974_, 2, v___x_2973_);
lean_ctor_set(v___x_2974_, 3, v___x_2973_);
lean_ctor_set(v___x_2974_, 4, v___x_2973_);
lean_ctor_set(v___x_2974_, 5, v___x_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(lean_object* v_env_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v___x_2979_; lean_object* v_nextMacroScope_2980_; lean_object* v_ngen_2981_; lean_object* v_auxDeclNGen_2982_; lean_object* v_traceState_2983_; lean_object* v_recordedDeps_2984_; lean_object* v_messages_2985_; lean_object* v_infoState_2986_; lean_object* v_snapshotTasks_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3013_; 
v___x_2979_ = lean_st_ref_take(v___y_2977_);
v_nextMacroScope_2980_ = lean_ctor_get(v___x_2979_, 1);
v_ngen_2981_ = lean_ctor_get(v___x_2979_, 2);
v_auxDeclNGen_2982_ = lean_ctor_get(v___x_2979_, 3);
v_traceState_2983_ = lean_ctor_get(v___x_2979_, 4);
v_recordedDeps_2984_ = lean_ctor_get(v___x_2979_, 6);
v_messages_2985_ = lean_ctor_get(v___x_2979_, 7);
v_infoState_2986_ = lean_ctor_get(v___x_2979_, 8);
v_snapshotTasks_2987_ = lean_ctor_get(v___x_2979_, 9);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3013_ == 0)
{
lean_object* v_unused_3014_; lean_object* v_unused_3015_; 
v_unused_3014_ = lean_ctor_get(v___x_2979_, 5);
lean_dec(v_unused_3014_);
v_unused_3015_ = lean_ctor_get(v___x_2979_, 0);
lean_dec(v_unused_3015_);
v___x_2989_ = v___x_2979_;
v_isShared_2990_ = v_isSharedCheck_3013_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_snapshotTasks_2987_);
lean_inc(v_infoState_2986_);
lean_inc(v_messages_2985_);
lean_inc(v_recordedDeps_2984_);
lean_inc(v_traceState_2983_);
lean_inc(v_auxDeclNGen_2982_);
lean_inc(v_ngen_2981_);
lean_inc(v_nextMacroScope_2980_);
lean_dec(v___x_2979_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3013_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2991_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 5, v___x_2991_);
lean_ctor_set(v___x_2989_, 0, v_env_2975_);
v___x_2993_ = v___x_2989_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_env_2975_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_nextMacroScope_2980_);
lean_ctor_set(v_reuseFailAlloc_3012_, 2, v_ngen_2981_);
lean_ctor_set(v_reuseFailAlloc_3012_, 3, v_auxDeclNGen_2982_);
lean_ctor_set(v_reuseFailAlloc_3012_, 4, v_traceState_2983_);
lean_ctor_set(v_reuseFailAlloc_3012_, 5, v___x_2991_);
lean_ctor_set(v_reuseFailAlloc_3012_, 6, v_recordedDeps_2984_);
lean_ctor_set(v_reuseFailAlloc_3012_, 7, v_messages_2985_);
lean_ctor_set(v_reuseFailAlloc_3012_, 8, v_infoState_2986_);
lean_ctor_set(v_reuseFailAlloc_3012_, 9, v_snapshotTasks_2987_);
v___x_2993_ = v_reuseFailAlloc_3012_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v_mctx_2996_; lean_object* v_zetaDeltaFVarIds_2997_; lean_object* v_postponed_2998_; lean_object* v_diag_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3010_; 
v___x_2994_ = lean_st_ref_put(v___y_2977_, v___x_2993_);
v___x_2995_ = lean_st_ref_take(v___y_2976_);
v_mctx_2996_ = lean_ctor_get(v___x_2995_, 0);
v_zetaDeltaFVarIds_2997_ = lean_ctor_get(v___x_2995_, 2);
v_postponed_2998_ = lean_ctor_get(v___x_2995_, 3);
v_diag_2999_ = lean_ctor_get(v___x_2995_, 4);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3010_ == 0)
{
lean_object* v_unused_3011_; 
v_unused_3011_ = lean_ctor_get(v___x_2995_, 1);
lean_dec(v_unused_3011_);
v___x_3001_ = v___x_2995_;
v_isShared_3002_ = v_isSharedCheck_3010_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_diag_2999_);
lean_inc(v_postponed_2998_);
lean_inc(v_zetaDeltaFVarIds_2997_);
lean_inc(v_mctx_2996_);
lean_dec(v___x_2995_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3010_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3006_; 
v___x_3003_ = lean_box(0);
v___x_3004_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 1, v___x_3004_);
v___x_3006_ = v___x_3001_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_mctx_2996_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v___x_3004_);
lean_ctor_set(v_reuseFailAlloc_3009_, 2, v_zetaDeltaFVarIds_2997_);
lean_ctor_set(v_reuseFailAlloc_3009_, 3, v_postponed_2998_);
lean_ctor_set(v_reuseFailAlloc_3009_, 4, v_diag_2999_);
v___x_3006_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = lean_st_ref_put(v___y_2976_, v___x_3006_);
v___x_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3003_);
return v___x_3008_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___boxed(lean_object* v_env_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec(v___y_3017_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(lean_object* v_env_3021_, lean_object* v_x_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v___x_3028_; lean_object* v_env_3029_; lean_object* v_a_3031_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3028_ = lean_st_ref_get(v___y_3026_);
v_env_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc_ref(v_env_3029_);
lean_dec(v___x_3028_);
v___x_3041_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3021_, v___y_3024_, v___y_3026_);
lean_dec_ref(v___x_3041_);
lean_inc(v___y_3026_);
lean_inc_ref(v___y_3025_);
lean_inc(v___y_3024_);
lean_inc_ref(v___y_3023_);
v___x_3042_ = lean_apply_5(v_x_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, lean_box(0));
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___x_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref_known(v___x_3042_, 1);
v___x_3044_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3029_, v___y_3024_, v___y_3026_);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3051_ == 0)
{
lean_object* v_unused_3052_; 
v_unused_3052_ = lean_ctor_get(v___x_3044_, 0);
lean_dec(v_unused_3052_);
v___x_3046_ = v___x_3044_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_dec(v___x_3044_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 0, v_a_3043_);
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3043_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
else
{
lean_object* v_a_3053_; 
v_a_3053_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3053_);
lean_dec_ref_known(v___x_3042_, 1);
v_a_3031_ = v_a_3053_;
goto v___jp_3030_;
}
v___jp_3030_:
{
lean_object* v___x_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
v___x_3032_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3029_, v___y_3024_, v___y_3026_);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3039_ == 0)
{
lean_object* v_unused_3040_; 
v_unused_3040_ = lean_ctor_get(v___x_3032_, 0);
lean_dec(v_unused_3040_);
v___x_3034_ = v___x_3032_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_dec(v___x_3032_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
lean_ctor_set_tag(v___x_3034_, 1);
lean_ctor_set(v___x_3034_, 0, v_a_3031_);
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3031_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___boxed(lean_object* v_env_3054_, lean_object* v_x_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_3054_, v_x_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object* v_fixedParamPerms_3062_, lean_object* v_argsPacker_3063_, lean_object* v_preDefs_3064_, lean_object* v_unaryPreDefNonRec_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v_levelParams_3071_; lean_object* v___x_3072_; lean_object* v_us_3073_; lean_object* v___f_3074_; lean_object* v___x_3075_; lean_object* v_env_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v_levelParams_3071_ = lean_ctor_get(v_unaryPreDefNonRec_3065_, 1);
v___x_3072_ = lean_box(0);
lean_inc(v_levelParams_3071_);
v_us_3073_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_3071_, v___x_3072_);
v___f_3074_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3074_, 0, v_unaryPreDefNonRec_3065_);
lean_closure_set(v___f_3074_, 1, v_preDefs_3064_);
lean_closure_set(v___f_3074_, 2, v_fixedParamPerms_3062_);
lean_closure_set(v___f_3074_, 3, v_us_3073_);
lean_closure_set(v___f_3074_, 4, v_argsPacker_3063_);
v___x_3075_ = lean_st_ref_get(v_a_3069_);
v_env_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc_ref(v_env_3076_);
lean_dec(v___x_3075_);
v___x_3077_ = l_Lean_Environment_unlockAsync(v_env_3076_);
v___x_3078_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v___x_3077_, v___f_3074_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___boxed(lean_object* v_fixedParamPerms_3079_, lean_object* v_argsPacker_3080_, lean_object* v_preDefs_3081_, lean_object* v_unaryPreDefNonRec_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fixedParamPerms_3079_, v_argsPacker_3080_, v_preDefs_3081_, v_unaryPreDefNonRec_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(lean_object* v_fixedParamPerms_3089_, lean_object* v_unaryPreDefNonRec_3090_, lean_object* v_us_3091_, lean_object* v_argsPacker_3092_, lean_object* v_as_3093_, size_t v_sz_3094_, size_t v_i_3095_, lean_object* v_bs_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v___x_3102_; 
v___x_3102_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_3089_, v_unaryPreDefNonRec_3090_, v_us_3091_, v_argsPacker_3092_, v_sz_3094_, v_i_3095_, v_bs_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___boxed(lean_object* v_fixedParamPerms_3103_, lean_object* v_unaryPreDefNonRec_3104_, lean_object* v_us_3105_, lean_object* v_argsPacker_3106_, lean_object* v_as_3107_, lean_object* v_sz_3108_, lean_object* v_i_3109_, lean_object* v_bs_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
size_t v_sz_boxed_3116_; size_t v_i_boxed_3117_; lean_object* v_res_3118_; 
v_sz_boxed_3116_ = lean_unbox_usize(v_sz_3108_);
lean_dec(v_sz_3108_);
v_i_boxed_3117_ = lean_unbox_usize(v_i_3109_);
lean_dec(v_i_3109_);
v_res_3118_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(v_fixedParamPerms_3103_, v_unaryPreDefNonRec_3104_, v_us_3105_, v_argsPacker_3106_, v_as_3107_, v_sz_boxed_3116_, v_i_boxed_3117_, v_bs_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec_ref(v_as_3107_);
lean_dec_ref(v_fixedParamPerms_3103_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(lean_object* v_env_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v___x_3125_; 
v___x_3125_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3119_, v___y_3121_, v___y_3123_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___boxed(lean_object* v_env_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(v_env_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(lean_object* v_00_u03b1_3133_, lean_object* v_env_3134_, lean_object* v_x_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v___x_3141_; 
v___x_3141_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_3134_, v_x_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___boxed(lean_object* v_00_u03b1_3142_, lean_object* v_env_3143_, lean_object* v_x_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(v_00_u03b1_3142_, v_env_3143_, v_x_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
return v_res_3150_;
}
}
lean_object* runtime_initialize_Lean_Meta_ArgsPacker(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Eqns(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_PackMutual(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_ArgsPacker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_WF_PackMutual(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_ArgsPacker(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Eqns(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_PackMutual(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_ArgsPacker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin);
}
#ifdef __cplusplus
}
#endif
