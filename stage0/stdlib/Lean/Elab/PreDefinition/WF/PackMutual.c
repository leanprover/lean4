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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(lean_object* v___x_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_544_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2___boxed(lean_object* v___x_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(v___x_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(lean_object* v_a_665_, lean_object* v_x_666_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg___boxed(lean_object* v_a_674_, lean_object* v_x_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_674_, v_x_675_);
lean_dec(v_x_675_);
lean_dec_ref(v_a_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(lean_object* v_m_677_, lean_object* v_a_678_){
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
v___x_694_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_678_, v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___boxed(lean_object* v_m_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_m_695_, v_a_696_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed(lean_object* v_fvars_837_, lean_object* v_pre_838_, lean_object* v_post_839_, lean_object* v_usedLetOnly_840_, lean_object* v_skipConstInApp_841_, lean_object* v_skipInstances_842_, lean_object* v_body_843_, lean_object* v_x_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
uint8_t v_usedLetOnly_boxed_851_; uint8_t v_skipConstInApp_boxed_852_; uint8_t v_skipInstances_boxed_853_; lean_object* v_res_854_; 
v_usedLetOnly_boxed_851_ = lean_unbox(v_usedLetOnly_840_);
v_skipConstInApp_boxed_852_ = lean_unbox(v_skipConstInApp_841_);
v_skipInstances_boxed_853_ = lean_unbox(v_skipInstances_842_);
v_res_854_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(v_fvars_837_, v_pre_838_, v_post_839_, v_usedLetOnly_boxed_851_, v_skipConstInApp_boxed_852_, v_skipInstances_boxed_853_, v_body_843_, v_x_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(lean_object* v_fvars_858_, lean_object* v_pre_859_, lean_object* v_post_860_, uint8_t v_usedLetOnly_861_, uint8_t v_skipConstInApp_862_, uint8_t v_skipInstances_863_, lean_object* v_body_864_, lean_object* v_x_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = lean_array_push(v_fvars_858_, v_x_865_);
v___x_873_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_859_, v_post_860_, v_usedLetOnly_861_, v_skipConstInApp_862_, v_skipInstances_863_, v___x_872_, v_body_864_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed(lean_object* v_fvars_874_, lean_object* v_pre_875_, lean_object* v_post_876_, lean_object* v_usedLetOnly_877_, lean_object* v_skipConstInApp_878_, lean_object* v_skipInstances_879_, lean_object* v_body_880_, lean_object* v_x_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
uint8_t v_usedLetOnly_boxed_888_; uint8_t v_skipConstInApp_boxed_889_; uint8_t v_skipInstances_boxed_890_; lean_object* v_res_891_; 
v_usedLetOnly_boxed_888_ = lean_unbox(v_usedLetOnly_877_);
v_skipConstInApp_boxed_889_ = lean_unbox(v_skipConstInApp_878_);
v_skipInstances_boxed_890_ = lean_unbox(v_skipInstances_879_);
v_res_891_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(v_fvars_874_, v_pre_875_, v_post_876_, v_usedLetOnly_boxed_888_, v_skipConstInApp_boxed_889_, v_skipInstances_boxed_890_, v_body_880_, v_x_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(lean_object* v_pre_892_, lean_object* v_post_893_, uint8_t v_usedLetOnly_894_, uint8_t v_skipConstInApp_895_, uint8_t v_skipInstances_896_, lean_object* v_e_897_, lean_object* v_a_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v___x_904_; 
lean_inc_ref(v_post_893_);
lean_inc(v___y_902_);
lean_inc_ref(v___y_901_);
lean_inc(v___y_900_);
lean_inc_ref(v___y_899_);
lean_inc_ref(v_e_897_);
v___x_904_ = lean_apply_6(v_post_893_, v_e_897_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, lean_box(0));
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_923_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_923_ == 0)
{
v___x_907_ = v___x_904_;
v_isShared_908_ = v_isSharedCheck_923_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_904_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_923_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
switch(lean_obj_tag(v_a_905_))
{
case 0:
{
lean_object* v_e_909_; lean_object* v___x_911_; 
lean_dec_ref(v_e_897_);
lean_dec_ref(v_post_893_);
lean_dec_ref(v_pre_892_);
v_e_909_ = lean_ctor_get(v_a_905_, 0);
lean_inc_ref(v_e_909_);
lean_dec_ref_known(v_a_905_, 1);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v_e_909_);
v___x_911_ = v___x_907_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_e_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
case 1:
{
lean_object* v_e_913_; lean_object* v___x_914_; 
lean_del_object(v___x_907_);
lean_dec_ref(v_e_897_);
v_e_913_ = lean_ctor_get(v_a_905_, 0);
lean_inc_ref(v_e_913_);
lean_dec_ref_known(v_a_905_, 1);
v___x_914_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_892_, v_post_893_, v_usedLetOnly_894_, v_skipConstInApp_895_, v_skipInstances_896_, v_e_913_, v_a_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
return v___x_914_;
}
default: 
{
lean_object* v_e_x3f_915_; 
lean_dec_ref(v_post_893_);
lean_dec_ref(v_pre_892_);
v_e_x3f_915_ = lean_ctor_get(v_a_905_, 0);
lean_inc(v_e_x3f_915_);
lean_dec_ref_known(v_a_905_, 1);
if (lean_obj_tag(v_e_x3f_915_) == 0)
{
lean_object* v___x_917_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v_e_897_);
v___x_917_ = v___x_907_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_e_897_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
else
{
lean_object* v_val_919_; lean_object* v___x_921_; 
lean_dec_ref(v_e_897_);
v_val_919_ = lean_ctor_get(v_e_x3f_915_, 0);
lean_inc(v_val_919_);
lean_dec_ref_known(v_e_x3f_915_, 1);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v_val_919_);
v___x_921_ = v___x_907_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_val_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec_ref(v_e_897_);
lean_dec_ref(v_post_893_);
lean_dec_ref(v_pre_892_);
v_a_924_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_904_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_904_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(lean_object* v_pre_932_, lean_object* v_post_933_, uint8_t v_usedLetOnly_934_, uint8_t v_skipConstInApp_935_, uint8_t v_skipInstances_936_, lean_object* v_fvars_937_, lean_object* v_e_938_, lean_object* v_a_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
if (lean_obj_tag(v_e_938_) == 6)
{
lean_object* v_binderName_945_; lean_object* v_binderType_946_; lean_object* v_body_947_; uint8_t v_binderInfo_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___f_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_binderName_945_ = lean_ctor_get(v_e_938_, 0);
lean_inc(v_binderName_945_);
v_binderType_946_ = lean_ctor_get(v_e_938_, 1);
lean_inc_ref(v_binderType_946_);
v_body_947_ = lean_ctor_get(v_e_938_, 2);
lean_inc_ref(v_body_947_);
v_binderInfo_948_ = lean_ctor_get_uint8(v_e_938_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_938_, 3);
v___x_949_ = lean_box(v_usedLetOnly_934_);
v___x_950_ = lean_box(v_skipConstInApp_935_);
v___x_951_ = lean_box(v_skipInstances_936_);
lean_inc_ref(v_post_933_);
lean_inc_ref(v_pre_932_);
lean_inc_ref(v_fvars_937_);
v___f_952_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed), 14, 7);
lean_closure_set(v___f_952_, 0, v_fvars_937_);
lean_closure_set(v___f_952_, 1, v_pre_932_);
lean_closure_set(v___f_952_, 2, v_post_933_);
lean_closure_set(v___f_952_, 3, v___x_949_);
lean_closure_set(v___f_952_, 4, v___x_950_);
lean_closure_set(v___f_952_, 5, v___x_951_);
lean_closure_set(v___f_952_, 6, v_body_947_);
v___x_953_ = lean_expr_instantiate_rev(v_binderType_946_, v_fvars_937_);
lean_dec_ref(v_fvars_937_);
lean_dec_ref(v_binderType_946_);
v___x_954_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_932_, v_post_933_, v_usedLetOnly_934_, v_skipConstInApp_935_, v_skipInstances_936_, v___x_953_, v_a_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; uint8_t v___x_956_; lean_object* v___x_957_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v___x_954_, 1);
v___x_956_ = 0;
v___x_957_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_945_, v_binderInfo_948_, v_a_955_, v___f_952_, v___x_956_, v_a_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
return v___x_957_;
}
else
{
lean_dec_ref(v___f_952_);
lean_dec(v_binderName_945_);
return v___x_954_;
}
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_expr_instantiate_rev(v_e_938_, v_fvars_937_);
lean_dec_ref(v_e_938_);
lean_inc_ref(v_post_933_);
lean_inc_ref(v_pre_932_);
v___x_959_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_932_, v_post_933_, v_usedLetOnly_934_, v_skipConstInApp_935_, v_skipInstances_936_, v___x_958_, v_a_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; uint8_t v___x_961_; uint8_t v___x_962_; uint8_t v___x_963_; lean_object* v___x_964_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref_known(v___x_959_, 1);
v___x_961_ = 0;
v___x_962_ = 1;
v___x_963_ = 1;
v___x_964_ = l_Lean_Meta_mkLambdaFVars(v_fvars_937_, v_a_960_, v___x_961_, v_usedLetOnly_934_, v___x_961_, v___x_962_, v___x_963_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
lean_dec_ref(v_fvars_937_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_966_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_964_, 1);
v___x_966_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_932_, v_post_933_, v_usedLetOnly_934_, v_skipConstInApp_935_, v_skipInstances_936_, v_a_965_, v_a_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
return v___x_966_;
}
else
{
lean_dec_ref(v_post_933_);
lean_dec_ref(v_pre_932_);
return v___x_964_;
}
}
else
{
lean_dec_ref(v_fvars_937_);
lean_dec_ref(v_post_933_);
lean_dec_ref(v_pre_932_);
return v___x_959_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(lean_object* v_fvars_967_, lean_object* v_pre_968_, lean_object* v_post_969_, uint8_t v_usedLetOnly_970_, uint8_t v_skipConstInApp_971_, uint8_t v_skipInstances_972_, lean_object* v_body_973_, lean_object* v_x_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_array_push(v_fvars_967_, v_x_974_);
v___x_982_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_968_, v_post_969_, v_usedLetOnly_970_, v_skipConstInApp_971_, v_skipInstances_972_, v___x_981_, v_body_973_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_983_, lean_object* v_pre_984_, lean_object* v_post_985_, lean_object* v_usedLetOnly_986_, lean_object* v_skipConstInApp_987_, lean_object* v_skipInstances_988_, lean_object* v_body_989_, lean_object* v_x_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
uint8_t v_usedLetOnly_boxed_997_; uint8_t v_skipConstInApp_boxed_998_; uint8_t v_skipInstances_boxed_999_; lean_object* v_res_1000_; 
v_usedLetOnly_boxed_997_ = lean_unbox(v_usedLetOnly_986_);
v_skipConstInApp_boxed_998_ = lean_unbox(v_skipConstInApp_987_);
v_skipInstances_boxed_999_ = lean_unbox(v_skipInstances_988_);
v_res_1000_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(v_fvars_983_, v_pre_984_, v_post_985_, v_usedLetOnly_boxed_997_, v_skipConstInApp_boxed_998_, v_skipInstances_boxed_999_, v_body_989_, v_x_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(lean_object* v_pre_1001_, lean_object* v_post_1002_, uint8_t v_usedLetOnly_1003_, uint8_t v_skipConstInApp_1004_, uint8_t v_skipInstances_1005_, lean_object* v_fvars_1006_, lean_object* v_e_1007_, lean_object* v_a_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
if (lean_obj_tag(v_e_1007_) == 8)
{
lean_object* v_declName_1014_; lean_object* v_type_1015_; lean_object* v_value_1016_; lean_object* v_body_1017_; uint8_t v_nondep_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___f_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_declName_1014_ = lean_ctor_get(v_e_1007_, 0);
lean_inc(v_declName_1014_);
v_type_1015_ = lean_ctor_get(v_e_1007_, 1);
lean_inc_ref(v_type_1015_);
v_value_1016_ = lean_ctor_get(v_e_1007_, 2);
lean_inc_ref(v_value_1016_);
v_body_1017_ = lean_ctor_get(v_e_1007_, 3);
lean_inc_ref(v_body_1017_);
v_nondep_1018_ = lean_ctor_get_uint8(v_e_1007_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1007_, 4);
v___x_1019_ = lean_box(v_usedLetOnly_1003_);
v___x_1020_ = lean_box(v_skipConstInApp_1004_);
v___x_1021_ = lean_box(v_skipInstances_1005_);
lean_inc_ref_n(v_post_1002_, 2);
lean_inc_ref_n(v_pre_1001_, 2);
lean_inc_ref(v_fvars_1006_);
v___f_1022_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1022_, 0, v_fvars_1006_);
lean_closure_set(v___f_1022_, 1, v_pre_1001_);
lean_closure_set(v___f_1022_, 2, v_post_1002_);
lean_closure_set(v___f_1022_, 3, v___x_1019_);
lean_closure_set(v___f_1022_, 4, v___x_1020_);
lean_closure_set(v___f_1022_, 5, v___x_1021_);
lean_closure_set(v___f_1022_, 6, v_body_1017_);
v___x_1023_ = lean_expr_instantiate_rev(v_type_1015_, v_fvars_1006_);
lean_dec_ref(v_type_1015_);
v___x_1024_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1001_, v_post_1002_, v_usedLetOnly_1003_, v_skipConstInApp_1004_, v_skipInstances_1005_, v___x_1023_, v_a_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v___x_1026_ = lean_expr_instantiate_rev(v_value_1016_, v_fvars_1006_);
lean_dec_ref(v_fvars_1006_);
lean_dec_ref(v_value_1016_);
v___x_1027_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1001_, v_post_1002_, v_usedLetOnly_1003_, v_skipConstInApp_1004_, v_skipInstances_1005_, v___x_1026_, v_a_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; uint8_t v___x_1029_; lean_object* v___x_1030_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
v___x_1029_ = 0;
v___x_1030_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_declName_1014_, v_a_1025_, v_a_1028_, v___f_1022_, v_nondep_1018_, v___x_1029_, v_a_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
return v___x_1030_;
}
else
{
lean_dec(v_a_1025_);
lean_dec_ref(v___f_1022_);
lean_dec(v_declName_1014_);
return v___x_1027_;
}
}
else
{
lean_dec_ref(v___f_1022_);
lean_dec_ref(v_value_1016_);
lean_dec(v_declName_1014_);
lean_dec_ref(v_fvars_1006_);
lean_dec_ref(v_post_1002_);
lean_dec_ref(v_pre_1001_);
return v___x_1024_;
}
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_expr_instantiate_rev(v_e_1007_, v_fvars_1006_);
lean_dec_ref(v_e_1007_);
lean_inc_ref(v_post_1002_);
lean_inc_ref(v_pre_1001_);
v___x_1032_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1001_, v_post_1002_, v_usedLetOnly_1003_, v_skipConstInApp_1004_, v_skipInstances_1005_, v___x_1031_, v_a_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; uint8_t v___x_1034_; uint8_t v___x_1035_; lean_object* v___x_1036_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___x_1032_, 1);
v___x_1034_ = 0;
v___x_1035_ = 1;
v___x_1036_ = l_Lean_Meta_mkLetFVars(v_fvars_1006_, v_a_1033_, v_usedLetOnly_1003_, v___x_1034_, v___x_1035_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec_ref(v_fvars_1006_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1038_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref_known(v___x_1036_, 1);
v___x_1038_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1001_, v_post_1002_, v_usedLetOnly_1003_, v_skipConstInApp_1004_, v_skipInstances_1005_, v_a_1037_, v_a_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
return v___x_1038_;
}
else
{
lean_dec_ref(v_post_1002_);
lean_dec_ref(v_pre_1001_);
return v___x_1036_;
}
}
else
{
lean_dec_ref(v_fvars_1006_);
lean_dec_ref(v_post_1002_);
lean_dec_ref(v_pre_1001_);
return v___x_1032_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(lean_object* v_pre_1039_, lean_object* v_post_1040_, uint8_t v_usedLetOnly_1041_, uint8_t v_skipConstInApp_1042_, uint8_t v_skipInstances_1043_, size_t v_sz_1044_, size_t v_i_1045_, lean_object* v_bs_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
uint8_t v___x_1053_; 
v___x_1053_ = lean_usize_dec_lt(v_i_1045_, v_sz_1044_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; 
lean_dec_ref(v_post_1040_);
lean_dec_ref(v_pre_1039_);
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v_bs_1046_);
return v___x_1054_;
}
else
{
lean_object* v_v_1055_; lean_object* v___x_1056_; lean_object* v_bs_x27_1057_; lean_object* v___x_1058_; 
v_v_1055_ = lean_array_uget(v_bs_1046_, v_i_1045_);
v___x_1056_ = lean_unsigned_to_nat(0u);
v_bs_x27_1057_ = lean_array_uset(v_bs_1046_, v_i_1045_, v___x_1056_);
lean_inc_ref(v_post_1040_);
lean_inc_ref(v_pre_1039_);
v___x_1058_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1039_, v_post_1040_, v_usedLetOnly_1041_, v_skipConstInApp_1042_, v_skipInstances_1043_, v_v_1055_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; size_t v___x_1060_; size_t v___x_1061_; lean_object* v___x_1062_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref_known(v___x_1058_, 1);
v___x_1060_ = ((size_t)1ULL);
v___x_1061_ = lean_usize_add(v_i_1045_, v___x_1060_);
v___x_1062_ = lean_array_uset(v_bs_x27_1057_, v_i_1045_, v_a_1059_);
v_i_1045_ = v___x_1061_;
v_bs_1046_ = v___x_1062_;
goto _start;
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec_ref(v_bs_x27_1057_);
lean_dec_ref(v_post_1040_);
lean_dec_ref(v_pre_1039_);
v_a_1064_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1058_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1058_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(lean_object* v_pre_1072_, lean_object* v_post_1073_, uint8_t v_usedLetOnly_1074_, uint8_t v_skipConstInApp_1075_, uint8_t v_skipInstances_1076_, lean_object* v___x_1077_, lean_object* v___y_1078_, lean_object* v_b_1079_, lean_object* v_a_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1072_, v_post_1073_, v_usedLetOnly_1074_, v_skipConstInApp_1075_, v_skipInstances_1076_, v___x_1077_, v___y_1078_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1096_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1096_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1096_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1091_ = lean_array_fset(v_b_1079_, v_a_1080_, v_a_1087_);
v___x_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1092_);
v___x_1094_ = v___x_1089_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec_ref(v_b_1079_);
v_a_1097_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1086_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1086_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed(lean_object* v_pre_1105_, lean_object* v_post_1106_, lean_object* v_usedLetOnly_1107_, lean_object* v_skipConstInApp_1108_, lean_object* v_skipInstances_1109_, lean_object* v___x_1110_, lean_object* v___y_1111_, lean_object* v_b_1112_, lean_object* v_a_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
uint8_t v_usedLetOnly_boxed_1119_; uint8_t v_skipConstInApp_boxed_1120_; uint8_t v_skipInstances_boxed_1121_; lean_object* v_res_1122_; 
v_usedLetOnly_boxed_1119_ = lean_unbox(v_usedLetOnly_1107_);
v_skipConstInApp_boxed_1120_ = lean_unbox(v_skipConstInApp_1108_);
v_skipInstances_boxed_1121_ = lean_unbox(v_skipInstances_1109_);
v_res_1122_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(v_pre_1105_, v_post_1106_, v_usedLetOnly_boxed_1119_, v_skipConstInApp_boxed_1120_, v_skipInstances_boxed_1121_, v___x_1110_, v___y_1111_, v_b_1112_, v_a_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v_a_1113_);
lean_dec(v___y_1111_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(lean_object* v_upperBound_1123_, lean_object* v___x_1124_, lean_object* v_pre_1125_, lean_object* v_post_1126_, uint8_t v_usedLetOnly_1127_, uint8_t v_skipConstInApp_1128_, uint8_t v_skipInstances_1129_, lean_object* v_a_1130_, lean_object* v_b_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v___y_1139_; uint8_t v___x_1162_; 
v___x_1162_ = lean_nat_dec_lt(v_a_1130_, v_upperBound_1123_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; 
lean_dec(v_a_1130_);
lean_dec_ref(v_post_1126_);
lean_dec_ref(v_pre_1125_);
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v_b_1131_);
return v___x_1163_;
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1164_ = lean_array_fget_borrowed(v_b_1131_, v_a_1130_);
v___x_1165_ = lean_array_get_size(v___x_1124_);
v___x_1166_ = lean_nat_dec_lt(v_a_1130_, v___x_1165_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___f_1170_; 
lean_inc(v___x_1164_);
v___x_1167_ = lean_box(v_usedLetOnly_1127_);
v___x_1168_ = lean_box(v_skipConstInApp_1128_);
v___x_1169_ = lean_box(v_skipInstances_1129_);
lean_inc(v_a_1130_);
lean_inc(v___y_1132_);
lean_inc_ref(v_post_1126_);
lean_inc_ref(v_pre_1125_);
v___f_1170_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1170_, 0, v_pre_1125_);
lean_closure_set(v___f_1170_, 1, v_post_1126_);
lean_closure_set(v___f_1170_, 2, v___x_1167_);
lean_closure_set(v___f_1170_, 3, v___x_1168_);
lean_closure_set(v___f_1170_, 4, v___x_1169_);
lean_closure_set(v___f_1170_, 5, v___x_1164_);
lean_closure_set(v___f_1170_, 6, v___y_1132_);
lean_closure_set(v___f_1170_, 7, v_b_1131_);
lean_closure_set(v___f_1170_, 8, v_a_1130_);
v___y_1139_ = v___f_1170_;
goto v___jp_1138_;
}
else
{
lean_object* v___x_1171_; uint8_t v_isInstance_1172_; 
v___x_1171_ = lean_array_fget_borrowed(v___x_1124_, v_a_1130_);
v_isInstance_1172_ = lean_ctor_get_uint8(v___x_1171_, sizeof(void*)*1 + 4);
if (v_isInstance_1172_ == 0)
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___f_1176_; 
lean_inc(v___x_1164_);
v___x_1173_ = lean_box(v_usedLetOnly_1127_);
v___x_1174_ = lean_box(v_skipConstInApp_1128_);
v___x_1175_ = lean_box(v_skipInstances_1129_);
lean_inc(v_a_1130_);
lean_inc(v___y_1132_);
lean_inc_ref(v_post_1126_);
lean_inc_ref(v_pre_1125_);
v___f_1176_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1176_, 0, v_pre_1125_);
lean_closure_set(v___f_1176_, 1, v_post_1126_);
lean_closure_set(v___f_1176_, 2, v___x_1173_);
lean_closure_set(v___f_1176_, 3, v___x_1174_);
lean_closure_set(v___f_1176_, 4, v___x_1175_);
lean_closure_set(v___f_1176_, 5, v___x_1164_);
lean_closure_set(v___f_1176_, 6, v___y_1132_);
lean_closure_set(v___f_1176_, 7, v_b_1131_);
lean_closure_set(v___f_1176_, 8, v_a_1130_);
v___y_1139_ = v___f_1176_;
goto v___jp_1138_;
}
else
{
lean_object* v___x_1177_; lean_object* v___f_1178_; 
v___x_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1177_, 0, v_b_1131_);
v___f_1178_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1178_, 0, v___x_1177_);
v___y_1139_ = v___f_1178_;
goto v___jp_1138_;
}
}
}
v___jp_1138_:
{
lean_object* v___x_1140_; 
lean_inc(v___y_1136_);
lean_inc_ref(v___y_1135_);
lean_inc(v___y_1134_);
lean_inc_ref(v___y_1133_);
v___x_1140_ = lean_apply_5(v___y_1139_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, lean_box(0));
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1153_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1143_ = v___x_1140_;
v_isShared_1144_ = v_isSharedCheck_1153_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1140_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1153_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
if (lean_obj_tag(v_a_1141_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1147_; 
lean_dec(v_a_1130_);
lean_dec_ref(v_post_1126_);
lean_dec_ref(v_pre_1125_);
v_a_1145_ = lean_ctor_get(v_a_1141_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v_a_1141_, 1);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v_a_1145_);
v___x_1147_ = v___x_1143_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_del_object(v___x_1143_);
v_a_1149_ = lean_ctor_get(v_a_1141_, 0);
lean_inc(v_a_1149_);
lean_dec_ref_known(v_a_1141_, 1);
v___x_1150_ = lean_unsigned_to_nat(1u);
v___x_1151_ = lean_nat_add(v_a_1130_, v___x_1150_);
lean_dec(v_a_1130_);
v_a_1130_ = v___x_1151_;
v_b_1131_ = v_a_1149_;
goto _start;
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec(v_a_1130_);
lean_dec_ref(v_post_1126_);
lean_dec_ref(v_pre_1125_);
v_a_1154_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1140_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1140_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(uint8_t v_skipInstances_1179_, lean_object* v_pre_1180_, lean_object* v_post_1181_, uint8_t v_usedLetOnly_1182_, uint8_t v_skipConstInApp_1183_, lean_object* v_x_1184_, lean_object* v_x_1185_, lean_object* v_x_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_f_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; 
if (lean_obj_tag(v_x_1184_) == 5)
{
lean_object* v_fn_1242_; lean_object* v_arg_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v_fn_1242_ = lean_ctor_get(v_x_1184_, 0);
lean_inc_ref(v_fn_1242_);
v_arg_1243_ = lean_ctor_get(v_x_1184_, 1);
lean_inc_ref(v_arg_1243_);
lean_dec_ref_known(v_x_1184_, 2);
v___x_1244_ = lean_array_set(v_x_1185_, v_x_1186_, v_arg_1243_);
v___x_1245_ = lean_unsigned_to_nat(1u);
v___x_1246_ = lean_nat_sub(v_x_1186_, v___x_1245_);
lean_dec(v_x_1186_);
v_x_1184_ = v_fn_1242_;
v_x_1185_ = v___x_1244_;
v_x_1186_ = v___x_1246_;
goto _start;
}
else
{
lean_dec(v_x_1186_);
if (v_skipConstInApp_1183_ == 0)
{
goto v___jp_1239_;
}
else
{
uint8_t v___x_1248_; 
v___x_1248_ = l_Lean_Expr_isConst(v_x_1184_);
if (v___x_1248_ == 0)
{
goto v___jp_1239_;
}
else
{
v_f_1194_ = v_x_1184_;
v___y_1195_ = v___y_1187_;
v___y_1196_ = v___y_1188_;
v___y_1197_ = v___y_1189_;
v___y_1198_ = v___y_1190_;
v___y_1199_ = v___y_1191_;
goto v___jp_1193_;
}
}
}
v___jp_1193_:
{
if (v_skipInstances_1179_ == 0)
{
size_t v_sz_1200_; size_t v___x_1201_; lean_object* v___x_1202_; 
v_sz_1200_ = lean_array_size(v_x_1185_);
v___x_1201_ = ((size_t)0ULL);
lean_inc_ref(v_post_1181_);
lean_inc_ref(v_pre_1180_);
v___x_1202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_1180_, v_post_1181_, v_usedLetOnly_1182_, v_skipConstInApp_1183_, v_skipInstances_1179_, v_sz_1200_, v___x_1201_, v_x_1185_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
lean_dec_ref_known(v___x_1202_, 1);
v___x_1204_ = l_Lean_mkAppN(v_f_1194_, v_a_1203_);
lean_dec(v_a_1203_);
v___x_1205_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1180_, v_post_1181_, v_usedLetOnly_1182_, v_skipConstInApp_1183_, v_skipInstances_1179_, v___x_1204_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
return v___x_1205_;
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec_ref(v_f_1194_);
lean_dec_ref(v_post_1181_);
lean_dec_ref(v_pre_1180_);
v_a_1206_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1202_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1202_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
else
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = lean_array_get_size(v_x_1185_);
lean_inc_ref(v_f_1194_);
v___x_1215_ = l_Lean_Meta_getFunInfoNArgs(v_f_1194_, v___x_1214_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v_paramInfo_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1215_, 1);
v_paramInfo_1217_ = lean_ctor_get(v_a_1216_, 0);
lean_inc_ref(v_paramInfo_1217_);
lean_dec(v_a_1216_);
v___x_1218_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1181_);
lean_inc_ref(v_pre_1180_);
v___x_1219_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v___x_1214_, v_paramInfo_1217_, v_pre_1180_, v_post_1181_, v_usedLetOnly_1182_, v_skipConstInApp_1183_, v_skipInstances_1179_, v___x_1218_, v_x_1185_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec_ref(v_paramInfo_1217_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v___x_1219_, 1);
v___x_1221_ = l_Lean_mkAppN(v_f_1194_, v_a_1220_);
lean_dec(v_a_1220_);
v___x_1222_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1180_, v_post_1181_, v_usedLetOnly_1182_, v_skipConstInApp_1183_, v_skipInstances_1179_, v___x_1221_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
return v___x_1222_;
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec_ref(v_f_1194_);
lean_dec_ref(v_post_1181_);
lean_dec_ref(v_pre_1180_);
v_a_1223_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1219_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1219_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec_ref(v_f_1194_);
lean_dec_ref(v_x_1185_);
lean_dec_ref(v_post_1181_);
lean_dec_ref(v_pre_1180_);
v_a_1231_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1215_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1215_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
v___jp_1239_:
{
lean_object* v___x_1240_; 
lean_inc_ref(v_post_1181_);
lean_inc_ref(v_pre_1180_);
v___x_1240_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1180_, v_post_1181_, v_usedLetOnly_1182_, v_skipConstInApp_1183_, v_skipInstances_1179_, v_x_1184_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref_known(v___x_1240_, 1);
v_f_1194_ = v_a_1241_;
v___y_1195_ = v___y_1187_;
v___y_1196_ = v___y_1188_;
v___y_1197_ = v___y_1189_;
v___y_1198_ = v___y_1190_;
v___y_1199_ = v___y_1191_;
goto v___jp_1193_;
}
else
{
lean_dec_ref(v_x_1185_);
lean_dec_ref(v_post_1181_);
lean_dec_ref(v_pre_1180_);
return v___x_1240_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(lean_object* v___x_1249_, lean_object* v_pre_1250_, lean_object* v_e_1251_, lean_object* v_post_1252_, uint8_t v_usedLetOnly_1253_, uint8_t v_skipConstInApp_1254_, uint8_t v_skipInstances_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_Core_checkSystem(v___x_1249_, v___y_1259_, v___y_1260_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v___x_1263_; 
lean_dec_ref_known(v___x_1262_, 1);
lean_inc_ref(v_pre_1250_);
lean_inc(v___y_1260_);
lean_inc_ref(v___y_1259_);
lean_inc(v___y_1258_);
lean_inc_ref(v___y_1257_);
lean_inc_ref(v_e_1251_);
v___x_1263_ = lean_apply_6(v_pre_1250_, v_e_1251_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, lean_box(0));
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1312_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1312_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1312_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___y_1269_; 
switch(lean_obj_tag(v_a_1264_))
{
case 0:
{
lean_object* v_e_1304_; lean_object* v___x_1306_; 
lean_dec_ref(v_post_1252_);
lean_dec_ref(v_e_1251_);
lean_dec_ref(v_pre_1250_);
v_e_1304_ = lean_ctor_get(v_a_1264_, 0);
lean_inc_ref(v_e_1304_);
lean_dec_ref_known(v_a_1264_, 1);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v_e_1304_);
v___x_1306_ = v___x_1266_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_e_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
case 1:
{
lean_object* v_e_1308_; lean_object* v___x_1309_; 
lean_del_object(v___x_1266_);
lean_dec_ref(v_e_1251_);
v_e_1308_ = lean_ctor_get(v_a_1264_, 0);
lean_inc_ref(v_e_1308_);
lean_dec_ref_known(v_a_1264_, 1);
v___x_1309_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1250_, v_post_1252_, v_usedLetOnly_1253_, v_skipConstInApp_1254_, v_skipInstances_1255_, v_e_1308_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
return v___x_1309_;
}
default: 
{
lean_object* v_e_x3f_1310_; 
lean_del_object(v___x_1266_);
v_e_x3f_1310_ = lean_ctor_get(v_a_1264_, 0);
lean_inc(v_e_x3f_1310_);
lean_dec_ref_known(v_a_1264_, 1);
if (lean_obj_tag(v_e_x3f_1310_) == 0)
{
v___y_1269_ = v_e_1251_;
goto v___jp_1268_;
}
else
{
lean_object* v_val_1311_; 
lean_dec_ref(v_e_1251_);
v_val_1311_ = lean_ctor_get(v_e_x3f_1310_, 0);
lean_inc(v_val_1311_);
lean_dec_ref_known(v_e_x3f_1310_, 1);
v___y_1269_ = v_val_1311_;
goto v___jp_1268_;
}
}
}
v___jp_1268_:
{
switch(lean_obj_tag(v___y_1269_))
{
case 7:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1271_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1250_, v_post_1252_, v_usedLetOnly_1253_, v_skipConstInApp_1254_, v_skipInstances_1255_, v___x_1270_, v___y_1269_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
return v___x_1271_;
}
case 6:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1273_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1250_, v_post_1252_, v_usedLetOnly_1253_, v_skipConstInApp_1254_, v_skipInstances_1255_, v___x_1272_, v___y_1269_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
return v___x_1273_;
}
case 8:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1275_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1250_, v_post_1252_, v_usedLetOnly_1253_, v_skipConstInApp_1254_, v_skipInstances_1255_, v___x_1274_, v___y_1269_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
return v___x_1275_;
}
case 5:
{
lean_object* v_dummy_1276_; lean_object* v_nargs_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v_dummy_1276_ = lean_obj_once(&l_Lean_Elab_WF_withAppN___closed__0, &l_Lean_Elab_WF_withAppN___closed__0_once, _init_l_Lean_Elab_WF_withAppN___closed__0);
v_nargs_1277_ = l_Lean_Expr_getAppNumArgs(v___y_1269_);
lean_inc(v_nargs_1277_);
v___x_1278_ = lean_mk_array(v_nargs_1277_, v_dummy_1276_);
v___x_1279_ = lean_unsigned_to_nat(1u);
v___x_1280_ = lean_nat_sub(v_nargs_1277_, v___x_1279_);
lean_dec(v_nargs_1277_);
v___x_1281_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_1255_, v_pre_1250_, v_post_1252_, v_usedLetOnly_1253_, v_skipConstInApp_1254_, v___y_1269_, v___x_1278_, v___x_1280_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
return v___x_1281_;
}
case 10:
{
lean_object* v_data_1282_; lean_object* v_expr_1283_; lean_object* v___x_1284_; 
v_data_1282_ = lean_ctor_get(v___y_1269_, 0);
v_expr_1283_ = lean_ctor_get(v___y_1269_, 1);
lean_inc_ref(v_expr_1283_);
lean_inc_ref(v_post_1252_);
lean_inc_ref(v_pre_1250_);
v___x_1284_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1250_, v_post_1252_, v_usedLetOnly_1253_, v_skipConstInApp_1254_, v_skipInstances_1255_, v_expr_1283_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; size_t v___x_1286_; size_t v___x_1287_; uint8_t v___x_1288_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1286_ = lean_ptr_addr(v_expr_1283_);
v___x_1287_ = lean_ptr_addr(v_a_1285_);
v___x_1288_ = lean_usize_dec_eq(v___x_1286_, v___x_1287_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
lean_inc(v_data_1282_);
lean_dec_ref_known(v___y_1269_, 2);
v___x_1289_ = l_Lean_Expr_mdata___override(v_data_1282_, v_a_1285_);
v___x_1290_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1250_, v_post_1252_, v_usedLetOnly_1253_, v_skipConstInApp_1254_, v_skipInstances_1255_, v___x_1289_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
return v___x_1290_;
}
else
{
lean_object* v___x_1291_; 
lean_dec(v_a_1285_);
v___x_1291_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1250_, v_post_1252_, v_usedLetOnly_1253_, v_skipConstInApp_1254_, v_skipInstances_1255_, v___y_1269_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
return v___x_1291_;
}
}
else
{
lean_dec_ref_known(v___y_1269_, 2);
lean_dec_ref(v_post_1252_);
lean_dec_ref(v_pre_1250_);
return v___x_1284_;
}
}
case 11:
{
lean_object* v_typeName_1292_; lean_object* v_idx_1293_; lean_object* v_struct_1294_; lean_object* v___x_1295_; 
v_typeName_1292_ = lean_ctor_get(v___y_1269_, 0);
v_idx_1293_ = lean_ctor_get(v___y_1269_, 1);
v_struct_1294_ = lean_ctor_get(v___y_1269_, 2);
lean_inc_ref(v_struct_1294_);
lean_inc_ref(v_post_1252_);
lean_inc_ref(v_pre_1250_);
v___x_1295_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1250_, v_post_1252_, v_usedLetOnly_1253_, v_skipConstInApp_1254_, v_skipInstances_1255_, v_struct_1294_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; size_t v___x_1297_; size_t v___x_1298_; uint8_t v___x_1299_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1296_);
lean_dec_ref_known(v___x_1295_, 1);
v___x_1297_ = lean_ptr_addr(v_struct_1294_);
v___x_1298_ = lean_ptr_addr(v_a_1296_);
v___x_1299_ = lean_usize_dec_eq(v___x_1297_, v___x_1298_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_inc(v_idx_1293_);
lean_inc(v_typeName_1292_);
lean_dec_ref_known(v___y_1269_, 3);
v___x_1300_ = l_Lean_Expr_proj___override(v_typeName_1292_, v_idx_1293_, v_a_1296_);
v___x_1301_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1250_, v_post_1252_, v_usedLetOnly_1253_, v_skipConstInApp_1254_, v_skipInstances_1255_, v___x_1300_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
return v___x_1301_;
}
else
{
lean_object* v___x_1302_; 
lean_dec(v_a_1296_);
v___x_1302_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1250_, v_post_1252_, v_usedLetOnly_1253_, v_skipConstInApp_1254_, v_skipInstances_1255_, v___y_1269_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
return v___x_1302_;
}
}
else
{
lean_dec_ref_known(v___y_1269_, 3);
lean_dec_ref(v_post_1252_);
lean_dec_ref(v_pre_1250_);
return v___x_1295_;
}
}
default: 
{
lean_object* v___x_1303_; 
v___x_1303_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1250_, v_post_1252_, v_usedLetOnly_1253_, v_skipConstInApp_1254_, v_skipInstances_1255_, v___y_1269_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
return v___x_1303_;
}
}
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec_ref(v_post_1252_);
lean_dec_ref(v_e_1251_);
lean_dec_ref(v_pre_1250_);
v_a_1313_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1263_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1263_);
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
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec_ref(v_post_1252_);
lean_dec_ref(v_e_1251_);
lean_dec_ref(v_pre_1250_);
v_a_1321_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1262_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1262_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed(lean_object* v___x_1329_, lean_object* v_pre_1330_, lean_object* v_e_1331_, lean_object* v_post_1332_, lean_object* v_usedLetOnly_1333_, lean_object* v_skipConstInApp_1334_, lean_object* v_skipInstances_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
uint8_t v_usedLetOnly_boxed_1342_; uint8_t v_skipConstInApp_boxed_1343_; uint8_t v_skipInstances_boxed_1344_; lean_object* v_res_1345_; 
v_usedLetOnly_boxed_1342_ = lean_unbox(v_usedLetOnly_1333_);
v_skipConstInApp_boxed_1343_ = lean_unbox(v_skipConstInApp_1334_);
v_skipInstances_boxed_1344_ = lean_unbox(v_skipInstances_1335_);
v_res_1345_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(v___x_1329_, v_pre_1330_, v_e_1331_, v_post_1332_, v_usedLetOnly_boxed_1342_, v_skipConstInApp_boxed_1343_, v_skipInstances_boxed_1344_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(lean_object* v_pre_1346_, lean_object* v_post_1347_, uint8_t v_usedLetOnly_1348_, uint8_t v_skipConstInApp_1349_, uint8_t v_skipInstances_1350_, lean_object* v_e_1351_, lean_object* v_a_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_inc(v_a_1352_);
v___x_1358_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1358_, 0, lean_box(0));
lean_closure_set(v___x_1358_, 1, lean_box(0));
lean_closure_set(v___x_1358_, 2, v_a_1352_);
v___x_1359_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___x_1358_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1394_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1394_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1394_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_a_1360_, v_e_1351_);
lean_dec(v_a_1360_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___f_1369_; lean_object* v___x_1370_; 
lean_del_object(v___x_1362_);
v___x_1365_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0));
v___x_1366_ = lean_box(v_usedLetOnly_1348_);
v___x_1367_ = lean_box(v_skipConstInApp_1349_);
v___x_1368_ = lean_box(v_skipInstances_1350_);
lean_inc_ref(v_e_1351_);
v___f_1369_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed), 13, 7);
lean_closure_set(v___f_1369_, 0, v___x_1365_);
lean_closure_set(v___f_1369_, 1, v_pre_1346_);
lean_closure_set(v___f_1369_, 2, v_e_1351_);
lean_closure_set(v___f_1369_, 3, v_post_1347_);
lean_closure_set(v___f_1369_, 4, v___x_1366_);
lean_closure_set(v___f_1369_, 5, v___x_1367_);
lean_closure_set(v___f_1369_, 6, v___x_1368_);
v___x_1370_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v___f_1369_, v_a_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___f_1372_; lean_object* v___x_1373_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc_n(v_a_1371_, 2);
lean_dec_ref_known(v___x_1370_, 1);
lean_inc(v_a_1352_);
v___f_1372_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1372_, 0, v_a_1352_);
lean_closure_set(v___f_1372_, 1, v_e_1351_);
lean_closure_set(v___f_1372_, 2, v_a_1371_);
v___x_1373_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___f_1372_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1380_ == 0)
{
lean_object* v_unused_1381_; 
v_unused_1381_ = lean_ctor_get(v___x_1373_, 0);
lean_dec(v_unused_1381_);
v___x_1375_ = v___x_1373_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_dec(v___x_1373_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v_a_1371_);
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1371_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec(v_a_1371_);
v_a_1382_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1373_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1373_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
else
{
lean_dec_ref(v_e_1351_);
return v___x_1370_;
}
}
else
{
lean_object* v_val_1390_; lean_object* v___x_1392_; 
lean_dec_ref(v_e_1351_);
lean_dec_ref(v_post_1347_);
lean_dec_ref(v_pre_1346_);
v_val_1390_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_val_1390_);
lean_dec_ref_known(v___x_1364_, 1);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v_val_1390_);
v___x_1392_ = v___x_1362_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_val_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_dec_ref(v_e_1351_);
lean_dec_ref(v_post_1347_);
lean_dec_ref(v_pre_1346_);
v_a_1395_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1359_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1359_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(lean_object* v_pre_1403_, lean_object* v_post_1404_, uint8_t v_usedLetOnly_1405_, uint8_t v_skipConstInApp_1406_, uint8_t v_skipInstances_1407_, lean_object* v_fvars_1408_, lean_object* v_e_1409_, lean_object* v_a_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
if (lean_obj_tag(v_e_1409_) == 7)
{
lean_object* v_binderName_1416_; lean_object* v_binderType_1417_; lean_object* v_body_1418_; uint8_t v_binderInfo_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___f_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v_binderName_1416_ = lean_ctor_get(v_e_1409_, 0);
lean_inc(v_binderName_1416_);
v_binderType_1417_ = lean_ctor_get(v_e_1409_, 1);
lean_inc_ref(v_binderType_1417_);
v_body_1418_ = lean_ctor_get(v_e_1409_, 2);
lean_inc_ref(v_body_1418_);
v_binderInfo_1419_ = lean_ctor_get_uint8(v_e_1409_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1409_, 3);
v___x_1420_ = lean_box(v_usedLetOnly_1405_);
v___x_1421_ = lean_box(v_skipConstInApp_1406_);
v___x_1422_ = lean_box(v_skipInstances_1407_);
lean_inc_ref(v_post_1404_);
lean_inc_ref(v_pre_1403_);
lean_inc_ref(v_fvars_1408_);
v___f_1423_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1423_, 0, v_fvars_1408_);
lean_closure_set(v___f_1423_, 1, v_pre_1403_);
lean_closure_set(v___f_1423_, 2, v_post_1404_);
lean_closure_set(v___f_1423_, 3, v___x_1420_);
lean_closure_set(v___f_1423_, 4, v___x_1421_);
lean_closure_set(v___f_1423_, 5, v___x_1422_);
lean_closure_set(v___f_1423_, 6, v_body_1418_);
v___x_1424_ = lean_expr_instantiate_rev(v_binderType_1417_, v_fvars_1408_);
lean_dec_ref(v_fvars_1408_);
lean_dec_ref(v_binderType_1417_);
v___x_1425_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1403_, v_post_1404_, v_usedLetOnly_1405_, v_skipConstInApp_1406_, v_skipInstances_1407_, v___x_1424_, v_a_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; uint8_t v___x_1427_; lean_object* v___x_1428_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref_known(v___x_1425_, 1);
v___x_1427_ = 0;
v___x_1428_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_1416_, v_binderInfo_1419_, v_a_1426_, v___f_1423_, v___x_1427_, v_a_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
return v___x_1428_;
}
else
{
lean_dec_ref(v___f_1423_);
lean_dec(v_binderName_1416_);
return v___x_1425_;
}
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = lean_expr_instantiate_rev(v_e_1409_, v_fvars_1408_);
lean_dec_ref(v_e_1409_);
lean_inc_ref(v_post_1404_);
lean_inc_ref(v_pre_1403_);
v___x_1430_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1403_, v_post_1404_, v_usedLetOnly_1405_, v_skipConstInApp_1406_, v_skipInstances_1407_, v___x_1429_, v_a_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; uint8_t v___x_1432_; uint8_t v___x_1433_; uint8_t v___x_1434_; lean_object* v___x_1435_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1432_ = 0;
v___x_1433_ = 1;
v___x_1434_ = 1;
v___x_1435_ = l_Lean_Meta_mkForallFVars(v_fvars_1408_, v_a_1431_, v___x_1432_, v_usedLetOnly_1405_, v___x_1433_, v___x_1434_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec_ref(v_fvars_1408_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1437_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v___x_1437_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1403_, v_post_1404_, v_usedLetOnly_1405_, v_skipConstInApp_1406_, v_skipInstances_1407_, v_a_1436_, v_a_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
return v___x_1437_;
}
else
{
lean_dec_ref(v_post_1404_);
lean_dec_ref(v_pre_1403_);
return v___x_1435_;
}
}
else
{
lean_dec_ref(v_fvars_1408_);
lean_dec_ref(v_post_1404_);
lean_dec_ref(v_pre_1403_);
return v___x_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(lean_object* v_fvars_1438_, lean_object* v_pre_1439_, lean_object* v_post_1440_, uint8_t v_usedLetOnly_1441_, uint8_t v_skipConstInApp_1442_, uint8_t v_skipInstances_1443_, lean_object* v_body_1444_, lean_object* v_x_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_array_push(v_fvars_1438_, v_x_1445_);
v___x_1453_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1439_, v_post_1440_, v_usedLetOnly_1441_, v_skipConstInApp_1442_, v_skipInstances_1443_, v___x_1452_, v_body_1444_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7___boxed(lean_object* v_pre_1454_, lean_object* v_post_1455_, lean_object* v_usedLetOnly_1456_, lean_object* v_skipConstInApp_1457_, lean_object* v_skipInstances_1458_, lean_object* v_e_1459_, lean_object* v_a_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
uint8_t v_usedLetOnly_boxed_1466_; uint8_t v_skipConstInApp_boxed_1467_; uint8_t v_skipInstances_boxed_1468_; lean_object* v_res_1469_; 
v_usedLetOnly_boxed_1466_ = lean_unbox(v_usedLetOnly_1456_);
v_skipConstInApp_boxed_1467_ = lean_unbox(v_skipConstInApp_1457_);
v_skipInstances_boxed_1468_ = lean_unbox(v_skipInstances_1458_);
v_res_1469_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1454_, v_post_1455_, v_usedLetOnly_boxed_1466_, v_skipConstInApp_boxed_1467_, v_skipInstances_boxed_1468_, v_e_1459_, v_a_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v_a_1460_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___boxed(lean_object* v_pre_1470_, lean_object* v_post_1471_, lean_object* v_usedLetOnly_1472_, lean_object* v_skipConstInApp_1473_, lean_object* v_skipInstances_1474_, lean_object* v_sz_1475_, lean_object* v_i_1476_, lean_object* v_bs_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
uint8_t v_usedLetOnly_boxed_1484_; uint8_t v_skipConstInApp_boxed_1485_; uint8_t v_skipInstances_boxed_1486_; size_t v_sz_boxed_1487_; size_t v_i_boxed_1488_; lean_object* v_res_1489_; 
v_usedLetOnly_boxed_1484_ = lean_unbox(v_usedLetOnly_1472_);
v_skipConstInApp_boxed_1485_ = lean_unbox(v_skipConstInApp_1473_);
v_skipInstances_boxed_1486_ = lean_unbox(v_skipInstances_1474_);
v_sz_boxed_1487_ = lean_unbox_usize(v_sz_1475_);
lean_dec(v_sz_1475_);
v_i_boxed_1488_ = lean_unbox_usize(v_i_1476_);
lean_dec(v_i_1476_);
v_res_1489_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_1470_, v_post_1471_, v_usedLetOnly_boxed_1484_, v_skipConstInApp_boxed_1485_, v_skipInstances_boxed_1486_, v_sz_boxed_1487_, v_i_boxed_1488_, v_bs_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___boxed(lean_object* v_pre_1490_, lean_object* v_post_1491_, lean_object* v_usedLetOnly_1492_, lean_object* v_skipConstInApp_1493_, lean_object* v_skipInstances_1494_, lean_object* v_e_1495_, lean_object* v_a_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
uint8_t v_usedLetOnly_boxed_1502_; uint8_t v_skipConstInApp_boxed_1503_; uint8_t v_skipInstances_boxed_1504_; lean_object* v_res_1505_; 
v_usedLetOnly_boxed_1502_ = lean_unbox(v_usedLetOnly_1492_);
v_skipConstInApp_boxed_1503_ = lean_unbox(v_skipConstInApp_1493_);
v_skipInstances_boxed_1504_ = lean_unbox(v_skipInstances_1494_);
v_res_1505_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1490_, v_post_1491_, v_usedLetOnly_boxed_1502_, v_skipConstInApp_boxed_1503_, v_skipInstances_boxed_1504_, v_e_1495_, v_a_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v_a_1496_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___boxed(lean_object* v_pre_1506_, lean_object* v_post_1507_, lean_object* v_usedLetOnly_1508_, lean_object* v_skipConstInApp_1509_, lean_object* v_skipInstances_1510_, lean_object* v_fvars_1511_, lean_object* v_e_1512_, lean_object* v_a_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
uint8_t v_usedLetOnly_boxed_1519_; uint8_t v_skipConstInApp_boxed_1520_; uint8_t v_skipInstances_boxed_1521_; lean_object* v_res_1522_; 
v_usedLetOnly_boxed_1519_ = lean_unbox(v_usedLetOnly_1508_);
v_skipConstInApp_boxed_1520_ = lean_unbox(v_skipConstInApp_1509_);
v_skipInstances_boxed_1521_ = lean_unbox(v_skipInstances_1510_);
v_res_1522_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1506_, v_post_1507_, v_usedLetOnly_boxed_1519_, v_skipConstInApp_boxed_1520_, v_skipInstances_boxed_1521_, v_fvars_1511_, v_e_1512_, v_a_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v_a_1513_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___boxed(lean_object* v_pre_1523_, lean_object* v_post_1524_, lean_object* v_usedLetOnly_1525_, lean_object* v_skipConstInApp_1526_, lean_object* v_skipInstances_1527_, lean_object* v_fvars_1528_, lean_object* v_e_1529_, lean_object* v_a_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
uint8_t v_usedLetOnly_boxed_1536_; uint8_t v_skipConstInApp_boxed_1537_; uint8_t v_skipInstances_boxed_1538_; lean_object* v_res_1539_; 
v_usedLetOnly_boxed_1536_ = lean_unbox(v_usedLetOnly_1525_);
v_skipConstInApp_boxed_1537_ = lean_unbox(v_skipConstInApp_1526_);
v_skipInstances_boxed_1538_ = lean_unbox(v_skipInstances_1527_);
v_res_1539_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1523_, v_post_1524_, v_usedLetOnly_boxed_1536_, v_skipConstInApp_boxed_1537_, v_skipInstances_boxed_1538_, v_fvars_1528_, v_e_1529_, v_a_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v_a_1530_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___boxed(lean_object* v_pre_1540_, lean_object* v_post_1541_, lean_object* v_usedLetOnly_1542_, lean_object* v_skipConstInApp_1543_, lean_object* v_skipInstances_1544_, lean_object* v_fvars_1545_, lean_object* v_e_1546_, lean_object* v_a_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
uint8_t v_usedLetOnly_boxed_1553_; uint8_t v_skipConstInApp_boxed_1554_; uint8_t v_skipInstances_boxed_1555_; lean_object* v_res_1556_; 
v_usedLetOnly_boxed_1553_ = lean_unbox(v_usedLetOnly_1542_);
v_skipConstInApp_boxed_1554_ = lean_unbox(v_skipConstInApp_1543_);
v_skipInstances_boxed_1555_ = lean_unbox(v_skipInstances_1544_);
v_res_1556_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1540_, v_post_1541_, v_usedLetOnly_boxed_1553_, v_skipConstInApp_boxed_1554_, v_skipInstances_boxed_1555_, v_fvars_1545_, v_e_1546_, v_a_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v_a_1547_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___boxed(lean_object* v_upperBound_1557_, lean_object* v___x_1558_, lean_object* v_pre_1559_, lean_object* v_post_1560_, lean_object* v_usedLetOnly_1561_, lean_object* v_skipConstInApp_1562_, lean_object* v_skipInstances_1563_, lean_object* v_a_1564_, lean_object* v_b_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
uint8_t v_usedLetOnly_boxed_1572_; uint8_t v_skipConstInApp_boxed_1573_; uint8_t v_skipInstances_boxed_1574_; lean_object* v_res_1575_; 
v_usedLetOnly_boxed_1572_ = lean_unbox(v_usedLetOnly_1561_);
v_skipConstInApp_boxed_1573_ = lean_unbox(v_skipConstInApp_1562_);
v_skipInstances_boxed_1574_ = lean_unbox(v_skipInstances_1563_);
v_res_1575_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_1557_, v___x_1558_, v_pre_1559_, v_post_1560_, v_usedLetOnly_boxed_1572_, v_skipConstInApp_boxed_1573_, v_skipInstances_boxed_1574_, v_a_1564_, v_b_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___x_1558_);
lean_dec(v_upperBound_1557_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13___boxed(lean_object* v_skipInstances_1576_, lean_object* v_pre_1577_, lean_object* v_post_1578_, lean_object* v_usedLetOnly_1579_, lean_object* v_skipConstInApp_1580_, lean_object* v_x_1581_, lean_object* v_x_1582_, lean_object* v_x_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
uint8_t v_skipInstances_boxed_1590_; uint8_t v_usedLetOnly_boxed_1591_; uint8_t v_skipConstInApp_boxed_1592_; lean_object* v_res_1593_; 
v_skipInstances_boxed_1590_ = lean_unbox(v_skipInstances_1576_);
v_usedLetOnly_boxed_1591_ = lean_unbox(v_usedLetOnly_1579_);
v_skipConstInApp_boxed_1592_ = lean_unbox(v_skipConstInApp_1580_);
v_res_1593_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_boxed_1590_, v_pre_1577_, v_post_1578_, v_usedLetOnly_boxed_1591_, v_skipConstInApp_boxed_1592_, v_x_1581_, v_x_1582_, v_x_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
return v_res_1593_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1594_ = lean_box(0);
v___x_1595_ = lean_unsigned_to_nat(16u);
v___x_1596_ = lean_mk_array(v___x_1595_, v___x_1594_);
return v___x_1596_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0);
v___x_1598_ = lean_unsigned_to_nat(0u);
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
lean_ctor_set(v___x_1599_, 1, v___x_1597_);
return v___x_1599_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1);
v___x_1601_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1601_, 0, lean_box(0));
lean_closure_set(v___x_1601_, 1, lean_box(0));
lean_closure_set(v___x_1601_, 2, v___x_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(lean_object* v_input_1602_, lean_object* v_pre_1603_, lean_object* v_post_1604_, uint8_t v_usedLetOnly_1605_, uint8_t v_skipConstInApp_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
uint8_t v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v_a_1615_; lean_object* v___x_1616_; 
v___x_1612_ = 0;
v___x_1613_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2);
v___x_1614_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1613_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref(v___x_1614_);
v___x_1616_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1603_, v_post_1604_, v_usedLetOnly_1605_, v_skipConstInApp_1606_, v___x_1612_, v_input_1602_, v_a_1615_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1616_, 1);
v___x_1618_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1618_, 0, lean_box(0));
lean_closure_set(v___x_1618_, 1, lean_box(0));
lean_closure_set(v___x_1618_, 2, v_a_1615_);
v___x_1619_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1618_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1626_ == 0)
{
lean_object* v_unused_1627_; 
v_unused_1627_ = lean_ctor_get(v___x_1619_, 0);
lean_dec(v_unused_1627_);
v___x_1621_ = v___x_1619_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_dec(v___x_1619_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v_a_1617_);
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1617_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
else
{
lean_dec(v_a_1615_);
return v___x_1616_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___boxed(lean_object* v_input_1628_, lean_object* v_pre_1629_, lean_object* v_post_1630_, lean_object* v_usedLetOnly_1631_, lean_object* v_skipConstInApp_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
uint8_t v_usedLetOnly_boxed_1638_; uint8_t v_skipConstInApp_boxed_1639_; lean_object* v_res_1640_; 
v_usedLetOnly_boxed_1638_ = lean_unbox(v_usedLetOnly_1631_);
v_skipConstInApp_boxed_1639_ = lean_unbox(v_skipConstInApp_1632_);
v_res_1640_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_input_1628_, v_pre_1629_, v_post_1630_, v_usedLetOnly_boxed_1638_, v_skipConstInApp_boxed_1639_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
return v_res_1640_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__1(void){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Array_instInhabited___redArg();
return v___x_1642_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__3(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__2));
v___x_1645_ = l_Lean_stringToMessageData(v___x_1644_);
return v___x_1645_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__5(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__4));
v___x_1648_ = l_Lean_stringToMessageData(v___x_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls(lean_object* v_fixedParamPerms_1649_, lean_object* v_argsPacker_1650_, lean_object* v_funNames_1651_, lean_object* v_newF_1652_, lean_object* v_e_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v___f_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___f_1659_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__0));
v___x_1660_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
lean_inc(v_a_1657_);
lean_inc_ref(v_a_1656_);
lean_inc(v_a_1655_);
lean_inc_ref(v_a_1654_);
lean_inc_ref(v_newF_1652_);
v___x_1661_ = lean_infer_type(v_newF_1652_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; uint8_t v___x_1673_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 1);
v___x_1673_ = l_Lean_Expr_isForall(v_a_1662_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec_ref(v_e_1653_);
lean_dec_ref(v_funNames_1651_);
lean_dec_ref(v_argsPacker_1650_);
lean_dec_ref(v_fixedParamPerms_1649_);
v___x_1674_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__3, &l_Lean_Elab_WF_packCalls___closed__3_once, _init_l_Lean_Elab_WF_packCalls___closed__3);
v___x_1675_ = l_Lean_MessageData_ofExpr(v_newF_1652_);
v___x_1676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__5, &l_Lean_Elab_WF_packCalls___closed__5_once, _init_l_Lean_Elab_WF_packCalls___closed__5);
v___x_1678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1676_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
v___x_1679_ = l_Lean_MessageData_ofExpr(v_a_1662_);
v___x_1680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1678_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v___x_1680_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1681_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1681_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
else
{
v___y_1664_ = v_a_1654_;
v___y_1665_ = v_a_1655_;
v___y_1666_ = v_a_1656_;
v___y_1667_ = v_a_1657_;
goto v___jp_1663_;
}
v___jp_1663_:
{
lean_object* v___x_1668_; lean_object* v___f_1669_; uint8_t v___x_1670_; uint8_t v___x_1671_; lean_object* v___x_1672_; 
v___x_1668_ = l_Lean_Expr_bindingDomain_x21(v_a_1662_);
lean_dec(v_a_1662_);
v___f_1669_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packCalls___lam__2___boxed), 12, 6);
lean_closure_set(v___f_1669_, 0, v_funNames_1651_);
lean_closure_set(v___f_1669_, 1, v_fixedParamPerms_1649_);
lean_closure_set(v___f_1669_, 2, v___x_1660_);
lean_closure_set(v___f_1669_, 3, v_argsPacker_1650_);
lean_closure_set(v___f_1669_, 4, v___x_1668_);
lean_closure_set(v___f_1669_, 5, v_newF_1652_);
v___x_1670_ = 0;
v___x_1671_ = 1;
v___x_1672_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_e_1653_, v___f_1659_, v___f_1669_, v___x_1670_, v___x_1671_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
return v___x_1672_;
}
}
else
{
lean_dec_ref(v_e_1653_);
lean_dec_ref(v_newF_1652_);
lean_dec_ref(v_funNames_1651_);
lean_dec_ref(v_argsPacker_1650_);
lean_dec_ref(v_fixedParamPerms_1649_);
return v___x_1661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___boxed(lean_object* v_fixedParamPerms_1690_, lean_object* v_argsPacker_1691_, lean_object* v_funNames_1692_, lean_object* v_newF_1693_, lean_object* v_e_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_1690_, v_argsPacker_1691_, v_funNames_1692_, v_newF_1693_, v_e_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(lean_object* v_upperBound_1701_, lean_object* v___x_1702_, lean_object* v_pre_1703_, lean_object* v_post_1704_, uint8_t v_usedLetOnly_1705_, uint8_t v_skipConstInApp_1706_, uint8_t v_skipInstances_1707_, lean_object* v___x_1708_, lean_object* v_inst_1709_, lean_object* v_R_1710_, lean_object* v_a_1711_, lean_object* v_b_1712_, lean_object* v_c_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_1701_, v___x_1702_, v_pre_1703_, v_post_1704_, v_usedLetOnly_1705_, v_skipConstInApp_1706_, v_skipInstances_1707_, v_a_1711_, v_b_1712_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1721_ = _args[0];
lean_object* v___x_1722_ = _args[1];
lean_object* v_pre_1723_ = _args[2];
lean_object* v_post_1724_ = _args[3];
lean_object* v_usedLetOnly_1725_ = _args[4];
lean_object* v_skipConstInApp_1726_ = _args[5];
lean_object* v_skipInstances_1727_ = _args[6];
lean_object* v___x_1728_ = _args[7];
lean_object* v_inst_1729_ = _args[8];
lean_object* v_R_1730_ = _args[9];
lean_object* v_a_1731_ = _args[10];
lean_object* v_b_1732_ = _args[11];
lean_object* v_c_1733_ = _args[12];
lean_object* v___y_1734_ = _args[13];
lean_object* v___y_1735_ = _args[14];
lean_object* v___y_1736_ = _args[15];
lean_object* v___y_1737_ = _args[16];
lean_object* v___y_1738_ = _args[17];
lean_object* v___y_1739_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_1740_; uint8_t v_skipConstInApp_boxed_1741_; uint8_t v_skipInstances_boxed_1742_; lean_object* v_res_1743_; 
v_usedLetOnly_boxed_1740_ = lean_unbox(v_usedLetOnly_1725_);
v_skipConstInApp_boxed_1741_ = lean_unbox(v_skipConstInApp_1726_);
v_skipInstances_boxed_1742_ = lean_unbox(v_skipInstances_1727_);
v_res_1743_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_upperBound_1721_, v___x_1722_, v_pre_1723_, v_post_1724_, v_usedLetOnly_boxed_1740_, v_skipConstInApp_boxed_1741_, v_skipInstances_boxed_1742_, v___x_1728_, v_inst_1729_, v_R_1730_, v_a_1731_, v_b_1732_, v_c_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec(v___x_1728_);
lean_dec_ref(v___x_1722_);
lean_dec(v_upperBound_1721_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1744_, lean_object* v_m_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_m_1745_, v_a_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___boxed(lean_object* v_00_u03b2_1748_, lean_object* v_m_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(v_00_u03b2_1748_, v_m_1749_, v_a_1750_);
lean_dec_ref(v_a_1750_);
lean_dec_ref(v_m_1749_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_1752_, lean_object* v_name_1753_, uint8_t v_bi_1754_, lean_object* v_type_1755_, lean_object* v_k_1756_, uint8_t v_kind_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_1753_, v_bi_1754_, v_type_1755_, v_k_1756_, v_kind_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_1765_, lean_object* v_name_1766_, lean_object* v_bi_1767_, lean_object* v_type_1768_, lean_object* v_k_1769_, lean_object* v_kind_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
uint8_t v_bi_boxed_1777_; uint8_t v_kind_boxed_1778_; lean_object* v_res_1779_; 
v_bi_boxed_1777_ = lean_unbox(v_bi_1767_);
v_kind_boxed_1778_ = lean_unbox(v_kind_1770_);
v_res_1779_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(v_00_u03b1_1765_, v_name_1766_, v_bi_boxed_1777_, v_type_1768_, v_k_1769_, v_kind_boxed_1778_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(lean_object* v_00_u03b1_1780_, lean_object* v_name_1781_, lean_object* v_type_1782_, lean_object* v_val_1783_, lean_object* v_k_1784_, uint8_t v_nondep_1785_, uint8_t v_kind_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_1781_, v_type_1782_, v_val_1783_, v_k_1784_, v_nondep_1785_, v_kind_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___boxed(lean_object* v_00_u03b1_1794_, lean_object* v_name_1795_, lean_object* v_type_1796_, lean_object* v_val_1797_, lean_object* v_k_1798_, lean_object* v_nondep_1799_, lean_object* v_kind_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
uint8_t v_nondep_boxed_1807_; uint8_t v_kind_boxed_1808_; lean_object* v_res_1809_; 
v_nondep_boxed_1807_ = lean_unbox(v_nondep_1799_);
v_kind_boxed_1808_ = lean_unbox(v_kind_1800_);
v_res_1809_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(v_00_u03b1_1794_, v_name_1795_, v_type_1796_, v_val_1797_, v_k_1798_, v_nondep_boxed_1807_, v_kind_boxed_1808_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(lean_object* v_00_u03b1_1810_, lean_object* v_ref_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_1811_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___boxed(lean_object* v_00_u03b1_1818_, lean_object* v_ref_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(v_00_u03b1_1818_, v_ref_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(lean_object* v_00_u03b1_1826_, lean_object* v_x_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___boxed(lean_object* v_00_u03b1_1835_, lean_object* v_x_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(v_00_u03b1_1835_, v_x_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15(lean_object* v_00_u03b2_1844_, lean_object* v_m_1845_, lean_object* v_a_1846_, lean_object* v_b_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v_m_1845_, v_a_1846_, v_b_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(lean_object* v_00_u03b2_1849_, lean_object* v_a_1850_, lean_object* v_x_1851_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_1850_, v_x_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___boxed(lean_object* v_00_u03b2_1853_, lean_object* v_a_1854_, lean_object* v_x_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(v_00_u03b2_1853_, v_a_1854_, v_x_1855_);
lean_dec(v_x_1855_);
lean_dec_ref(v_a_1854_);
return v_res_1856_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(lean_object* v_00_u03b2_1857_, lean_object* v_a_1858_, lean_object* v_x_1859_){
_start:
{
uint8_t v___x_1860_; 
v___x_1860_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_1858_, v_x_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___boxed(lean_object* v_00_u03b2_1861_, lean_object* v_a_1862_, lean_object* v_x_1863_){
_start:
{
uint8_t v_res_1864_; lean_object* v_r_1865_; 
v_res_1864_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(v_00_u03b2_1861_, v_a_1862_, v_x_1863_);
lean_dec(v_x_1863_);
lean_dec_ref(v_a_1862_);
v_r_1865_ = lean_box(v_res_1864_);
return v_r_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21(lean_object* v_00_u03b2_1866_, lean_object* v_data_1867_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_data_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22(lean_object* v_00_u03b2_1869_, lean_object* v_a_1870_, lean_object* v_b_1871_, lean_object* v_x_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_1870_, v_b_1871_, v_x_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22(lean_object* v_00_u03b2_1874_, lean_object* v_i_1875_, lean_object* v_source_1876_, lean_object* v_target_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v_i_1875_, v_source_1876_, v_target_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23(lean_object* v_00_u03b2_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(v_x_1880_, v_x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName(lean_object* v_fixedParamPerms_1889_, lean_object* v_argsPacker_1890_, lean_object* v_preDefs_1891_){
_start:
{
lean_object* v___x_1892_; uint8_t v___x_1907_; 
v___x_1892_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1907_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_1889_);
if (v___x_1907_ == 0)
{
goto v___jp_1893_;
}
else
{
uint8_t v___x_1908_; 
v___x_1908_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_1890_);
if (v___x_1908_ == 0)
{
goto v___jp_1893_;
}
else
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v_declName_1911_; 
v___x_1909_ = lean_unsigned_to_nat(0u);
v___x_1910_ = lean_array_get_borrowed(v___x_1892_, v_preDefs_1891_, v___x_1909_);
v_declName_1911_ = lean_ctor_get(v___x_1910_, 3);
lean_inc(v_declName_1911_);
return v_declName_1911_;
}
}
v___jp_1893_:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; 
v___x_1894_ = lean_unsigned_to_nat(1u);
v___x_1895_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_1890_);
v___x_1896_ = lean_nat_dec_lt(v___x_1894_, v___x_1895_);
lean_dec(v___x_1895_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v_declName_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1897_ = lean_unsigned_to_nat(0u);
v___x_1898_ = lean_array_get_borrowed(v___x_1892_, v_preDefs_1891_, v___x_1897_);
v_declName_1899_ = lean_ctor_get(v___x_1898_, 3);
v___x_1900_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__1));
lean_inc(v_declName_1899_);
v___x_1901_ = l_Lean_Name_append(v_declName_1899_, v___x_1900_);
return v___x_1901_;
}
else
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v_declName_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1902_ = lean_unsigned_to_nat(0u);
v___x_1903_ = lean_array_get_borrowed(v___x_1892_, v_preDefs_1891_, v___x_1902_);
v_declName_1904_ = lean_ctor_get(v___x_1903_, 3);
v___x_1905_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__3));
lean_inc(v_declName_1904_);
v___x_1906_ = l_Lean_Name_append(v_declName_1904_, v___x_1905_);
return v___x_1906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName___boxed(lean_object* v_fixedParamPerms_1912_, lean_object* v_argsPacker_1913_, lean_object* v_preDefs_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_1912_, v_argsPacker_1913_, v_preDefs_1914_);
lean_dec_ref(v_preDefs_1914_);
lean_dec_ref(v_argsPacker_1913_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(lean_object* v_k_1916_, lean_object* v_b_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___x_1923_; 
lean_inc(v___y_1921_);
lean_inc_ref(v___y_1920_);
lean_inc(v___y_1919_);
lean_inc_ref(v___y_1918_);
v___x_1923_ = lean_apply_6(v_k_1916_, v_b_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, lean_box(0));
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed(lean_object* v_k_1924_, lean_object* v_b_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(v_k_1924_, v_b_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(lean_object* v_perm_1932_, lean_object* v_type_1933_, lean_object* v_k_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___f_1940_; lean_object* v___x_1941_; 
v___f_1940_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1940_, 0, v_k_1934_);
v___x_1941_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_1932_, v_type_1933_, v___f_1940_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1941_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1941_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
v_a_1950_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1941_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1941_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___boxed(lean_object* v_perm_1958_, lean_object* v_type_1959_, lean_object* v_k_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_1958_, v_type_1959_, v_k_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(lean_object* v_00_u03b1_1967_, lean_object* v_perm_1968_, lean_object* v_type_1969_, lean_object* v_k_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_1968_, v_type_1969_, v_k_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___boxed(lean_object* v_00_u03b1_1977_, lean_object* v_perm_1978_, lean_object* v_type_1979_, lean_object* v_k_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(v_00_u03b1_1977_, v_perm_1978_, v_type_1979_, v_k_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(lean_object* v___x_1987_, lean_object* v_ys_1988_, size_t v_sz_1989_, size_t v_i_1990_, lean_object* v_bs_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
uint8_t v___x_1997_; 
v___x_1997_ = lean_usize_dec_lt(v_i_1990_, v_sz_1989_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; 
lean_dec_ref(v_ys_1988_);
v___x_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1998_, 0, v_bs_1991_);
return v___x_1998_;
}
else
{
lean_object* v_v_1999_; lean_object* v_value_2000_; lean_object* v___x_2001_; lean_object* v_bs_x27_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v_v_1999_ = lean_array_uget_borrowed(v_bs_1991_, v_i_1990_);
v_value_2000_ = lean_ctor_get(v_v_1999_, 7);
lean_inc_ref(v_value_2000_);
v___x_2001_ = lean_unsigned_to_nat(0u);
v_bs_x27_2002_ = lean_array_uset(v_bs_1991_, v_i_1990_, v___x_2001_);
v___x_2003_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2004_ = lean_usize_to_nat(v_i_1990_);
v___x_2005_ = lean_array_get_borrowed(v___x_2003_, v___x_1987_, v___x_2004_);
lean_dec(v___x_2004_);
lean_inc_ref(v_ys_1988_);
lean_inc(v___x_2005_);
v___x_2006_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_2005_, v_value_2000_, v_ys_1988_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; size_t v___x_2008_; size_t v___x_2009_; lean_object* v___x_2010_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2006_, 1);
v___x_2008_ = ((size_t)1ULL);
v___x_2009_ = lean_usize_add(v_i_1990_, v___x_2008_);
v___x_2010_ = lean_array_uset(v_bs_x27_2002_, v_i_1990_, v_a_2007_);
v_i_1990_ = v___x_2009_;
v_bs_1991_ = v___x_2010_;
goto _start;
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec_ref(v_bs_x27_2002_);
lean_dec_ref(v_ys_1988_);
v_a_2012_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_2006_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2006_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg___boxed(lean_object* v___x_2020_, lean_object* v_ys_2021_, lean_object* v_sz_2022_, lean_object* v_i_2023_, lean_object* v_bs_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
size_t v_sz_boxed_2030_; size_t v_i_boxed_2031_; lean_object* v_res_2032_; 
v_sz_boxed_2030_ = lean_unbox_usize(v_sz_2022_);
lean_dec(v_sz_2022_);
v_i_boxed_2031_ = lean_unbox_usize(v_i_2023_);
lean_dec(v_i_2023_);
v_res_2032_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2020_, v_ys_2021_, v_sz_boxed_2030_, v_i_boxed_2031_, v_bs_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec_ref(v___x_2020_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(lean_object* v___x_2033_, lean_object* v_ys_2034_, size_t v_sz_2035_, size_t v_i_2036_, lean_object* v_bs_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
uint8_t v___x_2043_; 
v___x_2043_ = lean_usize_dec_lt(v_i_2036_, v_sz_2035_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; 
lean_dec_ref(v_ys_2034_);
v___x_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2044_, 0, v_bs_2037_);
return v___x_2044_;
}
else
{
lean_object* v_v_2045_; lean_object* v_type_2046_; lean_object* v___x_2047_; lean_object* v_bs_x27_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v_v_2045_ = lean_array_uget_borrowed(v_bs_2037_, v_i_2036_);
v_type_2046_ = lean_ctor_get(v_v_2045_, 6);
lean_inc_ref(v_type_2046_);
v___x_2047_ = lean_unsigned_to_nat(0u);
v_bs_x27_2048_ = lean_array_uset(v_bs_2037_, v_i_2036_, v___x_2047_);
v___x_2049_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2050_ = lean_usize_to_nat(v_i_2036_);
v___x_2051_ = lean_array_get_borrowed(v___x_2049_, v___x_2033_, v___x_2050_);
lean_dec(v___x_2050_);
lean_inc_ref(v_ys_2034_);
lean_inc(v___x_2051_);
v___x_2052_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_2051_, v_type_2046_, v_ys_2034_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; size_t v___x_2054_; size_t v___x_2055_; lean_object* v___x_2056_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref_known(v___x_2052_, 1);
v___x_2054_ = ((size_t)1ULL);
v___x_2055_ = lean_usize_add(v_i_2036_, v___x_2054_);
v___x_2056_ = lean_array_uset(v_bs_x27_2048_, v_i_2036_, v_a_2053_);
v_i_2036_ = v___x_2055_;
v_bs_2037_ = v___x_2056_;
goto _start;
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec_ref(v_bs_x27_2048_);
lean_dec_ref(v_ys_2034_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg___boxed(lean_object* v___x_2066_, lean_object* v_ys_2067_, lean_object* v_sz_2068_, lean_object* v_i_2069_, lean_object* v_bs_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
size_t v_sz_boxed_2076_; size_t v_i_boxed_2077_; lean_object* v_res_2078_; 
v_sz_boxed_2076_ = lean_unbox_usize(v_sz_2068_);
lean_dec(v_sz_2068_);
v_i_boxed_2077_ = lean_unbox_usize(v_i_2069_);
lean_dec(v_i_2069_);
v_res_2078_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2066_, v_ys_2067_, v_sz_boxed_2076_, v_i_boxed_2077_, v_bs_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec_ref(v___x_2066_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
if (lean_obj_tag(v_a_2079_) == 0)
{
lean_object* v___x_2081_; 
v___x_2081_ = l_List_reverse___redArg(v_a_2080_);
return v___x_2081_;
}
else
{
lean_object* v_head_2082_; lean_object* v_tail_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2092_; 
v_head_2082_ = lean_ctor_get(v_a_2079_, 0);
v_tail_2083_ = lean_ctor_get(v_a_2079_, 1);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_a_2079_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2085_ = v_a_2079_;
v_isShared_2086_ = v_isSharedCheck_2092_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_tail_2083_);
lean_inc(v_head_2082_);
lean_dec(v_a_2079_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2092_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2087_ = l_Lean_mkLevelParam(v_head_2082_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 1, v_a_2080_);
lean_ctor_set(v___x_2085_, 0, v___x_2087_);
v___x_2089_ = v___x_2085_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2087_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_a_2080_);
v___x_2089_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
v_a_2079_ = v_tail_2083_;
v_a_2080_ = v___x_2089_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(size_t v_sz_2093_, size_t v_i_2094_, lean_object* v_bs_2095_){
_start:
{
uint8_t v___x_2096_; 
v___x_2096_ = lean_usize_dec_lt(v_i_2094_, v_sz_2093_);
if (v___x_2096_ == 0)
{
return v_bs_2095_;
}
else
{
lean_object* v_v_2097_; lean_object* v_declName_2098_; lean_object* v___x_2099_; lean_object* v_bs_x27_2100_; size_t v___x_2101_; size_t v___x_2102_; lean_object* v___x_2103_; 
v_v_2097_ = lean_array_uget_borrowed(v_bs_2095_, v_i_2094_);
v_declName_2098_ = lean_ctor_get(v_v_2097_, 3);
lean_inc(v_declName_2098_);
v___x_2099_ = lean_unsigned_to_nat(0u);
v_bs_x27_2100_ = lean_array_uset(v_bs_2095_, v_i_2094_, v___x_2099_);
v___x_2101_ = ((size_t)1ULL);
v___x_2102_ = lean_usize_add(v_i_2094_, v___x_2101_);
v___x_2103_ = lean_array_uset(v_bs_x27_2100_, v_i_2094_, v_declName_2098_);
v_i_2094_ = v___x_2102_;
v_bs_2095_ = v___x_2103_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3___boxed(lean_object* v_sz_2105_, lean_object* v_i_2106_, lean_object* v_bs_2107_){
_start:
{
size_t v_sz_boxed_2108_; size_t v_i_boxed_2109_; lean_object* v_res_2110_; 
v_sz_boxed_2108_ = lean_unbox_usize(v_sz_2105_);
lean_dec(v_sz_2105_);
v_i_boxed_2109_ = lean_unbox_usize(v_i_2106_);
lean_dec(v_i_2106_);
v_res_2110_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_boxed_2108_, v_i_boxed_2109_, v_bs_2107_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0(lean_object* v_preDefs_2111_, lean_object* v_perms_2112_, lean_object* v_argsPacker_2113_, uint8_t v___x_2114_, lean_object* v_ref_2115_, uint8_t v_kind_2116_, lean_object* v_levelParams_2117_, lean_object* v_modifiers_2118_, lean_object* v_newFn_2119_, lean_object* v_binders_2120_, lean_object* v_numSectionVars_2121_, lean_object* v_value_2122_, lean_object* v_termination_2123_, lean_object* v_fixedParamPerms_2124_, lean_object* v_ys_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
size_t v_sz_2131_; size_t v___x_2132_; lean_object* v___x_2133_; 
v_sz_2131_ = lean_array_size(v_preDefs_2111_);
v___x_2132_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_2111_);
lean_inc_ref(v_ys_2125_);
v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v_perms_2112_, v_ys_2125_, v_sz_2131_, v___x_2132_, v_preDefs_2111_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2135_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2133_, 1);
lean_inc_ref(v_preDefs_2111_);
lean_inc_ref(v_ys_2125_);
v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v_perms_2112_, v_ys_2125_, v_sz_2131_, v___x_2132_, v_preDefs_2111_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2137_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v___x_2137_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_2113_, v_a_2134_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec(v_a_2134_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; uint8_t v___x_2139_; uint8_t v___x_2140_; lean_object* v___x_2141_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v___x_2139_ = 1;
v___x_2140_ = 1;
v___x_2141_ = l_Lean_Meta_mkForallFVars(v_ys_2125_, v_a_2138_, v___x_2114_, v___x_2139_, v___x_2139_, v___x_2140_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc_n(v_a_2142_, 2);
lean_dec_ref_known(v___x_2141_, 1);
lean_inc_ref(v_termination_2123_);
lean_inc(v_numSectionVars_2121_);
lean_inc(v_binders_2120_);
lean_inc(v_newFn_2119_);
lean_inc_ref(v_modifiers_2118_);
lean_inc(v_levelParams_2117_);
lean_inc(v_ref_2115_);
v___x_2143_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2143_, 0, v_ref_2115_);
lean_ctor_set(v___x_2143_, 1, v_levelParams_2117_);
lean_ctor_set(v___x_2143_, 2, v_modifiers_2118_);
lean_ctor_set(v___x_2143_, 3, v_newFn_2119_);
lean_ctor_set(v___x_2143_, 4, v_binders_2120_);
lean_ctor_set(v___x_2143_, 5, v_numSectionVars_2121_);
lean_ctor_set(v___x_2143_, 6, v_a_2142_);
lean_ctor_set(v___x_2143_, 7, v_value_2122_);
lean_ctor_set(v___x_2143_, 8, v_termination_2123_);
lean_ctor_set_uint8(v___x_2143_, sizeof(void*)*9, v_kind_2116_);
v___x_2144_ = l_Lean_Elab_addAsAxiom___redArg(v___x_2143_, v___y_2128_, v___y_2129_);
lean_dec_ref_known(v___x_2143_, 9);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
lean_dec_ref_known(v___x_2144_, 1);
v___x_2145_ = lean_box(0);
lean_inc(v_levelParams_2117_);
v___x_2146_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_2117_, v___x_2145_);
lean_inc(v_newFn_2119_);
v___x_2147_ = l_Lean_mkConst(v_newFn_2119_, v___x_2146_);
v___x_2148_ = l_Lean_mkAppN(v___x_2147_, v_ys_2125_);
v___x_2149_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_2113_, v_a_2136_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec(v_a_2136_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v___x_2151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_2131_, v___x_2132_, v_preDefs_2111_);
v___x_2152_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_2124_, v_argsPacker_2113_, v___x_2151_, v___x_2148_, v_a_2150_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2154_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2153_);
lean_dec_ref_known(v___x_2152_, 1);
v___x_2154_ = l_Lean_Meta_mkLambdaFVars(v_ys_2125_, v_a_2153_, v___x_2114_, v___x_2139_, v___x_2114_, v___x_2139_, v___x_2140_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec_ref(v_ys_2125_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2163_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2157_ = v___x_2154_;
v_isShared_2158_ = v_isSharedCheck_2163_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2154_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2163_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2159_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2159_, 0, v_ref_2115_);
lean_ctor_set(v___x_2159_, 1, v_levelParams_2117_);
lean_ctor_set(v___x_2159_, 2, v_modifiers_2118_);
lean_ctor_set(v___x_2159_, 3, v_newFn_2119_);
lean_ctor_set(v___x_2159_, 4, v_binders_2120_);
lean_ctor_set(v___x_2159_, 5, v_numSectionVars_2121_);
lean_ctor_set(v___x_2159_, 6, v_a_2142_);
lean_ctor_set(v___x_2159_, 7, v_a_2155_);
lean_ctor_set(v___x_2159_, 8, v_termination_2123_);
lean_ctor_set_uint8(v___x_2159_, sizeof(void*)*9, v_kind_2116_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v___x_2159_);
v___x_2161_ = v___x_2157_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec(v_a_2142_);
lean_dec_ref(v_termination_2123_);
lean_dec(v_numSectionVars_2121_);
lean_dec(v_binders_2120_);
lean_dec(v_newFn_2119_);
lean_dec_ref(v_modifiers_2118_);
lean_dec(v_levelParams_2117_);
lean_dec(v_ref_2115_);
v_a_2164_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2154_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2154_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec(v_a_2142_);
lean_dec_ref(v_ys_2125_);
lean_dec_ref(v_termination_2123_);
lean_dec(v_numSectionVars_2121_);
lean_dec(v_binders_2120_);
lean_dec(v_newFn_2119_);
lean_dec_ref(v_modifiers_2118_);
lean_dec(v_levelParams_2117_);
lean_dec(v_ref_2115_);
v_a_2172_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2152_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2152_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec_ref(v___x_2148_);
lean_dec(v_a_2142_);
lean_dec_ref(v_ys_2125_);
lean_dec_ref(v_fixedParamPerms_2124_);
lean_dec_ref(v_termination_2123_);
lean_dec(v_numSectionVars_2121_);
lean_dec(v_binders_2120_);
lean_dec(v_newFn_2119_);
lean_dec_ref(v_modifiers_2118_);
lean_dec(v_levelParams_2117_);
lean_dec(v_ref_2115_);
lean_dec_ref(v_argsPacker_2113_);
lean_dec_ref(v_preDefs_2111_);
v_a_2180_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2149_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2149_);
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
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec(v_a_2142_);
lean_dec(v_a_2136_);
lean_dec_ref(v_ys_2125_);
lean_dec_ref(v_fixedParamPerms_2124_);
lean_dec_ref(v_termination_2123_);
lean_dec(v_numSectionVars_2121_);
lean_dec(v_binders_2120_);
lean_dec(v_newFn_2119_);
lean_dec_ref(v_modifiers_2118_);
lean_dec(v_levelParams_2117_);
lean_dec(v_ref_2115_);
lean_dec_ref(v_argsPacker_2113_);
lean_dec_ref(v_preDefs_2111_);
v_a_2188_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2144_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2144_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
else
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
lean_dec(v_a_2136_);
lean_dec_ref(v_ys_2125_);
lean_dec_ref(v_fixedParamPerms_2124_);
lean_dec_ref(v_termination_2123_);
lean_dec_ref(v_value_2122_);
lean_dec(v_numSectionVars_2121_);
lean_dec(v_binders_2120_);
lean_dec(v_newFn_2119_);
lean_dec_ref(v_modifiers_2118_);
lean_dec(v_levelParams_2117_);
lean_dec(v_ref_2115_);
lean_dec_ref(v_argsPacker_2113_);
lean_dec_ref(v_preDefs_2111_);
v_a_2196_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2141_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2141_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec(v_a_2136_);
lean_dec_ref(v_ys_2125_);
lean_dec_ref(v_fixedParamPerms_2124_);
lean_dec_ref(v_termination_2123_);
lean_dec_ref(v_value_2122_);
lean_dec(v_numSectionVars_2121_);
lean_dec(v_binders_2120_);
lean_dec(v_newFn_2119_);
lean_dec_ref(v_modifiers_2118_);
lean_dec(v_levelParams_2117_);
lean_dec(v_ref_2115_);
lean_dec_ref(v_argsPacker_2113_);
lean_dec_ref(v_preDefs_2111_);
v_a_2204_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2137_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2137_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_dec(v_a_2134_);
lean_dec_ref(v_ys_2125_);
lean_dec_ref(v_fixedParamPerms_2124_);
lean_dec_ref(v_termination_2123_);
lean_dec_ref(v_value_2122_);
lean_dec(v_numSectionVars_2121_);
lean_dec(v_binders_2120_);
lean_dec(v_newFn_2119_);
lean_dec_ref(v_modifiers_2118_);
lean_dec(v_levelParams_2117_);
lean_dec(v_ref_2115_);
lean_dec_ref(v_argsPacker_2113_);
lean_dec_ref(v_preDefs_2111_);
v_a_2212_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2135_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2135_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec_ref(v_ys_2125_);
lean_dec_ref(v_fixedParamPerms_2124_);
lean_dec_ref(v_termination_2123_);
lean_dec_ref(v_value_2122_);
lean_dec(v_numSectionVars_2121_);
lean_dec(v_binders_2120_);
lean_dec(v_newFn_2119_);
lean_dec_ref(v_modifiers_2118_);
lean_dec(v_levelParams_2117_);
lean_dec(v_ref_2115_);
lean_dec_ref(v_argsPacker_2113_);
lean_dec_ref(v_preDefs_2111_);
v_a_2220_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2133_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2133_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0___boxed(lean_object** _args){
lean_object* v_preDefs_2228_ = _args[0];
lean_object* v_perms_2229_ = _args[1];
lean_object* v_argsPacker_2230_ = _args[2];
lean_object* v___x_2231_ = _args[3];
lean_object* v_ref_2232_ = _args[4];
lean_object* v_kind_2233_ = _args[5];
lean_object* v_levelParams_2234_ = _args[6];
lean_object* v_modifiers_2235_ = _args[7];
lean_object* v_newFn_2236_ = _args[8];
lean_object* v_binders_2237_ = _args[9];
lean_object* v_numSectionVars_2238_ = _args[10];
lean_object* v_value_2239_ = _args[11];
lean_object* v_termination_2240_ = _args[12];
lean_object* v_fixedParamPerms_2241_ = _args[13];
lean_object* v_ys_2242_ = _args[14];
lean_object* v___y_2243_ = _args[15];
lean_object* v___y_2244_ = _args[16];
lean_object* v___y_2245_ = _args[17];
lean_object* v___y_2246_ = _args[18];
lean_object* v___y_2247_ = _args[19];
_start:
{
uint8_t v___x_2509__boxed_2248_; uint8_t v_kind_boxed_2249_; lean_object* v_res_2250_; 
v___x_2509__boxed_2248_ = lean_unbox(v___x_2231_);
v_kind_boxed_2249_ = lean_unbox(v_kind_2233_);
v_res_2250_ = l_Lean_Elab_WF_packMutual___lam__0(v_preDefs_2228_, v_perms_2229_, v_argsPacker_2230_, v___x_2509__boxed_2248_, v_ref_2232_, v_kind_boxed_2249_, v_levelParams_2234_, v_modifiers_2235_, v_newFn_2236_, v_binders_2237_, v_numSectionVars_2238_, v_value_2239_, v_termination_2240_, v_fixedParamPerms_2241_, v_ys_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec_ref(v_perms_2229_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual(lean_object* v_fixedParamPerms_2251_, lean_object* v_argsPacker_2252_, lean_object* v_preDefs_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v_ref_2262_; uint8_t v_kind_2263_; lean_object* v_levelParams_2264_; lean_object* v_modifiers_2265_; lean_object* v_declName_2266_; lean_object* v_binders_2267_; lean_object* v_numSectionVars_2268_; lean_object* v_type_2269_; lean_object* v_value_2270_; lean_object* v_termination_2271_; lean_object* v_newFn_2272_; uint8_t v___x_2273_; 
v___x_2259_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_2260_ = lean_unsigned_to_nat(0u);
v___x_2261_ = lean_array_get_borrowed(v___x_2259_, v_preDefs_2253_, v___x_2260_);
v_ref_2262_ = lean_ctor_get(v___x_2261_, 0);
v_kind_2263_ = lean_ctor_get_uint8(v___x_2261_, sizeof(void*)*9);
v_levelParams_2264_ = lean_ctor_get(v___x_2261_, 1);
v_modifiers_2265_ = lean_ctor_get(v___x_2261_, 2);
v_declName_2266_ = lean_ctor_get(v___x_2261_, 3);
v_binders_2267_ = lean_ctor_get(v___x_2261_, 4);
v_numSectionVars_2268_ = lean_ctor_get(v___x_2261_, 5);
v_type_2269_ = lean_ctor_get(v___x_2261_, 6);
v_value_2270_ = lean_ctor_get(v___x_2261_, 7);
v_termination_2271_ = lean_ctor_get(v___x_2261_, 8);
lean_inc_ref(v_fixedParamPerms_2251_);
v_newFn_2272_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_2251_, v_argsPacker_2252_, v_preDefs_2253_);
v___x_2273_ = lean_name_eq(v_newFn_2272_, v_declName_2266_);
if (v___x_2273_ == 0)
{
lean_object* v_perms_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___f_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
lean_inc_ref(v_termination_2271_);
lean_inc_ref(v_value_2270_);
lean_inc_ref(v_type_2269_);
lean_inc(v_numSectionVars_2268_);
lean_inc(v_binders_2267_);
lean_inc_ref(v_modifiers_2265_);
lean_inc(v_levelParams_2264_);
lean_inc(v_ref_2262_);
v_perms_2274_ = lean_ctor_get(v_fixedParamPerms_2251_, 1);
lean_inc_ref_n(v_perms_2274_, 2);
v___x_2275_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2276_ = lean_box(v___x_2273_);
v___x_2277_ = lean_box(v_kind_2263_);
v___f_2278_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packMutual___lam__0___boxed), 20, 14);
lean_closure_set(v___f_2278_, 0, v_preDefs_2253_);
lean_closure_set(v___f_2278_, 1, v_perms_2274_);
lean_closure_set(v___f_2278_, 2, v_argsPacker_2252_);
lean_closure_set(v___f_2278_, 3, v___x_2276_);
lean_closure_set(v___f_2278_, 4, v_ref_2262_);
lean_closure_set(v___f_2278_, 5, v___x_2277_);
lean_closure_set(v___f_2278_, 6, v_levelParams_2264_);
lean_closure_set(v___f_2278_, 7, v_modifiers_2265_);
lean_closure_set(v___f_2278_, 8, v_newFn_2272_);
lean_closure_set(v___f_2278_, 9, v_binders_2267_);
lean_closure_set(v___f_2278_, 10, v_numSectionVars_2268_);
lean_closure_set(v___f_2278_, 11, v_value_2270_);
lean_closure_set(v___f_2278_, 12, v_termination_2271_);
lean_closure_set(v___f_2278_, 13, v_fixedParamPerms_2251_);
v___x_2279_ = lean_array_get(v___x_2275_, v_perms_2274_, v___x_2260_);
lean_dec_ref(v_perms_2274_);
v___x_2280_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v___x_2279_, v_type_2269_, v___f_2278_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_);
return v___x_2280_;
}
else
{
lean_object* v___x_2281_; 
lean_inc(v___x_2261_);
lean_dec(v_newFn_2272_);
lean_dec_ref(v_preDefs_2253_);
lean_dec_ref(v_argsPacker_2252_);
lean_dec_ref(v_fixedParamPerms_2251_);
v___x_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2261_);
return v___x_2281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___boxed(lean_object* v_fixedParamPerms_2282_, lean_object* v_argsPacker_2283_, lean_object* v_preDefs_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_Elab_WF_packMutual(v_fixedParamPerms_2282_, v_argsPacker_2283_, v_preDefs_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
lean_dec(v_a_2288_);
lean_dec_ref(v_a_2287_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(lean_object* v___x_2291_, lean_object* v_ys_2292_, lean_object* v_as_2293_, size_t v_sz_2294_, size_t v_i_2295_, lean_object* v_bs_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2291_, v_ys_2292_, v_sz_2294_, v_i_2295_, v_bs_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___boxed(lean_object* v___x_2303_, lean_object* v_ys_2304_, lean_object* v_as_2305_, lean_object* v_sz_2306_, lean_object* v_i_2307_, lean_object* v_bs_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
size_t v_sz_boxed_2314_; size_t v_i_boxed_2315_; lean_object* v_res_2316_; 
v_sz_boxed_2314_ = lean_unbox_usize(v_sz_2306_);
lean_dec(v_sz_2306_);
v_i_boxed_2315_ = lean_unbox_usize(v_i_2307_);
lean_dec(v_i_2307_);
v_res_2316_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(v___x_2303_, v_ys_2304_, v_as_2305_, v_sz_boxed_2314_, v_i_boxed_2315_, v_bs_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec_ref(v_as_2305_);
lean_dec_ref(v___x_2303_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(lean_object* v___x_2317_, lean_object* v_ys_2318_, lean_object* v_as_2319_, size_t v_sz_2320_, size_t v_i_2321_, lean_object* v_bs_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2317_, v_ys_2318_, v_sz_2320_, v_i_2321_, v_bs_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___boxed(lean_object* v___x_2329_, lean_object* v_ys_2330_, lean_object* v_as_2331_, lean_object* v_sz_2332_, lean_object* v_i_2333_, lean_object* v_bs_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
size_t v_sz_boxed_2340_; size_t v_i_boxed_2341_; lean_object* v_res_2342_; 
v_sz_boxed_2340_ = lean_unbox_usize(v_sz_2332_);
lean_dec(v_sz_2332_);
v_i_boxed_2341_ = lean_unbox_usize(v_i_2333_);
lean_dec(v_i_2333_);
v_res_2342_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(v___x_2329_, v_ys_2330_, v_as_2331_, v_sz_boxed_2340_, v_i_boxed_2341_, v_bs_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec_ref(v_as_2331_);
lean_dec_ref(v___x_2329_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(lean_object* v_e_2343_, lean_object* v_k_2344_, uint8_t v_cleanupAnnotations_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v___f_2351_; uint8_t v___x_2352_; uint8_t v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___f_2351_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2351_, 0, v_k_2344_);
v___x_2352_ = 1;
v___x_2353_ = 0;
v___x_2354_ = lean_box(0);
v___x_2355_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2343_, v___x_2352_, v___x_2353_, v___x_2352_, v___x_2353_, v___x_2354_, v___f_2351_, v_cleanupAnnotations_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2355_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2355_);
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
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
v_a_2364_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2355_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2355_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg___boxed(lean_object* v_e_2372_, lean_object* v_k_2373_, lean_object* v_cleanupAnnotations_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2380_; lean_object* v_res_2381_; 
v_cleanupAnnotations_boxed_2380_ = lean_unbox(v_cleanupAnnotations_2374_);
v_res_2381_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2372_, v_k_2373_, v_cleanupAnnotations_boxed_2380_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(lean_object* v_00_u03b1_2382_, lean_object* v_e_2383_, lean_object* v_k_2384_, uint8_t v_cleanupAnnotations_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2383_, v_k_2384_, v_cleanupAnnotations_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___boxed(lean_object* v_00_u03b1_2392_, lean_object* v_e_2393_, lean_object* v_k_2394_, lean_object* v_cleanupAnnotations_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2401_; lean_object* v_res_2402_; 
v_cleanupAnnotations_boxed_2401_ = lean_unbox(v_cleanupAnnotations_2395_);
v_res_2402_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(v_00_u03b1_2392_, v_e_2393_, v_k_2394_, v_cleanupAnnotations_boxed_2401_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(lean_object* v_msg_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v___f_2409_; lean_object* v___x_1649__overap_2410_; lean_object* v___x_2411_; 
v___f_2409_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1649__overap_2410_ = lean_panic_fn_borrowed(v___f_2409_, v_msg_2403_);
lean_inc(v___y_2407_);
lean_inc_ref(v___y_2406_);
lean_inc(v___y_2405_);
lean_inc_ref(v___y_2404_);
v___x_2411_ = lean_apply_5(v___x_1649__overap_2410_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, lean_box(0));
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1___boxed(lean_object* v_msg_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v_msg_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0(lean_object* v_xs_2419_, lean_object* v_x_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = lean_array_get_size(v_xs_2419_);
v___x_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0___boxed(lean_object* v_xs_2428_, lean_object* v_x_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Lean_Elab_WF_varyingVarNames___lam__0(v_xs_2428_, v_x_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec_ref(v_x_2429_);
lean_dec_ref(v_xs_2428_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(lean_object* v_as_2436_, size_t v_sz_2437_, size_t v_i_2438_, lean_object* v_b_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v_a_2445_; uint8_t v___x_2449_; 
v___x_2449_ = lean_usize_dec_lt(v_i_2438_, v_sz_2437_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; 
v___x_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2450_, 0, v_b_2439_);
return v___x_2450_;
}
else
{
lean_object* v_snd_2451_; lean_object* v_fst_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2496_; 
v_snd_2451_ = lean_ctor_get(v_b_2439_, 1);
v_fst_2452_ = lean_ctor_get(v_b_2439_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_b_2439_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2454_ = v_b_2439_;
v_isShared_2455_ = v_isSharedCheck_2496_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_snd_2451_);
lean_inc(v_fst_2452_);
lean_dec(v_b_2439_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2496_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v_array_2456_; lean_object* v_start_2457_; lean_object* v_stop_2458_; uint8_t v___x_2459_; 
v_array_2456_ = lean_ctor_get(v_snd_2451_, 0);
v_start_2457_ = lean_ctor_get(v_snd_2451_, 1);
v_stop_2458_ = lean_ctor_get(v_snd_2451_, 2);
v___x_2459_ = lean_nat_dec_lt(v_start_2457_, v_stop_2458_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2461_; 
if (v_isShared_2455_ == 0)
{
v___x_2461_ = v___x_2454_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_fst_2452_);
lean_ctor_set(v_reuseFailAlloc_2463_, 1, v_snd_2451_);
v___x_2461_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
return v___x_2462_;
}
}
else
{
lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2492_; 
lean_inc(v_stop_2458_);
lean_inc(v_start_2457_);
lean_inc_ref(v_array_2456_);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_snd_2451_);
if (v_isSharedCheck_2492_ == 0)
{
lean_object* v_unused_2493_; lean_object* v_unused_2494_; lean_object* v_unused_2495_; 
v_unused_2493_ = lean_ctor_get(v_snd_2451_, 2);
lean_dec(v_unused_2493_);
v_unused_2494_ = lean_ctor_get(v_snd_2451_, 1);
lean_dec(v_unused_2494_);
v_unused_2495_ = lean_ctor_get(v_snd_2451_, 0);
lean_dec(v_unused_2495_);
v___x_2465_ = v_snd_2451_;
v_isShared_2466_ = v_isSharedCheck_2492_;
goto v_resetjp_2464_;
}
else
{
lean_dec(v_snd_2451_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2492_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2467_ = lean_array_fget(v_array_2456_, v_start_2457_);
v___x_2468_ = lean_unsigned_to_nat(1u);
v___x_2469_ = lean_nat_add(v_start_2457_, v___x_2468_);
lean_dec(v_start_2457_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 1, v___x_2469_);
v___x_2471_ = v___x_2465_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_array_2456_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_stop_2458_);
v___x_2471_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v_a_2472_ = lean_array_uget_borrowed(v_as_2436_, v_i_2438_);
v___x_2473_ = l_Lean_Expr_fvarId_x21(v_a_2472_);
v___x_2474_ = l_Lean_FVarId_getUserName___redArg(v___x_2473_, v___y_2440_, v___y_2441_, v___y_2442_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v___x_2476_; lean_object* v___x_2478_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref_known(v___x_2474_, 1);
v___x_2476_ = lean_array_push(v_fst_2452_, v_a_2475_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 1, v___x_2471_);
lean_ctor_set(v___x_2454_, 0, v___x_2476_);
v___x_2478_ = v___x_2454_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2476_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v___x_2471_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
v_a_2445_ = v___x_2478_;
goto v___jp_2444_;
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
lean_dec_ref(v___x_2471_);
lean_del_object(v___x_2454_);
lean_dec(v_fst_2452_);
v_a_2480_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2474_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2474_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
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
}
else
{
lean_object* v___x_2489_; 
lean_dec_ref_known(v___x_2467_, 1);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 1, v___x_2471_);
v___x_2489_ = v___x_2454_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_fst_2452_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v___x_2471_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
v_a_2445_ = v___x_2489_;
goto v___jp_2444_;
}
}
}
}
}
}
}
v___jp_2444_:
{
size_t v___x_2446_; size_t v___x_2447_; 
v___x_2446_ = ((size_t)1ULL);
v___x_2447_ = lean_usize_add(v_i_2438_, v___x_2446_);
v_i_2438_ = v___x_2447_;
v_b_2439_ = v_a_2445_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg___boxed(lean_object* v_as_2497_, lean_object* v_sz_2498_, lean_object* v_i_2499_, lean_object* v_b_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
size_t v_sz_boxed_2505_; size_t v_i_boxed_2506_; lean_object* v_res_2507_; 
v_sz_boxed_2505_ = lean_unbox_usize(v_sz_2498_);
lean_dec(v_sz_2498_);
v_i_boxed_2506_ = lean_unbox_usize(v_i_2499_);
lean_dec(v_i_2499_);
v_res_2507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2497_, v_sz_boxed_2505_, v_i_boxed_2506_, v_b_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec_ref(v_as_2497_);
return v_res_2507_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2510_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1));
v___x_2511_ = lean_unsigned_to_nat(4u);
v___x_2512_ = lean_unsigned_to_nat(119u);
v___x_2513_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2514_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2515_ = l_mkPanicMessageWithDecl(v___x_2514_, v___x_2513_, v___x_2512_, v___x_2511_, v___x_2510_);
return v___x_2515_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2517_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3));
v___x_2518_ = lean_unsigned_to_nat(4u);
v___x_2519_ = lean_unsigned_to_nat(120u);
v___x_2520_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2521_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2522_ = l_mkPanicMessageWithDecl(v___x_2521_, v___x_2520_, v___x_2519_, v___x_2518_, v___x_2517_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1(lean_object* v_a_2525_, lean_object* v_fixedParamPerms_2526_, lean_object* v___x_2527_, lean_object* v_preDefIdx_2528_, lean_object* v_xs_2529_, lean_object* v_x_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v___x_2536_; uint8_t v___x_2537_; 
v___x_2536_ = lean_array_get_size(v_xs_2529_);
v___x_2537_ = lean_nat_dec_eq(v___x_2536_, v_a_2525_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2);
v___x_2539_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2538_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
return v___x_2539_;
}
else
{
lean_object* v_perms_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; uint8_t v___x_2543_; 
v_perms_2540_ = lean_ctor_get(v_fixedParamPerms_2526_, 1);
v___x_2541_ = lean_array_get_borrowed(v___x_2527_, v_perms_2540_, v_preDefIdx_2528_);
v___x_2542_ = lean_array_get_size(v___x_2541_);
v___x_2543_ = lean_nat_dec_eq(v___x_2542_, v_a_2525_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4);
v___x_2545_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2544_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
return v___x_2545_;
}
else
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; size_t v_sz_2550_; size_t v___x_2551_; lean_object* v___x_2552_; 
v___x_2546_ = lean_unsigned_to_nat(0u);
v___x_2547_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5));
lean_inc(v___x_2541_);
v___x_2548_ = l_Array_toSubarray___redArg(v___x_2541_, v___x_2546_, v___x_2542_);
v___x_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2547_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v_sz_2550_ = lean_array_size(v_xs_2529_);
v___x_2551_ = ((size_t)0ULL);
v___x_2552_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_xs_2529_, v_sz_2550_, v___x_2551_, v___x_2549_, v___y_2531_, v___y_2533_, v___y_2534_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2561_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2555_ = v___x_2552_;
v_isShared_2556_ = v_isSharedCheck_2561_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2552_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2561_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v_fst_2557_; lean_object* v___x_2559_; 
v_fst_2557_ = lean_ctor_get(v_a_2553_, 0);
lean_inc(v_fst_2557_);
lean_dec(v_a_2553_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v_fst_2557_);
v___x_2559_ = v___x_2555_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_fst_2557_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
v_a_2562_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2552_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2552_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___boxed(lean_object* v_a_2570_, lean_object* v_fixedParamPerms_2571_, lean_object* v___x_2572_, lean_object* v_preDefIdx_2573_, lean_object* v_xs_2574_, lean_object* v_x_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lean_Elab_WF_varyingVarNames___lam__1(v_a_2570_, v_fixedParamPerms_2571_, v___x_2572_, v_preDefIdx_2573_, v_xs_2574_, v_x_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec_ref(v_x_2575_);
lean_dec_ref(v_xs_2574_);
lean_dec(v_preDefIdx_2573_);
lean_dec_ref(v___x_2572_);
lean_dec_ref(v_fixedParamPerms_2571_);
lean_dec(v_a_2570_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object* v_fixedParamPerms_2583_, lean_object* v_preDefIdx_2584_, lean_object* v_preDef_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_){
_start:
{
lean_object* v_type_2591_; lean_object* v_value_2592_; lean_object* v___f_2593_; lean_object* v___x_2594_; uint8_t v___x_2595_; lean_object* v___x_2596_; 
v_type_2591_ = lean_ctor_get(v_preDef_2585_, 6);
lean_inc_ref(v_type_2591_);
v_value_2592_ = lean_ctor_get(v_preDef_2585_, 7);
lean_inc_ref(v_value_2592_);
lean_dec_ref(v_preDef_2585_);
v___f_2593_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___closed__0));
v___x_2594_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2595_ = 0;
v___x_2596_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_value_2592_, v___f_2593_, v___x_2595_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v___f_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc_n(v_a_2597_, 2);
lean_dec_ref_known(v___x_2596_, 1);
v___f_2598_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_varyingVarNames___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2598_, 0, v_a_2597_);
lean_closure_set(v___f_2598_, 1, v_fixedParamPerms_2583_);
lean_closure_set(v___f_2598_, 2, v___x_2594_);
lean_closure_set(v___f_2598_, 3, v_preDefIdx_2584_);
v___x_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2599_, 0, v_a_2597_);
v___x_2600_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2591_, v___x_2599_, v___f_2598_, v___x_2595_, v___x_2595_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_);
return v___x_2600_;
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
lean_dec_ref(v_type_2591_);
lean_dec(v_preDefIdx_2584_);
lean_dec_ref(v_fixedParamPerms_2583_);
v_a_2601_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2596_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2596_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___boxed(lean_object* v_fixedParamPerms_2609_, lean_object* v_preDefIdx_2610_, lean_object* v_preDef_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Lean_Elab_WF_varyingVarNames(v_fixedParamPerms_2609_, v_preDefIdx_2610_, v_preDef_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
lean_dec(v_a_2613_);
lean_dec_ref(v_a_2612_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(lean_object* v_as_2618_, size_t v_sz_2619_, size_t v_i_2620_, lean_object* v_b_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v___x_2627_; 
v___x_2627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2618_, v_sz_2619_, v_i_2620_, v_b_2621_, v___y_2622_, v___y_2624_, v___y_2625_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___boxed(lean_object* v_as_2628_, lean_object* v_sz_2629_, lean_object* v_i_2630_, lean_object* v_b_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
size_t v_sz_boxed_2637_; size_t v_i_boxed_2638_; lean_object* v_res_2639_; 
v_sz_boxed_2637_ = lean_unbox_usize(v_sz_2629_);
lean_dec(v_sz_2629_);
v_i_boxed_2638_ = lean_unbox_usize(v_i_2630_);
lean_dec(v_i_2630_);
v_res_2639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(v_as_2628_, v_sz_boxed_2637_, v_i_boxed_2638_, v_b_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec_ref(v_as_2628_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(lean_object* v_msg_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___f_2646_; lean_object* v___x_1596__overap_2647_; lean_object* v___x_2648_; 
v___f_2646_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1596__overap_2647_ = lean_panic_fn_borrowed(v___f_2646_, v_msg_2640_);
lean_inc(v___y_2644_);
lean_inc_ref(v___y_2643_);
lean_inc(v___y_2642_);
lean_inc_ref(v___y_2641_);
v___x_2648_ = lean_apply_5(v___x_1596__overap_2647_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, lean_box(0));
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0___boxed(lean_object* v_msg_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v_msg_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
return v_res_2655_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2656_; double v___x_2657_; 
v___x_2656_ = lean_unsigned_to_nat(0u);
v___x_2657_ = lean_float_of_nat(v___x_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(lean_object* v_cls_2661_, lean_object* v_msg_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_ref_2668_; lean_object* v___x_2669_; lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2715_; 
v_ref_2668_ = lean_ctor_get(v___y_2665_, 2);
v___x_2669_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msg_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2672_ = v___x_2669_;
v_isShared_2673_ = v_isSharedCheck_2715_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2669_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2715_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; lean_object* v_traceState_2675_; lean_object* v_env_2676_; lean_object* v_nextMacroScope_2677_; lean_object* v_ngen_2678_; lean_object* v_auxDeclNGen_2679_; lean_object* v_cache_2680_; lean_object* v_recordedDeps_2681_; lean_object* v_messages_2682_; lean_object* v_infoState_2683_; lean_object* v_snapshotTasks_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2714_; 
v___x_2674_ = lean_st_ref_take(v___y_2666_);
v_traceState_2675_ = lean_ctor_get(v___x_2674_, 4);
v_env_2676_ = lean_ctor_get(v___x_2674_, 0);
v_nextMacroScope_2677_ = lean_ctor_get(v___x_2674_, 1);
v_ngen_2678_ = lean_ctor_get(v___x_2674_, 2);
v_auxDeclNGen_2679_ = lean_ctor_get(v___x_2674_, 3);
v_cache_2680_ = lean_ctor_get(v___x_2674_, 5);
v_recordedDeps_2681_ = lean_ctor_get(v___x_2674_, 6);
v_messages_2682_ = lean_ctor_get(v___x_2674_, 7);
v_infoState_2683_ = lean_ctor_get(v___x_2674_, 8);
v_snapshotTasks_2684_ = lean_ctor_get(v___x_2674_, 9);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2686_ = v___x_2674_;
v_isShared_2687_ = v_isSharedCheck_2714_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_snapshotTasks_2684_);
lean_inc(v_infoState_2683_);
lean_inc(v_messages_2682_);
lean_inc(v_recordedDeps_2681_);
lean_inc(v_cache_2680_);
lean_inc(v_traceState_2675_);
lean_inc(v_auxDeclNGen_2679_);
lean_inc(v_ngen_2678_);
lean_inc(v_nextMacroScope_2677_);
lean_inc(v_env_2676_);
lean_dec(v___x_2674_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2714_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
uint64_t v_tid_2688_; lean_object* v_traces_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2713_; 
v_tid_2688_ = lean_ctor_get_uint64(v_traceState_2675_, sizeof(void*)*1);
v_traces_2689_ = lean_ctor_get(v_traceState_2675_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v_traceState_2675_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2691_ = v_traceState_2675_;
v_isShared_2692_ = v_isSharedCheck_2713_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_traces_2689_);
lean_dec(v_traceState_2675_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2713_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; double v___x_2695_; uint8_t v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2693_ = lean_box(0);
v___x_2694_ = lean_box(0);
v___x_2695_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0);
v___x_2696_ = 0;
v___x_2697_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1));
v___x_2698_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2698_, 0, v_cls_2661_);
lean_ctor_set(v___x_2698_, 1, v___x_2694_);
lean_ctor_set(v___x_2698_, 2, v___x_2697_);
lean_ctor_set_float(v___x_2698_, sizeof(void*)*3, v___x_2695_);
lean_ctor_set_float(v___x_2698_, sizeof(void*)*3 + 8, v___x_2695_);
lean_ctor_set_uint8(v___x_2698_, sizeof(void*)*3 + 16, v___x_2696_);
v___x_2699_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2));
v___x_2700_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v_a_2670_);
lean_ctor_set(v___x_2700_, 2, v___x_2699_);
lean_inc(v_ref_2668_);
v___x_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2701_, 0, v_ref_2668_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = l_Lean_PersistentArray_push___redArg(v_traces_2689_, v___x_2701_);
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 0, v___x_2702_);
v___x_2704_ = v___x_2691_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2702_);
lean_ctor_set_uint64(v_reuseFailAlloc_2712_, sizeof(void*)*1, v_tid_2688_);
v___x_2704_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2706_; 
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 4, v___x_2704_);
v___x_2706_ = v___x_2686_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_env_2676_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v_nextMacroScope_2677_);
lean_ctor_set(v_reuseFailAlloc_2711_, 2, v_ngen_2678_);
lean_ctor_set(v_reuseFailAlloc_2711_, 3, v_auxDeclNGen_2679_);
lean_ctor_set(v_reuseFailAlloc_2711_, 4, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2711_, 5, v_cache_2680_);
lean_ctor_set(v_reuseFailAlloc_2711_, 6, v_recordedDeps_2681_);
lean_ctor_set(v_reuseFailAlloc_2711_, 7, v_messages_2682_);
lean_ctor_set(v_reuseFailAlloc_2711_, 8, v_infoState_2683_);
lean_ctor_set(v_reuseFailAlloc_2711_, 9, v_snapshotTasks_2684_);
v___x_2706_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2707_; lean_object* v___x_2709_; 
v___x_2707_ = lean_st_ref_put(v___y_2666_, v___x_2706_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 0, v___x_2693_);
v___x_2709_ = v___x_2672_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2693_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___boxed(lean_object* v_cls_2716_, lean_object* v_msg_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v_cls_2716_, v_msg_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
return v_res_2723_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1));
v___x_2727_ = lean_unsigned_to_nat(8u);
v___x_2728_ = lean_unsigned_to_nat(135u);
v___x_2729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0));
v___x_2730_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2731_ = l_mkPanicMessageWithDecl(v___x_2730_, v___x_2729_, v___x_2728_, v___x_2727_, v___x_2726_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(lean_object* v___x_2732_, lean_object* v_unaryPreDefNonRec_2733_, lean_object* v___x_2734_, lean_object* v_us_2735_, lean_object* v_argsPacker_2736_, lean_object* v___x_2737_, lean_object* v_params_2738_, lean_object* v_x_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v___x_2745_; uint8_t v___x_2746_; 
v___x_2745_ = lean_array_get_size(v_params_2738_);
v___x_2746_ = lean_nat_dec_eq(v___x_2732_, v___x_2745_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
lean_dec(v___x_2737_);
lean_dec(v_us_2735_);
lean_dec_ref(v_unaryPreDefNonRec_2733_);
v___x_2747_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2);
v___x_2748_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v___x_2747_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
return v___x_2748_;
}
else
{
lean_object* v_declName_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v_declName_2749_ = lean_ctor_get(v_unaryPreDefNonRec_2733_, 3);
lean_inc(v_declName_2749_);
lean_dec_ref(v_unaryPreDefNonRec_2733_);
v___x_2750_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v___x_2734_, v_params_2738_);
v___x_2751_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_2734_, v_params_2738_);
v___x_2752_ = l_Lean_mkConst(v_declName_2749_, v_us_2735_);
v___x_2753_ = l_Lean_mkAppN(v___x_2752_, v___x_2750_);
lean_dec_ref(v___x_2750_);
v___x_2754_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_2736_, v___x_2753_, v___x_2737_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2756_; uint8_t v___x_2757_; uint8_t v___x_2758_; lean_object* v___x_2759_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2755_);
lean_dec_ref_known(v___x_2754_, 1);
v___x_2756_ = l_Lean_Expr_beta(v_a_2755_, v___x_2751_);
v___x_2757_ = 0;
v___x_2758_ = 1;
v___x_2759_ = l_Lean_Meta_mkLambdaFVars(v_params_2738_, v___x_2756_, v___x_2757_, v___x_2746_, v___x_2757_, v___x_2746_, v___x_2758_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
return v___x_2759_;
}
else
{
lean_dec_ref(v___x_2751_);
return v___x_2754_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed(lean_object* v___x_2760_, lean_object* v_unaryPreDefNonRec_2761_, lean_object* v___x_2762_, lean_object* v_us_2763_, lean_object* v_argsPacker_2764_, lean_object* v___x_2765_, lean_object* v_params_2766_, lean_object* v_x_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(v___x_2760_, v_unaryPreDefNonRec_2761_, v___x_2762_, v_us_2763_, v_argsPacker_2764_, v___x_2765_, v_params_2766_, v_x_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec_ref(v_x_2767_);
lean_dec_ref(v_params_2766_);
lean_dec_ref(v_argsPacker_2764_);
lean_dec_ref(v___x_2762_);
lean_dec(v___x_2760_);
return v_res_2773_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2785_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5));
v___x_2786_ = l_Lean_Name_append(v___x_2785_, v___x_2784_);
return v___x_2786_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7));
v___x_2789_ = l_Lean_stringToMessageData(v___x_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(lean_object* v_fixedParamPerms_2790_, lean_object* v_unaryPreDefNonRec_2791_, lean_object* v_us_2792_, lean_object* v_argsPacker_2793_, size_t v_sz_2794_, size_t v_i_2795_, lean_object* v_bs_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
uint8_t v___x_2802_; 
v___x_2802_ = lean_usize_dec_lt(v_i_2795_, v_sz_2794_);
if (v___x_2802_ == 0)
{
lean_object* v___x_2803_; 
lean_dec_ref(v_argsPacker_2793_);
lean_dec(v_us_2792_);
lean_dec_ref(v_unaryPreDefNonRec_2791_);
v___x_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2803_, 0, v_bs_2796_);
return v___x_2803_;
}
else
{
lean_object* v_v_2804_; lean_object* v_perms_2805_; lean_object* v_ref_2806_; uint8_t v_kind_2807_; lean_object* v_levelParams_2808_; lean_object* v_modifiers_2809_; lean_object* v_declName_2810_; lean_object* v_binders_2811_; lean_object* v_numSectionVars_2812_; lean_object* v_type_2813_; lean_object* v_termination_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2866_; 
v_v_2804_ = lean_array_uget(v_bs_2796_, v_i_2795_);
v_perms_2805_ = lean_ctor_get(v_fixedParamPerms_2790_, 1);
v_ref_2806_ = lean_ctor_get(v_v_2804_, 0);
v_kind_2807_ = lean_ctor_get_uint8(v_v_2804_, sizeof(void*)*9);
v_levelParams_2808_ = lean_ctor_get(v_v_2804_, 1);
v_modifiers_2809_ = lean_ctor_get(v_v_2804_, 2);
v_declName_2810_ = lean_ctor_get(v_v_2804_, 3);
v_binders_2811_ = lean_ctor_get(v_v_2804_, 4);
v_numSectionVars_2812_ = lean_ctor_get(v_v_2804_, 5);
v_type_2813_ = lean_ctor_get(v_v_2804_, 6);
v_termination_2814_ = lean_ctor_get(v_v_2804_, 8);
v_isSharedCheck_2866_ = !lean_is_exclusive(v_v_2804_);
if (v_isSharedCheck_2866_ == 0)
{
lean_object* v_unused_2867_; 
v_unused_2867_ = lean_ctor_get(v_v_2804_, 7);
lean_dec(v_unused_2867_);
v___x_2816_ = v_v_2804_;
v_isShared_2817_ = v_isSharedCheck_2866_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_termination_2814_);
lean_inc(v_type_2813_);
lean_inc(v_numSectionVars_2812_);
lean_inc(v_binders_2811_);
lean_inc(v_declName_2810_);
lean_inc(v_modifiers_2809_);
lean_inc(v_levelParams_2808_);
lean_inc(v_ref_2806_);
lean_dec(v_v_2804_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2866_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2818_; lean_object* v_bs_x27_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___f_2824_; lean_object* v___x_2825_; uint8_t v___x_2826_; lean_object* v___x_2827_; 
v___x_2818_ = lean_unsigned_to_nat(0u);
v_bs_x27_2819_ = lean_array_uset(v_bs_2796_, v_i_2795_, v___x_2818_);
v___x_2820_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2821_ = lean_usize_to_nat(v_i_2795_);
v___x_2822_ = lean_array_get_borrowed(v___x_2820_, v_perms_2805_, v___x_2821_);
v___x_2823_ = lean_array_get_size(v___x_2822_);
lean_inc_ref(v_argsPacker_2793_);
lean_inc(v_us_2792_);
lean_inc(v___x_2822_);
lean_inc_ref(v_unaryPreDefNonRec_2791_);
v___f_2824_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2824_, 0, v___x_2823_);
lean_closure_set(v___f_2824_, 1, v_unaryPreDefNonRec_2791_);
lean_closure_set(v___f_2824_, 2, v___x_2822_);
lean_closure_set(v___f_2824_, 3, v_us_2792_);
lean_closure_set(v___f_2824_, 4, v_argsPacker_2793_);
lean_closure_set(v___f_2824_, 5, v___x_2821_);
v___x_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2823_);
v___x_2826_ = 0;
lean_inc_ref(v_type_2813_);
v___x_2827_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2813_, v___x_2825_, v___f_2824_, v___x_2826_, v___x_2826_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v_toCold_2837_; lean_object* v_options_2838_; uint8_t v_hasTrace_2839_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2827_, 1);
v_toCold_2837_ = lean_ctor_get(v___y_2799_, 0);
v_options_2838_ = lean_ctor_get(v_toCold_2837_, 2);
v_hasTrace_2839_ = lean_ctor_get_uint8(v_options_2838_, sizeof(void*)*1);
if (v_hasTrace_2839_ == 0)
{
goto v___jp_2829_;
}
else
{
lean_object* v_inheritedTraceOptions_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
v_inheritedTraceOptions_2840_ = lean_ctor_get(v_toCold_2837_, 11);
v___x_2841_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2842_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6);
v___x_2843_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2840_, v_options_2838_, v___x_2842_);
if (v___x_2843_ == 0)
{
goto v___jp_2829_;
}
else
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
lean_inc(v_declName_2810_);
v___x_2844_ = l_Lean_MessageData_ofName(v_declName_2810_);
v___x_2845_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8);
v___x_2846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2844_);
lean_ctor_set(v___x_2846_, 1, v___x_2845_);
lean_inc(v_a_2828_);
v___x_2847_ = l_Lean_MessageData_ofExpr(v_a_2828_);
v___x_2848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2846_);
lean_ctor_set(v___x_2848_, 1, v___x_2847_);
v___x_2849_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v___x_2841_, v___x_2848_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_dec_ref_known(v___x_2849_, 1);
goto v___jp_2829_;
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_dec(v_a_2828_);
lean_dec_ref(v_bs_x27_2819_);
lean_del_object(v___x_2816_);
lean_dec_ref(v_termination_2814_);
lean_dec_ref(v_type_2813_);
lean_dec(v_numSectionVars_2812_);
lean_dec(v_binders_2811_);
lean_dec(v_declName_2810_);
lean_dec_ref(v_modifiers_2809_);
lean_dec(v_levelParams_2808_);
lean_dec(v_ref_2806_);
lean_dec_ref(v_argsPacker_2793_);
lean_dec(v_us_2792_);
lean_dec_ref(v_unaryPreDefNonRec_2791_);
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2849_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2849_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
}
v___jp_2829_:
{
lean_object* v___x_2831_; 
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 7, v_a_2828_);
v___x_2831_ = v___x_2816_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_ref_2806_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_levelParams_2808_);
lean_ctor_set(v_reuseFailAlloc_2836_, 2, v_modifiers_2809_);
lean_ctor_set(v_reuseFailAlloc_2836_, 3, v_declName_2810_);
lean_ctor_set(v_reuseFailAlloc_2836_, 4, v_binders_2811_);
lean_ctor_set(v_reuseFailAlloc_2836_, 5, v_numSectionVars_2812_);
lean_ctor_set(v_reuseFailAlloc_2836_, 6, v_type_2813_);
lean_ctor_set(v_reuseFailAlloc_2836_, 7, v_a_2828_);
lean_ctor_set(v_reuseFailAlloc_2836_, 8, v_termination_2814_);
lean_ctor_set_uint8(v_reuseFailAlloc_2836_, sizeof(void*)*9, v_kind_2807_);
v___x_2831_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
size_t v___x_2832_; size_t v___x_2833_; lean_object* v___x_2834_; 
v___x_2832_ = ((size_t)1ULL);
v___x_2833_ = lean_usize_add(v_i_2795_, v___x_2832_);
v___x_2834_ = lean_array_uset(v_bs_x27_2819_, v_i_2795_, v___x_2831_);
v_i_2795_ = v___x_2833_;
v_bs_2796_ = v___x_2834_;
goto _start;
}
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec_ref(v_bs_x27_2819_);
lean_del_object(v___x_2816_);
lean_dec_ref(v_termination_2814_);
lean_dec_ref(v_type_2813_);
lean_dec(v_numSectionVars_2812_);
lean_dec(v_binders_2811_);
lean_dec(v_declName_2810_);
lean_dec_ref(v_modifiers_2809_);
lean_dec(v_levelParams_2808_);
lean_dec(v_ref_2806_);
lean_dec_ref(v_argsPacker_2793_);
lean_dec(v_us_2792_);
lean_dec_ref(v_unaryPreDefNonRec_2791_);
v_a_2858_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2827_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2827_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_2868_, lean_object* v_unaryPreDefNonRec_2869_, lean_object* v_us_2870_, lean_object* v_argsPacker_2871_, lean_object* v_sz_2872_, lean_object* v_i_2873_, lean_object* v_bs_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
size_t v_sz_boxed_2880_; size_t v_i_boxed_2881_; lean_object* v_res_2882_; 
v_sz_boxed_2880_ = lean_unbox_usize(v_sz_2872_);
lean_dec(v_sz_2872_);
v_i_boxed_2881_ = lean_unbox_usize(v_i_2873_);
lean_dec(v_i_2873_);
v_res_2882_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2868_, v_unaryPreDefNonRec_2869_, v_us_2870_, v_argsPacker_2871_, v_sz_boxed_2880_, v_i_boxed_2881_, v_bs_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec_ref(v_fixedParamPerms_2868_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(lean_object* v_unaryPreDefNonRec_2883_, lean_object* v_preDefs_2884_, lean_object* v_fixedParamPerms_2885_, lean_object* v_us_2886_, lean_object* v_argsPacker_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l_Lean_Elab_addAsAxiom___redArg(v_unaryPreDefNonRec_2883_, v___y_2890_, v___y_2891_);
if (lean_obj_tag(v___x_2893_) == 0)
{
size_t v_sz_2894_; size_t v___x_2895_; lean_object* v___x_2896_; 
lean_dec_ref_known(v___x_2893_, 1);
v_sz_2894_ = lean_array_size(v_preDefs_2884_);
v___x_2895_ = ((size_t)0ULL);
v___x_2896_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2885_, v_unaryPreDefNonRec_2883_, v_us_2886_, v_argsPacker_2887_, v_sz_2894_, v___x_2895_, v_preDefs_2884_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
return v___x_2896_;
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_dec_ref(v_argsPacker_2887_);
lean_dec(v_us_2886_);
lean_dec_ref(v_preDefs_2884_);
lean_dec_ref(v_unaryPreDefNonRec_2883_);
v_a_2897_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2893_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2893_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed(lean_object* v_unaryPreDefNonRec_2905_, lean_object* v_preDefs_2906_, lean_object* v_fixedParamPerms_2907_, lean_object* v_us_2908_, lean_object* v_argsPacker_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(v_unaryPreDefNonRec_2905_, v_preDefs_2906_, v_fixedParamPerms_2907_, v_us_2908_, v_argsPacker_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec_ref(v_fixedParamPerms_2907_);
return v_res_2915_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2916_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0);
v___x_2918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
return v___x_2918_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
v___x_2920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2919_);
lean_ctor_set(v___x_2920_, 1, v___x_2919_);
return v___x_2920_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2921_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
v___x_2922_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
lean_ctor_set(v___x_2922_, 2, v___x_2921_);
lean_ctor_set(v___x_2922_, 3, v___x_2921_);
lean_ctor_set(v___x_2922_, 4, v___x_2921_);
lean_ctor_set(v___x_2922_, 5, v___x_2921_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(lean_object* v_env_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v___x_2927_; lean_object* v_nextMacroScope_2928_; lean_object* v_ngen_2929_; lean_object* v_auxDeclNGen_2930_; lean_object* v_traceState_2931_; lean_object* v_recordedDeps_2932_; lean_object* v_messages_2933_; lean_object* v_infoState_2934_; lean_object* v_snapshotTasks_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2961_; 
v___x_2927_ = lean_st_ref_take(v___y_2925_);
v_nextMacroScope_2928_ = lean_ctor_get(v___x_2927_, 1);
v_ngen_2929_ = lean_ctor_get(v___x_2927_, 2);
v_auxDeclNGen_2930_ = lean_ctor_get(v___x_2927_, 3);
v_traceState_2931_ = lean_ctor_get(v___x_2927_, 4);
v_recordedDeps_2932_ = lean_ctor_get(v___x_2927_, 6);
v_messages_2933_ = lean_ctor_get(v___x_2927_, 7);
v_infoState_2934_ = lean_ctor_get(v___x_2927_, 8);
v_snapshotTasks_2935_ = lean_ctor_get(v___x_2927_, 9);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2961_ == 0)
{
lean_object* v_unused_2962_; lean_object* v_unused_2963_; 
v_unused_2962_ = lean_ctor_get(v___x_2927_, 5);
lean_dec(v_unused_2962_);
v_unused_2963_ = lean_ctor_get(v___x_2927_, 0);
lean_dec(v_unused_2963_);
v___x_2937_ = v___x_2927_;
v_isShared_2938_ = v_isSharedCheck_2961_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_snapshotTasks_2935_);
lean_inc(v_infoState_2934_);
lean_inc(v_messages_2933_);
lean_inc(v_recordedDeps_2932_);
lean_inc(v_traceState_2931_);
lean_inc(v_auxDeclNGen_2930_);
lean_inc(v_ngen_2929_);
lean_inc(v_nextMacroScope_2928_);
lean_dec(v___x_2927_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2961_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2939_; lean_object* v___x_2941_; 
v___x_2939_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 5, v___x_2939_);
lean_ctor_set(v___x_2937_, 0, v_env_2923_);
v___x_2941_ = v___x_2937_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_env_2923_);
lean_ctor_set(v_reuseFailAlloc_2960_, 1, v_nextMacroScope_2928_);
lean_ctor_set(v_reuseFailAlloc_2960_, 2, v_ngen_2929_);
lean_ctor_set(v_reuseFailAlloc_2960_, 3, v_auxDeclNGen_2930_);
lean_ctor_set(v_reuseFailAlloc_2960_, 4, v_traceState_2931_);
lean_ctor_set(v_reuseFailAlloc_2960_, 5, v___x_2939_);
lean_ctor_set(v_reuseFailAlloc_2960_, 6, v_recordedDeps_2932_);
lean_ctor_set(v_reuseFailAlloc_2960_, 7, v_messages_2933_);
lean_ctor_set(v_reuseFailAlloc_2960_, 8, v_infoState_2934_);
lean_ctor_set(v_reuseFailAlloc_2960_, 9, v_snapshotTasks_2935_);
v___x_2941_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v_mctx_2944_; lean_object* v_zetaDeltaFVarIds_2945_; lean_object* v_postponed_2946_; lean_object* v_diag_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2958_; 
v___x_2942_ = lean_st_ref_put(v___y_2925_, v___x_2941_);
v___x_2943_ = lean_st_ref_take(v___y_2924_);
v_mctx_2944_ = lean_ctor_get(v___x_2943_, 0);
v_zetaDeltaFVarIds_2945_ = lean_ctor_get(v___x_2943_, 2);
v_postponed_2946_ = lean_ctor_get(v___x_2943_, 3);
v_diag_2947_ = lean_ctor_get(v___x_2943_, 4);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2958_ == 0)
{
lean_object* v_unused_2959_; 
v_unused_2959_ = lean_ctor_get(v___x_2943_, 1);
lean_dec(v_unused_2959_);
v___x_2949_ = v___x_2943_;
v_isShared_2950_ = v_isSharedCheck_2958_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_diag_2947_);
lean_inc(v_postponed_2946_);
lean_inc(v_zetaDeltaFVarIds_2945_);
lean_inc(v_mctx_2944_);
lean_dec(v___x_2943_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2958_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2951_ = lean_box(0);
v___x_2952_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3);
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 1, v___x_2952_);
v___x_2954_ = v___x_2949_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_mctx_2944_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v___x_2952_);
lean_ctor_set(v_reuseFailAlloc_2957_, 2, v_zetaDeltaFVarIds_2945_);
lean_ctor_set(v_reuseFailAlloc_2957_, 3, v_postponed_2946_);
lean_ctor_set(v_reuseFailAlloc_2957_, 4, v_diag_2947_);
v___x_2954_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = lean_st_ref_put(v___y_2924_, v___x_2954_);
v___x_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2951_);
return v___x_2956_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___boxed(lean_object* v_env_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec(v___y_2965_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(lean_object* v_env_2969_, lean_object* v_x_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
lean_object* v___x_2976_; lean_object* v_env_2977_; lean_object* v_a_2979_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2976_ = lean_st_ref_get(v___y_2974_);
v_env_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc_ref(v_env_2977_);
lean_dec(v___x_2976_);
v___x_2989_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2969_, v___y_2972_, v___y_2974_);
lean_dec_ref(v___x_2989_);
lean_inc(v___y_2974_);
lean_inc_ref(v___y_2973_);
lean_inc(v___y_2972_);
lean_inc_ref(v___y_2971_);
v___x_2990_ = lean_apply_5(v_x_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, lean_box(0));
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref_known(v___x_2990_, 1);
v___x_2992_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2977_, v___y_2972_, v___y_2974_);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_2999_ == 0)
{
lean_object* v_unused_3000_; 
v_unused_3000_ = lean_ctor_get(v___x_2992_, 0);
lean_dec(v_unused_3000_);
v___x_2994_ = v___x_2992_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_dec(v___x_2992_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 0, v_a_2991_);
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2991_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
else
{
lean_object* v_a_3001_; 
v_a_3001_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_3001_);
lean_dec_ref_known(v___x_2990_, 1);
v_a_2979_ = v_a_3001_;
goto v___jp_2978_;
}
v___jp_2978_:
{
lean_object* v___x_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
v___x_2980_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2977_, v___y_2972_, v___y_2974_);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; 
v_unused_2988_ = lean_ctor_get(v___x_2980_, 0);
lean_dec(v_unused_2988_);
v___x_2982_ = v___x_2980_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_dec(v___x_2980_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
lean_ctor_set_tag(v___x_2982_, 1);
lean_ctor_set(v___x_2982_, 0, v_a_2979_);
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2979_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___boxed(lean_object* v_env_3002_, lean_object* v_x_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_3002_, v_x_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object* v_fixedParamPerms_3010_, lean_object* v_argsPacker_3011_, lean_object* v_preDefs_3012_, lean_object* v_unaryPreDefNonRec_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_){
_start:
{
lean_object* v_levelParams_3019_; lean_object* v___x_3020_; lean_object* v_us_3021_; lean_object* v___f_3022_; lean_object* v___x_3023_; lean_object* v_env_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v_levelParams_3019_ = lean_ctor_get(v_unaryPreDefNonRec_3013_, 1);
v___x_3020_ = lean_box(0);
lean_inc(v_levelParams_3019_);
v_us_3021_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_3019_, v___x_3020_);
v___f_3022_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3022_, 0, v_unaryPreDefNonRec_3013_);
lean_closure_set(v___f_3022_, 1, v_preDefs_3012_);
lean_closure_set(v___f_3022_, 2, v_fixedParamPerms_3010_);
lean_closure_set(v___f_3022_, 3, v_us_3021_);
lean_closure_set(v___f_3022_, 4, v_argsPacker_3011_);
v___x_3023_ = lean_st_ref_get(v_a_3017_);
v_env_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc_ref(v_env_3024_);
lean_dec(v___x_3023_);
v___x_3025_ = l_Lean_Environment_unlockAsync(v_env_3024_);
v___x_3026_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v___x_3025_, v___f_3022_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___boxed(lean_object* v_fixedParamPerms_3027_, lean_object* v_argsPacker_3028_, lean_object* v_preDefs_3029_, lean_object* v_unaryPreDefNonRec_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fixedParamPerms_3027_, v_argsPacker_3028_, v_preDefs_3029_, v_unaryPreDefNonRec_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(lean_object* v_fixedParamPerms_3037_, lean_object* v_unaryPreDefNonRec_3038_, lean_object* v_us_3039_, lean_object* v_argsPacker_3040_, lean_object* v_as_3041_, size_t v_sz_3042_, size_t v_i_3043_, lean_object* v_bs_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_3037_, v_unaryPreDefNonRec_3038_, v_us_3039_, v_argsPacker_3040_, v_sz_3042_, v_i_3043_, v_bs_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___boxed(lean_object* v_fixedParamPerms_3051_, lean_object* v_unaryPreDefNonRec_3052_, lean_object* v_us_3053_, lean_object* v_argsPacker_3054_, lean_object* v_as_3055_, lean_object* v_sz_3056_, lean_object* v_i_3057_, lean_object* v_bs_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
size_t v_sz_boxed_3064_; size_t v_i_boxed_3065_; lean_object* v_res_3066_; 
v_sz_boxed_3064_ = lean_unbox_usize(v_sz_3056_);
lean_dec(v_sz_3056_);
v_i_boxed_3065_ = lean_unbox_usize(v_i_3057_);
lean_dec(v_i_3057_);
v_res_3066_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(v_fixedParamPerms_3051_, v_unaryPreDefNonRec_3052_, v_us_3053_, v_argsPacker_3054_, v_as_3055_, v_sz_boxed_3064_, v_i_boxed_3065_, v_bs_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec_ref(v_as_3055_);
lean_dec_ref(v_fixedParamPerms_3051_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(lean_object* v_env_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3067_, v___y_3069_, v___y_3071_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___boxed(lean_object* v_env_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(v_env_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(lean_object* v_00_u03b1_3081_, lean_object* v_env_3082_, lean_object* v_x_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v___x_3089_; 
v___x_3089_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_3082_, v_x_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___boxed(lean_object* v_00_u03b1_3090_, lean_object* v_env_3091_, lean_object* v_x_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(v_00_u03b1_3090_, v_env_3091_, v_x_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
return v_res_3098_;
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
