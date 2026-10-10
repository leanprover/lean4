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
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
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
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1_ = stack[0].m_obj;
lean_object* v_b_2_ = stack[1].m_obj;
lean_object* v_c_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v_res_10_;
v_res_10_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0(v_k_1_, v_b_2_, v_c_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_);
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed(lean_object* v_k_11_, lean_object* v_b_12_, lean_object* v_c_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0(v_k_11_, v_b_12_, v_c_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
return v_res_19_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(lean_object* v_type_20_, lean_object* v_maxFVars_x3f_21_, lean_object* v_k_22_, uint8_t v_cleanupAnnotations_23_, uint8_t v_whnfType_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v___f_30_; lean_object* v___x_31_; 
v___f_30_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_30_, 0, v_k_22_);
v___x_31_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_20_, v_maxFVars_x3f_21_, v___f_30_, v_cleanupAnnotations_23_, v_whnfType_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
if (lean_obj_tag(v___x_31_) == 0)
{
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_39_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_39_ == 0)
{
v___x_34_ = v___x_31_;
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_37_; 
if (v_isShared_35_ == 0)
{
v___x_37_ = v___x_34_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_a_32_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
else
{
lean_object* v_a_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_47_; 
v_a_40_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_47_ == 0)
{
v___x_42_ = v___x_31_;
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_a_40_);
lean_dec(v___x_31_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_45_; 
if (v_isShared_43_ == 0)
{
v___x_45_ = v___x_42_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_a_40_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_20_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_21_ = stack[1].m_obj;
lean_object* v_k_22_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_23_ = stack[3].m_num;
uint8_t v_whnfType_24_ = stack[4].m_num;
lean_object* v___y_25_ = stack[5].m_obj;
lean_object* v___y_26_ = stack[6].m_obj;
lean_object* v___y_27_ = stack[7].m_obj;
lean_object* v___y_28_ = stack[8].m_obj;
lean_object* v_res_48_;
v_res_48_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_20_, v_maxFVars_x3f_21_, v_k_22_, v_cleanupAnnotations_23_, v_whnfType_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
stack->m_obj
 = v_res_48_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___boxed(lean_object* v_type_49_, lean_object* v_maxFVars_x3f_50_, lean_object* v_k_51_, lean_object* v_cleanupAnnotations_52_, lean_object* v_whnfType_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_59_; uint8_t v_whnfType_boxed_60_; lean_object* v_res_61_; 
v_cleanupAnnotations_boxed_59_ = lean_unbox(v_cleanupAnnotations_52_);
v_whnfType_boxed_60_ = lean_unbox(v_whnfType_53_);
v_res_61_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_49_, v_maxFVars_x3f_50_, v_k_51_, v_cleanupAnnotations_boxed_59_, v_whnfType_boxed_60_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
return v_res_61_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1(lean_object* v_00_u03b1_62_, lean_object* v_type_63_, lean_object* v_maxFVars_x3f_64_, lean_object* v_k_65_, uint8_t v_cleanupAnnotations_66_, uint8_t v_whnfType_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_63_, v_maxFVars_x3f_64_, v_k_65_, v_cleanupAnnotations_66_, v_whnfType_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
return v___x_73_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_63_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_64_ = stack[2].m_obj;
lean_object* v_k_65_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_66_ = stack[4].m_num;
uint8_t v_whnfType_67_ = stack[5].m_num;
lean_object* v___y_68_ = stack[6].m_obj;
lean_object* v___y_69_ = stack[7].m_obj;
lean_object* v___y_70_ = stack[8].m_obj;
lean_object* v___y_71_ = stack[9].m_obj;
lean_object* v_res_74_;
v_res_74_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1(lean_box(0), v_type_63_, v_maxFVars_x3f_64_, v_k_65_, v_cleanupAnnotations_66_, v_whnfType_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
stack->m_obj
 = v_res_74_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___boxed(lean_object* v_00_u03b1_75_, lean_object* v_type_76_, lean_object* v_maxFVars_x3f_77_, lean_object* v_k_78_, lean_object* v_cleanupAnnotations_79_, lean_object* v_whnfType_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_86_; uint8_t v_whnfType_boxed_87_; lean_object* v_res_88_; 
v_cleanupAnnotations_boxed_86_ = lean_unbox(v_cleanupAnnotations_79_);
v_whnfType_boxed_87_ = lean_unbox(v_whnfType_80_);
v_res_88_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1(v_00_u03b1_75_, v_type_76_, v_maxFVars_x3f_77_, v_k_78_, v_cleanupAnnotations_boxed_86_, v_whnfType_boxed_87_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
return v_res_88_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(lean_object* v_msgData_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v___x_95_; lean_object* v_env_96_; uint8_t v___x_97_; lean_object* v_env_98_; lean_object* v___x_99_; lean_object* v_toCold_100_; lean_object* v_mctx_101_; lean_object* v_lctx_102_; lean_object* v_options_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_95_ = lean_st_ref_get(v___y_93_);
v_env_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc_ref(v_env_96_);
lean_dec(v___x_95_);
v___x_97_ = 0;
v_env_98_ = l_Lean_Environment_setRecordingDeps(v_env_96_, v___x_97_);
v___x_99_ = lean_st_ref_get(v___y_91_);
v_toCold_100_ = lean_ctor_get(v___y_92_, 0);
v_mctx_101_ = lean_ctor_get(v___x_99_, 0);
lean_inc_ref(v_mctx_101_);
lean_dec(v___x_99_);
v_lctx_102_ = lean_ctor_get(v___y_90_, 2);
v_options_103_ = lean_ctor_get(v_toCold_100_, 2);
lean_inc_ref(v_options_103_);
lean_inc_ref(v_lctx_102_);
v___x_104_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_104_, 0, v_env_98_);
lean_ctor_set(v___x_104_, 1, v_mctx_101_);
lean_ctor_set(v___x_104_, 2, v_lctx_102_);
lean_ctor_set(v___x_104_, 3, v_options_103_);
v___x_105_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v_msgData_89_);
v___x_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_89_ = stack[0].m_obj;
lean_object* v___y_90_ = stack[1].m_obj;
lean_object* v___y_91_ = stack[2].m_obj;
lean_object* v___y_92_ = stack[3].m_obj;
lean_object* v___y_93_ = stack[4].m_obj;
lean_object* v_res_107_;
v_res_107_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msgData_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
stack->m_obj
 = v_res_107_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0___boxed(lean_object* v_msgData_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msgData_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
return v_res_114_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(lean_object* v_msg_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_ref_121_; lean_object* v___x_122_; lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_131_; 
v_ref_121_ = lean_ctor_get(v___y_118_, 2);
v___x_122_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msg_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_131_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
lean_inc(v_ref_121_);
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v_ref_121_);
lean_ctor_set(v___x_127_, 1, v_a_123_);
if (v_isShared_126_ == 0)
{
lean_ctor_set_tag(v___x_125_, 1);
lean_ctor_set(v___x_125_, 0, v___x_127_);
v___x_129_ = v___x_125_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_115_ = stack[0].m_obj;
lean_object* v___y_116_ = stack[1].m_obj;
lean_object* v___y_117_ = stack[2].m_obj;
lean_object* v___y_118_ = stack[3].m_obj;
lean_object* v___y_119_ = stack[4].m_obj;
lean_object* v_res_132_;
v_res_132_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v_msg_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
stack->m_obj
 = v_res_132_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg___boxed(lean_object* v_msg_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v_msg_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
return v_res_139_;
}
}
static lean_object* _init_l_Lean_Elab_WF_withAppN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = ((lean_object*)(l_Lean_Elab_WF_withAppN___lam__0___closed__0));
v___x_142_ = l_Lean_stringToMessageData(v___x_141_);
return v___x_142_;
}
}
lean_object* l_Lean_Elab_WF_withAppN___lam__0(lean_object* v_args_143_, lean_object* v_k_144_, uint8_t v___x_145_, lean_object* v_missing_146_, lean_object* v_xs_147_, lean_object* v_x_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = lean_array_get_size(v_xs_147_);
v___x_162_ = lean_nat_dec_lt(v___x_161_, v_missing_146_);
if (v___x_162_ == 0)
{
goto v___jp_154_;
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
lean_dec_ref(v_k_144_);
lean_dec_ref(v_args_143_);
v___x_163_ = lean_obj_once(&l_Lean_Elab_WF_withAppN___lam__0___closed__1, &l_Lean_Elab_WF_withAppN___lam__0___closed__1_once, _init_l_Lean_Elab_WF_withAppN___lam__0___closed__1);
v___x_164_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v___x_163_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
v_a_165_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_164_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_164_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
v___jp_154_:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = l_Array_append___redArg(v_args_143_, v_xs_147_);
lean_inc(v___y_152_);
lean_inc_ref(v___y_151_);
lean_inc(v___y_150_);
lean_inc_ref(v___y_149_);
v___x_156_ = lean_apply_6(v_k_144_, v___x_155_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, lean_box(0));
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; uint8_t v___x_158_; uint8_t v___x_159_; lean_object* v___x_160_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_a_157_);
lean_dec_ref_known(v___x_156_, 1);
v___x_158_ = 1;
v___x_159_ = 1;
v___x_160_ = l_Lean_Meta_mkLambdaFVars(v_xs_147_, v_a_157_, v___x_145_, v___x_158_, v___x_145_, v___x_158_, v___x_159_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
return v___x_160_;
}
else
{
return v___x_156_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_WF_withAppN___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_143_ = stack[0].m_obj;
lean_object* v_k_144_ = stack[1].m_obj;
uint8_t v___x_145_ = stack[2].m_num;
lean_object* v_missing_146_ = stack[3].m_obj;
lean_object* v_xs_147_ = stack[4].m_obj;
lean_object* v_x_148_ = stack[5].m_obj;
lean_object* v___y_149_ = stack[6].m_obj;
lean_object* v___y_150_ = stack[7].m_obj;
lean_object* v___y_151_ = stack[8].m_obj;
lean_object* v___y_152_ = stack[9].m_obj;
lean_object* v_res_173_;
v_res_173_ = l_Lean_Elab_WF_withAppN___lam__0(v_args_143_, v_k_144_, v___x_145_, v_missing_146_, v_xs_147_, v_x_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
stack->m_obj
 = v_res_173_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___lam__0___boxed(lean_object* v_args_174_, lean_object* v_k_175_, lean_object* v___x_176_, lean_object* v_missing_177_, lean_object* v_xs_178_, lean_object* v_x_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
uint8_t v___x_2337__boxed_185_; lean_object* v_res_186_; 
v___x_2337__boxed_185_ = lean_unbox(v___x_176_);
v_res_186_ = l_Lean_Elab_WF_withAppN___lam__0(v_args_174_, v_k_175_, v___x_2337__boxed_185_, v_missing_177_, v_xs_178_, v_x_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec_ref(v_x_179_);
lean_dec_ref(v_xs_178_);
lean_dec(v_missing_177_);
return v_res_186_;
}
}
static lean_object* _init_l_Lean_Elab_WF_withAppN___closed__0(void){
_start:
{
lean_object* v___x_187_; lean_object* v_dummy_188_; 
v___x_187_ = lean_box(0);
v_dummy_188_ = l_Lean_Expr_sort___override(v___x_187_);
return v_dummy_188_;
}
}
lean_object* l_Lean_Elab_WF_withAppN(lean_object* v_n_189_, lean_object* v_e_190_, lean_object* v_k_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_dummy_197_; lean_object* v_nargs_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v_args_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v_dummy_197_ = lean_obj_once(&l_Lean_Elab_WF_withAppN___closed__0, &l_Lean_Elab_WF_withAppN___closed__0_once, _init_l_Lean_Elab_WF_withAppN___closed__0);
v_nargs_198_ = l_Lean_Expr_getAppNumArgs(v_e_190_);
lean_inc(v_nargs_198_);
v___x_199_ = lean_mk_array(v_nargs_198_, v_dummy_197_);
v___x_200_ = lean_unsigned_to_nat(1u);
v___x_201_ = lean_nat_sub(v_nargs_198_, v___x_200_);
lean_dec(v_nargs_198_);
lean_inc_ref(v_e_190_);
v_args_202_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_190_, v___x_199_, v___x_201_);
v___x_203_ = lean_array_get_size(v_args_202_);
v___x_204_ = lean_nat_dec_le(v_n_189_, v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v_missing_205_; lean_object* v___x_206_; lean_object* v___f_207_; lean_object* v___x_208_; 
v_missing_205_ = lean_nat_sub(v_n_189_, v___x_203_);
lean_dec(v_n_189_);
v___x_206_ = lean_box(v___x_204_);
lean_inc(v_missing_205_);
v___f_207_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_withAppN___lam__0___boxed), 11, 4);
lean_closure_set(v___f_207_, 0, v_args_202_);
lean_closure_set(v___f_207_, 1, v_k_191_);
lean_closure_set(v___f_207_, 2, v___x_206_);
lean_closure_set(v___f_207_, 3, v_missing_205_);
lean_inc(v_a_195_);
lean_inc_ref(v_a_194_);
lean_inc(v_a_193_);
lean_inc_ref(v_a_192_);
v___x_208_ = lean_infer_type(v_e_190_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_217_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_217_ == 0)
{
v___x_211_ = v___x_208_;
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_208_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
lean_ctor_set_tag(v___x_211_, 1);
lean_ctor_set(v___x_211_, 0, v_missing_205_);
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_missing_205_);
v___x_214_ = v_reuseFailAlloc_216_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_a_209_, v___x_214_, v___f_207_, v___x_204_, v___x_204_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
return v___x_215_;
}
}
}
else
{
lean_dec_ref(v___f_207_);
lean_dec(v_missing_205_);
return v___x_208_;
}
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec_ref(v_e_190_);
v___x_218_ = lean_unsigned_to_nat(0u);
lean_inc(v_n_189_);
lean_inc_ref(v_args_202_);
v___x_219_ = l_Array_toSubarray___redArg(v_args_202_, v___x_218_, v_n_189_);
v___x_220_ = l_Subarray_copy___redArg(v___x_219_);
lean_inc(v_a_195_);
lean_inc_ref(v_a_194_);
lean_inc(v_a_193_);
lean_inc_ref(v_a_192_);
v___x_221_ = lean_apply_6(v_k_191_, v___x_220_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, lean_box(0));
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_236_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_236_ == 0)
{
v___x_224_ = v___x_221_;
v_isShared_225_ = v_isSharedCheck_236_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_221_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_236_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v_lower_227_; lean_object* v_upper_228_; uint8_t v___x_235_; 
v___x_235_ = lean_nat_dec_le(v_n_189_, v___x_218_);
if (v___x_235_ == 0)
{
v_lower_227_ = v_n_189_;
v_upper_228_ = v___x_203_;
goto v___jp_226_;
}
else
{
lean_dec(v_n_189_);
v_lower_227_ = v___x_218_;
v_upper_228_ = v___x_203_;
goto v___jp_226_;
}
v___jp_226_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_229_ = l_Array_toSubarray___redArg(v_args_202_, v_lower_227_, v_upper_228_);
v___x_230_ = l_Subarray_copy___redArg(v___x_229_);
v___x_231_ = l_Lean_mkAppN(v_a_222_, v___x_230_);
lean_dec_ref(v___x_230_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_231_);
v___x_233_ = v___x_224_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
else
{
lean_dec_ref(v_args_202_);
lean_dec(v_n_189_);
return v___x_221_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_WF_withAppN_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_189_ = stack[0].m_obj;
lean_object* v_e_190_ = stack[1].m_obj;
lean_object* v_k_191_ = stack[2].m_obj;
lean_object* v_a_192_ = stack[3].m_obj;
lean_object* v_a_193_ = stack[4].m_obj;
lean_object* v_a_194_ = stack[5].m_obj;
lean_object* v_a_195_ = stack[6].m_obj;
lean_object* v_res_237_;
v_res_237_ = l_Lean_Elab_WF_withAppN(v_n_189_, v_e_190_, v_k_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
stack->m_obj
 = v_res_237_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___boxed(lean_object* v_n_238_, lean_object* v_e_239_, lean_object* v_k_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Elab_WF_withAppN(v_n_238_, v_e_239_, v_k_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
return v_res_246_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0(lean_object* v_00_u03b1_247_, lean_object* v_msg_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v_msg_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
return v___x_254_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_248_ = stack[1].m_obj;
lean_object* v___y_249_ = stack[2].m_obj;
lean_object* v___y_250_ = stack[3].m_obj;
lean_object* v___y_251_ = stack[4].m_obj;
lean_object* v___y_252_ = stack[5].m_obj;
lean_object* v_res_255_;
v_res_255_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0(lean_box(0), v_msg_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
stack->m_obj
 = v_res_255_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___boxed(lean_object* v_00_u03b1_256_, lean_object* v_msg_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0(v_00_u03b1_256_, v_msg_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
return v_res_263_;
}
}
lean_object* l_panic___at___00Lean_Elab_WF_packCalls_spec__1(lean_object* v_msg_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v___f_271_; lean_object* v___x_1209__overap_272_; lean_object* v___x_273_; 
v___f_271_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1209__overap_272_ = lean_panic_fn_borrowed(v___f_271_, v_msg_265_);
lean_inc(v___y_269_);
lean_inc_ref(v___y_268_);
lean_inc(v___y_267_);
lean_inc_ref(v___y_266_);
v___x_273_ = lean_apply_5(v___x_1209__overap_272_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, lean_box(0));
return v___x_273_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_WF_packCalls_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_265_ = stack[0].m_obj;
lean_object* v___y_266_ = stack[1].m_obj;
lean_object* v___y_267_ = stack[2].m_obj;
lean_object* v___y_268_ = stack[3].m_obj;
lean_object* v___y_269_ = stack[4].m_obj;
lean_object* v_res_274_;
v_res_274_ = l_panic___at___00Lean_Elab_WF_packCalls_spec__1(v_msg_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
stack->m_obj
 = v_res_274_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_packCalls_spec__1___boxed(lean_object* v_msg_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_panic___at___00Lean_Elab_WF_packCalls_spec__1(v_msg_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
return v_res_281_;
}
}
lean_object* l_Lean_Elab_WF_packCalls___lam__0(lean_object* v_x_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__0___closed__0));
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT void l_Lean_Elab_WF_packCalls___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_284_ = stack[0].m_obj;
lean_object* v___y_285_ = stack[1].m_obj;
lean_object* v___y_286_ = stack[2].m_obj;
lean_object* v___y_287_ = stack[3].m_obj;
lean_object* v___y_288_ = stack[4].m_obj;
lean_object* v_res_292_;
v_res_292_ = l_Lean_Elab_WF_packCalls___lam__0(v_x_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
stack->m_obj
 = v_res_292_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__0___boxed(lean_object* v_x_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Elab_WF_packCalls___lam__0(v_x_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec_ref(v_x_293_);
return v_res_299_;
}
}
lean_object* l_Lean_Elab_WF_packCalls___lam__1(lean_object* v___x_300_, lean_object* v_argsPacker_301_, lean_object* v___x_302_, lean_object* v_val_303_, lean_object* v_newF_304_, lean_object* v_args_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_300_, v_args_305_);
v___x_312_ = l_Lean_Meta_ArgsPacker_pack(v_argsPacker_301_, v___x_302_, v_val_303_, v___x_311_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec_ref(v___x_311_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_321_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_321_ == 0)
{
v___x_315_ = v___x_312_;
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_312_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_317_ = l_Lean_Expr_app___override(v_newF_304_, v_a_313_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_317_);
v___x_319_ = v___x_315_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
else
{
lean_dec_ref(v_newF_304_);
return v___x_312_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_WF_packCalls___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_300_ = stack[0].m_obj;
lean_object* v_argsPacker_301_ = stack[1].m_obj;
lean_object* v___x_302_ = stack[2].m_obj;
lean_object* v_val_303_ = stack[3].m_obj;
lean_object* v_newF_304_ = stack[4].m_obj;
lean_object* v_args_305_ = stack[5].m_obj;
lean_object* v___y_306_ = stack[6].m_obj;
lean_object* v___y_307_ = stack[7].m_obj;
lean_object* v___y_308_ = stack[8].m_obj;
lean_object* v___y_309_ = stack[9].m_obj;
lean_object* v_res_322_;
v_res_322_ = l_Lean_Elab_WF_packCalls___lam__1(v___x_300_, v_argsPacker_301_, v___x_302_, v_val_303_, v_newF_304_, v_args_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
stack->m_obj
 = v_res_322_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__1___boxed(lean_object* v___x_323_, lean_object* v_argsPacker_324_, lean_object* v___x_325_, lean_object* v_val_326_, lean_object* v_newF_327_, lean_object* v_args_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Elab_WF_packCalls___lam__1(v___x_323_, v_argsPacker_324_, v___x_325_, v_val_326_, v_newF_327_, v_args_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec_ref(v_args_328_);
lean_dec_ref(v_argsPacker_324_);
lean_dec_ref(v___x_323_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2(lean_object* v_xs_335_, lean_object* v_v_336_, lean_object* v_i_337_){
_start:
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = lean_array_get_size(v_xs_335_);
v___x_339_ = lean_nat_dec_lt(v_i_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; 
lean_dec(v_i_337_);
v___x_340_ = lean_box(0);
return v___x_340_;
}
else
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = lean_array_fget_borrowed(v_xs_335_, v_i_337_);
v___x_342_ = lean_name_eq(v___x_341_, v_v_336_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(1u);
v___x_344_ = lean_nat_add(v_i_337_, v___x_343_);
lean_dec(v_i_337_);
v_i_337_ = v___x_344_;
goto _start;
}
else
{
lean_object* v___x_346_; 
v___x_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_346_, 0, v_i_337_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2___boxed(lean_object* v_xs_347_, lean_object* v_v_348_, lean_object* v_i_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2(v_xs_347_, v_v_348_, v_i_349_);
lean_dec(v_v_348_);
lean_dec_ref(v_xs_347_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0(lean_object* v_xs_351_, lean_object* v_v_352_){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2(v_xs_351_, v_v_352_, v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0___boxed(lean_object* v_xs_355_, lean_object* v_v_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0(v_xs_355_, v_v_356_);
lean_dec(v_v_356_);
lean_dec_ref(v_xs_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(lean_object* v_xs_358_, lean_object* v_v_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0(v_xs_358_, v_v_359_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v___x_361_; 
v___x_361_ = lean_box(0);
return v___x_361_;
}
else
{
lean_object* v_val_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
v_val_362_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_360_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_val_362_);
lean_dec(v___x_360_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_val_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0___boxed(lean_object* v_xs_370_, lean_object* v_v_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(v_xs_370_, v_v_371_);
lean_dec(v_v_371_);
lean_dec_ref(v_xs_370_);
return v_res_372_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(lean_object* v_val_373_, lean_object* v___x_374_, size_t v_sz_375_, size_t v_i_376_, lean_object* v_bs_377_){
_start:
{
uint8_t v___x_378_; 
v___x_378_ = lean_usize_dec_lt(v_i_376_, v_sz_375_);
if (v___x_378_ == 0)
{
return v_bs_377_;
}
else
{
lean_object* v_v_379_; lean_object* v___x_380_; lean_object* v_bs_x27_381_; uint8_t v___y_383_; 
v_v_379_ = lean_array_uget(v_bs_377_, v_i_376_);
v___x_380_ = lean_unsigned_to_nat(0u);
v_bs_x27_381_ = lean_array_uset(v_bs_377_, v_i_376_, v___x_380_);
if (lean_obj_tag(v_v_379_) == 0)
{
uint8_t v___x_389_; 
v___x_389_ = 0;
v___y_383_ = v___x_389_;
goto v___jp_382_;
}
else
{
uint8_t v___x_390_; 
lean_dec_ref_known(v_v_379_, 1);
v___x_390_ = lean_nat_dec_lt(v_val_373_, v___x_374_);
v___y_383_ = v___x_390_;
goto v___jp_382_;
}
v___jp_382_:
{
size_t v___x_384_; size_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_384_ = ((size_t)1ULL);
v___x_385_ = lean_usize_add(v_i_376_, v___x_384_);
v___x_386_ = lean_box(v___y_383_);
v___x_387_ = lean_array_uset(v_bs_x27_381_, v_i_376_, v___x_386_);
v_i_376_ = v___x_385_;
v_bs_377_ = v___x_387_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_373_ = stack[0].m_obj;
lean_object* v___x_374_ = stack[1].m_obj;
size_t v_sz_375_ = stack[2].m_num;
size_t v_i_376_ = stack[3].m_num;
lean_object* v_bs_377_ = stack[4].m_obj;
lean_object* v_res_391_;
v_res_391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(v_val_373_, v___x_374_, v_sz_375_, v_i_376_, v_bs_377_);
stack->m_obj
 = v_res_391_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2___boxed(lean_object* v_val_392_, lean_object* v___x_393_, lean_object* v_sz_394_, lean_object* v_i_395_, lean_object* v_bs_396_){
_start:
{
size_t v_sz_boxed_397_; size_t v_i_boxed_398_; lean_object* v_res_399_; 
v_sz_boxed_397_ = lean_unbox_usize(v_sz_394_);
lean_dec(v_sz_394_);
v_i_boxed_398_ = lean_unbox_usize(v_i_395_);
lean_dec(v_i_395_);
v_res_399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(v_val_392_, v___x_393_, v_sz_boxed_397_, v_i_boxed_398_, v_bs_396_);
lean_dec(v___x_393_);
lean_dec(v_val_392_);
return v_res_399_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___lam__2___closed__3(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_403_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__2));
v___x_404_ = lean_unsigned_to_nat(6u);
v___x_405_ = lean_unsigned_to_nat(55u);
v___x_406_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__1));
v___x_407_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_408_ = l_mkPanicMessageWithDecl(v___x_407_, v___x_406_, v___x_405_, v___x_404_, v___x_403_);
return v___x_408_;
}
}
lean_object* l_Lean_Elab_WF_packCalls___lam__2(lean_object* v_funNames_409_, lean_object* v_fixedParamPerms_410_, lean_object* v___x_411_, lean_object* v_argsPacker_412_, lean_object* v___x_413_, lean_object* v_newF_414_, lean_object* v_e_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_421_ = l_Lean_Expr_getAppFn(v_e_415_);
v___x_422_ = l_Lean_Expr_isConst(v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec_ref(v___x_421_);
lean_dec_ref(v_newF_414_);
lean_dec_ref(v___x_413_);
lean_dec_ref(v_argsPacker_412_);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v_e_415_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = l_Lean_Expr_constName_x21(v___x_421_);
lean_dec_ref(v___x_421_);
v___x_426_ = l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(v_funNames_409_, v___x_425_);
lean_dec(v___x_425_);
if (lean_obj_tag(v___x_426_) == 1)
{
lean_object* v_val_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_462_; 
v_val_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_462_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_462_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_val_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_462_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v_perms_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v_perms_431_ = lean_ctor_get(v_fixedParamPerms_410_, 1);
v___x_432_ = lean_array_get_size(v_perms_431_);
v___x_433_ = lean_nat_dec_lt(v_val_427_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; 
lean_del_object(v___x_429_);
lean_dec(v_val_427_);
lean_dec_ref(v_e_415_);
lean_dec_ref(v_newF_414_);
lean_dec_ref(v___x_413_);
lean_dec_ref(v_argsPacker_412_);
v___x_434_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__3, &l_Lean_Elab_WF_packCalls___lam__2___closed__3_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__3);
v___x_435_ = l_panic___at___00Lean_Elab_WF_packCalls_spec__1(v___x_434_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
return v___x_435_;
}
else
{
lean_object* v___x_436_; lean_object* v___f_437_; size_t v_sz_438_; size_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_436_ = lean_array_get_borrowed(v___x_411_, v_perms_431_, v_val_427_);
lean_inc(v_val_427_);
lean_inc_n(v___x_436_, 2);
v___f_437_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packCalls___lam__1___boxed), 11, 5);
lean_closure_set(v___f_437_, 0, v___x_436_);
lean_closure_set(v___f_437_, 1, v_argsPacker_412_);
lean_closure_set(v___f_437_, 2, v___x_413_);
lean_closure_set(v___f_437_, 3, v_val_427_);
lean_closure_set(v___f_437_, 4, v_newF_414_);
v_sz_438_ = lean_array_size(v___x_436_);
v___x_439_ = ((size_t)0ULL);
v___x_440_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(v_val_427_, v___x_432_, v_sz_438_, v___x_439_, v___x_436_);
lean_dec(v_val_427_);
v___x_441_ = lean_array_get_size(v___x_440_);
lean_dec_ref(v___x_440_);
v___x_442_ = l_Lean_Elab_WF_withAppN(v___x_441_, v_e_415_, v___f_437_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_453_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_453_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_453_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_453_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set_tag(v___x_429_, 0);
lean_ctor_set(v___x_429_, 0, v_a_443_);
v___x_448_ = v___x_429_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_452_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_450_; 
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_448_);
v___x_450_ = v___x_445_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
else
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
lean_del_object(v___x_429_);
v_a_454_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_442_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_442_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec(v___x_426_);
lean_dec_ref(v_newF_414_);
lean_dec_ref(v___x_413_);
lean_dec_ref(v_argsPacker_412_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v_e_415_);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_WF_packCalls___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_funNames_409_ = stack[0].m_obj;
lean_object* v_fixedParamPerms_410_ = stack[1].m_obj;
lean_object* v___x_411_ = stack[2].m_obj;
lean_object* v_argsPacker_412_ = stack[3].m_obj;
lean_object* v___x_413_ = stack[4].m_obj;
lean_object* v_newF_414_ = stack[5].m_obj;
lean_object* v_e_415_ = stack[6].m_obj;
lean_object* v___y_416_ = stack[7].m_obj;
lean_object* v___y_417_ = stack[8].m_obj;
lean_object* v___y_418_ = stack[9].m_obj;
lean_object* v___y_419_ = stack[10].m_obj;
lean_object* v_res_465_;
v_res_465_ = l_Lean_Elab_WF_packCalls___lam__2(v_funNames_409_, v_fixedParamPerms_410_, v___x_411_, v_argsPacker_412_, v___x_413_, v_newF_414_, v_e_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
stack->m_obj
 = v_res_465_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__2___boxed(lean_object* v_funNames_466_, lean_object* v_fixedParamPerms_467_, lean_object* v___x_468_, lean_object* v_argsPacker_469_, lean_object* v___x_470_, lean_object* v_newF_471_, lean_object* v_e_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_Elab_WF_packCalls___lam__2(v_funNames_466_, v_fixedParamPerms_467_, v___x_468_, v_argsPacker_469_, v___x_470_, v_newF_471_, v_e_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec_ref(v___x_468_);
lean_dec_ref(v_fixedParamPerms_467_);
lean_dec_ref(v_funNames_466_);
return v_res_478_;
}
}
lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_object* v_00_u03b1_479_, lean_object* v_x_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_apply_1(v_x_480_, lean_box(0));
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT void l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_480_ = stack[1].m_obj;
lean_object* v___y_481_ = stack[2].m_obj;
lean_object* v___y_482_ = stack[3].m_obj;
lean_object* v___y_483_ = stack[4].m_obj;
lean_object* v___y_484_ = stack[5].m_obj;
lean_object* v_res_488_;
v_res_488_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v_x_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
stack->m_obj
 = v_res_488_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0___boxed(lean_object* v_00_u03b1_489_, lean_object* v_x_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(v_00_u03b1_489_, v_x_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
return v_res_496_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = l_Lean_maxRecDepthErrorMessage;
v___x_503_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3);
v___x_505_ = l_Lean_MessageData_ofFormat(v___x_504_);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4);
v___x_507_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2));
v___x_508_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
lean_ctor_set(v___x_508_, 1, v___x_506_);
return v___x_508_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(lean_object* v_ref_509_){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_511_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v_ref_509_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_509_ = stack[0].m_obj;
lean_object* v_res_514_;
v_res_514_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_509_);
stack->m_obj
 = v_res_514_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___boxed(lean_object* v_ref_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_515_);
return v_res_517_;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(lean_object* v_x_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___y_526_; lean_object* v_toCold_535_; lean_object* v_currRecDepth_536_; lean_object* v_ref_537_; uint16_t v_optionFlags_538_; uint8_t v_suppressElabErrors_539_; uint8_t v_isRecordingDeps_540_; lean_object* v_maxRecDepth_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v_toCold_535_ = lean_ctor_get(v___y_522_, 0);
v_currRecDepth_536_ = lean_ctor_get(v___y_522_, 1);
v_ref_537_ = lean_ctor_get(v___y_522_, 2);
v_optionFlags_538_ = lean_ctor_get_uint16(v___y_522_, sizeof(void*)*3);
v_suppressElabErrors_539_ = lean_ctor_get_uint8(v___y_522_, sizeof(void*)*3 + 2);
v_isRecordingDeps_540_ = lean_ctor_get_uint8(v___y_522_, sizeof(void*)*3 + 3);
v_maxRecDepth_546_ = lean_ctor_get(v_toCold_535_, 3);
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_nat_dec_eq(v_maxRecDepth_546_, v___x_547_);
if (v___x_548_ == 0)
{
uint8_t v___x_549_; 
v___x_549_ = lean_nat_dec_eq(v_currRecDepth_536_, v_maxRecDepth_546_);
if (v___x_549_ == 0)
{
goto v___jp_541_;
}
else
{
lean_object* v___x_550_; 
lean_dec_ref(v_x_518_);
lean_inc(v_ref_537_);
v___x_550_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_537_);
v___y_526_ = v___x_550_;
goto v___jp_525_;
}
}
else
{
goto v___jp_541_;
}
v___jp_525_:
{
if (lean_obj_tag(v___y_526_) == 0)
{
return v___y_526_;
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
v_a_527_ = lean_ctor_get(v___y_526_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___y_526_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___y_526_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___y_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
v___jp_541_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_add(v_currRecDepth_536_, v___x_542_);
lean_inc(v_ref_537_);
lean_inc_ref(v_toCold_535_);
v___x_544_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_544_, 0, v_toCold_535_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
lean_ctor_set(v___x_544_, 2, v_ref_537_);
lean_ctor_set_uint16(v___x_544_, sizeof(void*)*3, v_optionFlags_538_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*3 + 2, v_suppressElabErrors_539_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*3 + 3, v_isRecordingDeps_540_);
lean_inc(v___y_523_);
lean_inc(v___y_521_);
lean_inc_ref(v___y_520_);
lean_inc(v___y_519_);
v___x_545_ = lean_apply_6(v_x_518_, v___y_519_, v___y_520_, v___y_521_, v___x_544_, v___y_523_, lean_box(0));
v___y_526_ = v___x_545_;
goto v___jp_525_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_518_ = stack[0].m_obj;
lean_object* v___y_519_ = stack[1].m_obj;
lean_object* v___y_520_ = stack[2].m_obj;
lean_object* v___y_521_ = stack[3].m_obj;
lean_object* v___y_522_ = stack[4].m_obj;
lean_object* v___y_523_ = stack[5].m_obj;
lean_object* v_res_551_;
v_res_551_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
stack->m_obj
 = v_res_551_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg___boxed(lean_object* v_x_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
return v_res_559_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(lean_object* v___x_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_560_);
return v___x_566_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_560_ = stack[0].m_obj;
lean_object* v___y_561_ = stack[1].m_obj;
lean_object* v___y_562_ = stack[2].m_obj;
lean_object* v___y_563_ = stack[3].m_obj;
lean_object* v___y_564_ = stack[4].m_obj;
lean_object* v_res_567_;
v_res_567_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(v___x_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
stack->m_obj
 = v_res_567_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2___boxed(lean_object* v___x_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(v___x_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
return v_res_574_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(lean_object* v_k_575_, lean_object* v___y_576_, lean_object* v_b_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; 
lean_inc(v___y_581_);
lean_inc_ref(v___y_580_);
lean_inc(v___y_579_);
lean_inc_ref(v___y_578_);
lean_inc(v___y_576_);
v___x_583_ = lean_apply_7(v_k_575_, v_b_577_, v___y_576_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, lean_box(0));
return v___x_583_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_575_ = stack[0].m_obj;
lean_object* v___y_576_ = stack[1].m_obj;
lean_object* v_b_577_ = stack[2].m_obj;
lean_object* v___y_578_ = stack[3].m_obj;
lean_object* v___y_579_ = stack[4].m_obj;
lean_object* v___y_580_ = stack[5].m_obj;
lean_object* v___y_581_ = stack[6].m_obj;
lean_object* v_res_584_;
v_res_584_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(v_k_575_, v___y_576_, v_b_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
stack->m_obj
 = v_res_584_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed(lean_object* v_k_585_, lean_object* v___y_586_, lean_object* v_b_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(v_k_585_, v___y_586_, v_b_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_586_);
return v_res_593_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(lean_object* v_name_594_, lean_object* v_type_595_, lean_object* v_val_596_, lean_object* v_k_597_, uint8_t v_nondep_598_, uint8_t v_kind_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v___f_606_; lean_object* v___x_607_; 
lean_inc(v___y_600_);
v___f_606_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_606_, 0, v_k_597_);
lean_closure_set(v___f_606_, 1, v___y_600_);
v___x_607_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_594_, v_type_595_, v_val_596_, v___f_606_, v_nondep_598_, v_kind_599_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_607_) == 0)
{
return v___x_607_;
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
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
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_594_ = stack[0].m_obj;
lean_object* v_type_595_ = stack[1].m_obj;
lean_object* v_val_596_ = stack[2].m_obj;
lean_object* v_k_597_ = stack[3].m_obj;
uint8_t v_nondep_598_ = stack[4].m_num;
uint8_t v_kind_599_ = stack[5].m_num;
lean_object* v___y_600_ = stack[6].m_obj;
lean_object* v___y_601_ = stack[7].m_obj;
lean_object* v___y_602_ = stack[8].m_obj;
lean_object* v___y_603_ = stack[9].m_obj;
lean_object* v___y_604_ = stack[10].m_obj;
lean_object* v_res_616_;
v_res_616_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_594_, v_type_595_, v_val_596_, v_k_597_, v_nondep_598_, v_kind_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
stack->m_obj
 = v_res_616_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg___boxed(lean_object* v_name_617_, lean_object* v_type_618_, lean_object* v_val_619_, lean_object* v_k_620_, lean_object* v_nondep_621_, lean_object* v_kind_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
uint8_t v_nondep_boxed_629_; uint8_t v_kind_boxed_630_; lean_object* v_res_631_; 
v_nondep_boxed_629_ = lean_unbox(v_nondep_621_);
v_kind_boxed_630_ = lean_unbox(v_kind_622_);
v_res_631_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_617_, v_type_618_, v_val_619_, v_k_620_, v_nondep_boxed_629_, v_kind_boxed_630_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
return v_res_631_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(lean_object* v_name_632_, uint8_t v_bi_633_, lean_object* v_type_634_, lean_object* v_k_635_, uint8_t v_kind_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v___f_643_; lean_object* v___x_644_; 
lean_inc(v___y_637_);
v___f_643_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_643_, 0, v_k_635_);
lean_closure_set(v___f_643_, 1, v___y_637_);
v___x_644_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_632_, v_bi_633_, v_type_634_, v___f_643_, v_kind_636_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_644_) == 0)
{
return v___x_644_;
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_644_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_632_ = stack[0].m_obj;
uint8_t v_bi_633_ = stack[1].m_num;
lean_object* v_type_634_ = stack[2].m_obj;
lean_object* v_k_635_ = stack[3].m_obj;
uint8_t v_kind_636_ = stack[4].m_num;
lean_object* v___y_637_ = stack[5].m_obj;
lean_object* v___y_638_ = stack[6].m_obj;
lean_object* v___y_639_ = stack[7].m_obj;
lean_object* v___y_640_ = stack[8].m_obj;
lean_object* v___y_641_ = stack[9].m_obj;
lean_object* v_res_653_;
v_res_653_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_632_, v_bi_633_, v_type_634_, v_k_635_, v_kind_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
stack->m_obj
 = v_res_653_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___boxed(lean_object* v_name_654_, lean_object* v_bi_655_, lean_object* v_type_656_, lean_object* v_k_657_, lean_object* v_kind_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
uint8_t v_bi_boxed_665_; uint8_t v_kind_boxed_666_; lean_object* v_res_667_; 
v_bi_boxed_665_ = lean_unbox(v_bi_655_);
v_kind_boxed_666_ = lean_unbox(v_kind_658_);
v_res_667_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_654_, v_bi_boxed_665_, v_type_656_, v_k_657_, v_kind_boxed_666_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
return v_res_667_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_object* v_00_u03b1_668_, lean_object* v_x_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_apply_1(v_x_669_, lean_box(0));
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_669_ = stack[1].m_obj;
lean_object* v___y_670_ = stack[2].m_obj;
lean_object* v___y_671_ = stack[3].m_obj;
lean_object* v___y_672_ = stack[4].m_obj;
lean_object* v___y_673_ = stack[5].m_obj;
lean_object* v_res_677_;
v_res_677_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v_x_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
stack->m_obj
 = v_res_677_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0___boxed(lean_object* v_00_u03b1_678_, lean_object* v_x_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(v_00_u03b1_678_, v_x_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(lean_object* v_a_686_, lean_object* v_x_687_){
_start:
{
if (lean_obj_tag(v_x_687_) == 0)
{
lean_object* v___x_688_; 
v___x_688_ = lean_box(0);
return v___x_688_;
}
else
{
lean_object* v_key_689_; lean_object* v_value_690_; lean_object* v_tail_691_; uint8_t v___x_692_; 
v_key_689_ = lean_ctor_get(v_x_687_, 0);
v_value_690_ = lean_ctor_get(v_x_687_, 1);
v_tail_691_ = lean_ctor_get(v_x_687_, 2);
v___x_692_ = l_Lean_ExprStructEq_beq(v_key_689_, v_a_686_);
if (v___x_692_ == 0)
{
v_x_687_ = v_tail_691_;
goto _start;
}
else
{
lean_object* v___x_694_; 
lean_inc(v_value_690_);
v___x_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_694_, 0, v_value_690_);
return v___x_694_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg___boxed(lean_object* v_a_695_, lean_object* v_x_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_695_, v_x_696_);
lean_dec(v_x_696_);
lean_dec_ref(v_a_695_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(lean_object* v_m_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_buckets_700_; lean_object* v___x_701_; uint64_t v___x_702_; uint64_t v___x_703_; uint64_t v___x_704_; uint64_t v_fold_705_; uint64_t v___x_706_; uint64_t v___x_707_; uint64_t v___x_708_; size_t v___x_709_; size_t v___x_710_; size_t v___x_711_; size_t v___x_712_; size_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v_buckets_700_ = lean_ctor_get(v_m_698_, 1);
v___x_701_ = lean_array_get_size(v_buckets_700_);
v___x_702_ = l_Lean_ExprStructEq_hash(v_a_699_);
v___x_703_ = 32ULL;
v___x_704_ = lean_uint64_shift_right(v___x_702_, v___x_703_);
v_fold_705_ = lean_uint64_xor(v___x_702_, v___x_704_);
v___x_706_ = 16ULL;
v___x_707_ = lean_uint64_shift_right(v_fold_705_, v___x_706_);
v___x_708_ = lean_uint64_xor(v_fold_705_, v___x_707_);
v___x_709_ = lean_uint64_to_usize(v___x_708_);
v___x_710_ = lean_usize_of_nat(v___x_701_);
v___x_711_ = ((size_t)1ULL);
v___x_712_ = lean_usize_sub(v___x_710_, v___x_711_);
v___x_713_ = lean_usize_land(v___x_709_, v___x_712_);
v___x_714_ = lean_array_uget_borrowed(v_buckets_700_, v___x_713_);
v___x_715_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_699_, v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___boxed(lean_object* v_m_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_m_716_, v_a_717_);
lean_dec_ref(v_a_717_);
lean_dec_ref(v_m_716_);
return v_res_718_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(lean_object* v_a_719_, lean_object* v_x_720_){
_start:
{
if (lean_obj_tag(v_x_720_) == 0)
{
uint8_t v___x_721_; 
v___x_721_ = 0;
return v___x_721_;
}
else
{
lean_object* v_key_722_; lean_object* v_tail_723_; uint8_t v___x_724_; 
v_key_722_ = lean_ctor_get(v_x_720_, 0);
v_tail_723_ = lean_ctor_get(v_x_720_, 2);
v___x_724_ = l_Lean_ExprStructEq_beq(v_key_722_, v_a_719_);
if (v___x_724_ == 0)
{
v_x_720_ = v_tail_723_;
goto _start;
}
else
{
return v___x_724_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_719_ = stack[0].m_obj;
lean_object* v_x_720_ = stack[1].m_obj;
uint8_t v_res_726_;
v_res_726_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_719_, v_x_720_);
stack->m_num = v_res_726_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg___boxed(lean_object* v_a_727_, lean_object* v_x_728_){
_start:
{
uint8_t v_res_729_; lean_object* v_r_730_; 
v_res_729_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_727_, v_x_728_);
lean_dec(v_x_728_);
lean_dec_ref(v_a_727_);
v_r_730_ = lean_box(v_res_729_);
return v_r_730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(lean_object* v_x_731_, lean_object* v_x_732_){
_start:
{
if (lean_obj_tag(v_x_732_) == 0)
{
return v_x_731_;
}
else
{
lean_object* v_key_733_; lean_object* v_value_734_; lean_object* v_tail_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_758_; 
v_key_733_ = lean_ctor_get(v_x_732_, 0);
v_value_734_ = lean_ctor_get(v_x_732_, 1);
v_tail_735_ = lean_ctor_get(v_x_732_, 2);
v_isSharedCheck_758_ = !lean_is_exclusive(v_x_732_);
if (v_isSharedCheck_758_ == 0)
{
v___x_737_ = v_x_732_;
v_isShared_738_ = v_isSharedCheck_758_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_tail_735_);
lean_inc(v_value_734_);
lean_inc(v_key_733_);
lean_dec(v_x_732_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_758_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; uint64_t v___x_740_; uint64_t v___x_741_; uint64_t v___x_742_; uint64_t v_fold_743_; uint64_t v___x_744_; uint64_t v___x_745_; uint64_t v___x_746_; size_t v___x_747_; size_t v___x_748_; size_t v___x_749_; size_t v___x_750_; size_t v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_739_ = lean_array_get_size(v_x_731_);
v___x_740_ = l_Lean_ExprStructEq_hash(v_key_733_);
v___x_741_ = 32ULL;
v___x_742_ = lean_uint64_shift_right(v___x_740_, v___x_741_);
v_fold_743_ = lean_uint64_xor(v___x_740_, v___x_742_);
v___x_744_ = 16ULL;
v___x_745_ = lean_uint64_shift_right(v_fold_743_, v___x_744_);
v___x_746_ = lean_uint64_xor(v_fold_743_, v___x_745_);
v___x_747_ = lean_uint64_to_usize(v___x_746_);
v___x_748_ = lean_usize_of_nat(v___x_739_);
v___x_749_ = ((size_t)1ULL);
v___x_750_ = lean_usize_sub(v___x_748_, v___x_749_);
v___x_751_ = lean_usize_land(v___x_747_, v___x_750_);
v___x_752_ = lean_array_uget_borrowed(v_x_731_, v___x_751_);
lean_inc(v___x_752_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 2, v___x_752_);
v___x_754_ = v___x_737_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_key_733_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_value_734_);
lean_ctor_set(v_reuseFailAlloc_757_, 2, v___x_752_);
v___x_754_ = v_reuseFailAlloc_757_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; 
v___x_755_ = lean_array_uset(v_x_731_, v___x_751_, v___x_754_);
v_x_731_ = v___x_755_;
v_x_732_ = v_tail_735_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(lean_object* v_i_759_, lean_object* v_source_760_, lean_object* v_target_761_){
_start:
{
lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_762_ = lean_array_get_size(v_source_760_);
v___x_763_ = lean_nat_dec_lt(v_i_759_, v___x_762_);
if (v___x_763_ == 0)
{
lean_dec_ref(v_source_760_);
lean_dec(v_i_759_);
return v_target_761_;
}
else
{
lean_object* v_es_764_; lean_object* v___x_765_; lean_object* v_source_766_; lean_object* v_target_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v_es_764_ = lean_array_fget(v_source_760_, v_i_759_);
v___x_765_ = lean_box(0);
v_source_766_ = lean_array_fset(v_source_760_, v_i_759_, v___x_765_);
v_target_767_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(v_target_761_, v_es_764_);
v___x_768_ = lean_unsigned_to_nat(1u);
v___x_769_ = lean_nat_add(v_i_759_, v___x_768_);
lean_dec(v_i_759_);
v_i_759_ = v___x_769_;
v_source_760_ = v_source_766_;
v_target_761_ = v_target_767_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(lean_object* v_data_771_){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v_nbuckets_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_772_ = lean_array_get_size(v_data_771_);
v___x_773_ = lean_unsigned_to_nat(2u);
v_nbuckets_774_ = lean_nat_mul(v___x_772_, v___x_773_);
v___x_775_ = lean_unsigned_to_nat(0u);
v___x_776_ = lean_box(0);
v___x_777_ = lean_mk_array(v_nbuckets_774_, v___x_776_);
v___x_778_ = lean_array_propagate_mark(v_data_771_, v___x_777_);
v___x_779_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v___x_775_, v_data_771_, v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(lean_object* v_a_780_, lean_object* v_b_781_, lean_object* v_x_782_){
_start:
{
if (lean_obj_tag(v_x_782_) == 0)
{
lean_dec(v_b_781_);
lean_dec_ref(v_a_780_);
return v_x_782_;
}
else
{
lean_object* v_key_783_; lean_object* v_value_784_; lean_object* v_tail_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_797_; 
v_key_783_ = lean_ctor_get(v_x_782_, 0);
v_value_784_ = lean_ctor_get(v_x_782_, 1);
v_tail_785_ = lean_ctor_get(v_x_782_, 2);
v_isSharedCheck_797_ = !lean_is_exclusive(v_x_782_);
if (v_isSharedCheck_797_ == 0)
{
v___x_787_ = v_x_782_;
v_isShared_788_ = v_isSharedCheck_797_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_tail_785_);
lean_inc(v_value_784_);
lean_inc(v_key_783_);
lean_dec(v_x_782_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_797_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
uint8_t v___x_789_; 
v___x_789_ = l_Lean_ExprStructEq_beq(v_key_783_, v_a_780_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_790_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_780_, v_b_781_, v_tail_785_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 2, v___x_790_);
v___x_792_ = v___x_787_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_key_783_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_value_784_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
else
{
lean_object* v___x_795_; 
lean_dec(v_value_784_);
lean_dec(v_key_783_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v_b_781_);
lean_ctor_set(v___x_787_, 0, v_a_780_);
v___x_795_ = v___x_787_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_780_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_b_781_);
lean_ctor_set(v_reuseFailAlloc_796_, 2, v_tail_785_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(lean_object* v_m_798_, lean_object* v_a_799_, lean_object* v_b_800_){
_start:
{
lean_object* v_size_801_; lean_object* v_buckets_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_845_; 
v_size_801_ = lean_ctor_get(v_m_798_, 0);
v_buckets_802_ = lean_ctor_get(v_m_798_, 1);
v_isSharedCheck_845_ = !lean_is_exclusive(v_m_798_);
if (v_isSharedCheck_845_ == 0)
{
v___x_804_ = v_m_798_;
v_isShared_805_ = v_isSharedCheck_845_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_buckets_802_);
lean_inc(v_size_801_);
lean_dec(v_m_798_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_845_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; uint64_t v___x_807_; uint64_t v___x_808_; uint64_t v___x_809_; uint64_t v_fold_810_; uint64_t v___x_811_; uint64_t v___x_812_; uint64_t v___x_813_; size_t v___x_814_; size_t v___x_815_; size_t v___x_816_; size_t v___x_817_; size_t v___x_818_; lean_object* v_bkt_819_; uint8_t v___x_820_; 
v___x_806_ = lean_array_get_size(v_buckets_802_);
v___x_807_ = l_Lean_ExprStructEq_hash(v_a_799_);
v___x_808_ = 32ULL;
v___x_809_ = lean_uint64_shift_right(v___x_807_, v___x_808_);
v_fold_810_ = lean_uint64_xor(v___x_807_, v___x_809_);
v___x_811_ = 16ULL;
v___x_812_ = lean_uint64_shift_right(v_fold_810_, v___x_811_);
v___x_813_ = lean_uint64_xor(v_fold_810_, v___x_812_);
v___x_814_ = lean_uint64_to_usize(v___x_813_);
v___x_815_ = lean_usize_of_nat(v___x_806_);
v___x_816_ = ((size_t)1ULL);
v___x_817_ = lean_usize_sub(v___x_815_, v___x_816_);
v___x_818_ = lean_usize_land(v___x_814_, v___x_817_);
v_bkt_819_ = lean_array_uget_borrowed(v_buckets_802_, v___x_818_);
v___x_820_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_799_, v_bkt_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v_size_x27_822_; lean_object* v___x_823_; lean_object* v_buckets_x27_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_821_ = lean_unsigned_to_nat(1u);
v_size_x27_822_ = lean_nat_add(v_size_801_, v___x_821_);
lean_dec(v_size_801_);
lean_inc(v_bkt_819_);
v___x_823_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_823_, 0, v_a_799_);
lean_ctor_set(v___x_823_, 1, v_b_800_);
lean_ctor_set(v___x_823_, 2, v_bkt_819_);
v_buckets_x27_824_ = lean_array_uset(v_buckets_802_, v___x_818_, v___x_823_);
v___x_825_ = lean_unsigned_to_nat(4u);
v___x_826_ = lean_nat_mul(v_size_x27_822_, v___x_825_);
v___x_827_ = lean_unsigned_to_nat(3u);
v___x_828_ = lean_nat_div(v___x_826_, v___x_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_array_get_size(v_buckets_x27_824_);
v___x_830_ = lean_nat_dec_le(v___x_828_, v___x_829_);
lean_dec(v___x_828_);
if (v___x_830_ == 0)
{
lean_object* v_val_831_; lean_object* v___x_833_; 
v_val_831_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_buckets_x27_824_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 1, v_val_831_);
lean_ctor_set(v___x_804_, 0, v_size_x27_822_);
v___x_833_ = v___x_804_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_size_x27_822_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_val_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
else
{
lean_object* v___x_836_; 
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 1, v_buckets_x27_824_);
lean_ctor_set(v___x_804_, 0, v_size_x27_822_);
v___x_836_ = v___x_804_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_size_x27_822_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_buckets_x27_824_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
else
{
lean_object* v___x_838_; lean_object* v_buckets_x27_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
lean_inc(v_bkt_819_);
v___x_838_ = lean_box(0);
v_buckets_x27_839_ = lean_array_uset(v_buckets_802_, v___x_818_, v___x_838_);
v___x_840_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_799_, v_b_800_, v_bkt_819_);
v___x_841_ = lean_array_uset(v_buckets_x27_839_, v___x_818_, v___x_840_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 1, v___x_841_);
v___x_843_ = v___x_804_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_size_801_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(lean_object* v_a_846_, lean_object* v_e_847_, lean_object* v_a_848_){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_850_ = lean_st_ref_take(v_a_846_);
v___x_851_ = lean_box(0);
v___x_852_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v___x_850_, v_e_847_, v_a_848_);
v___x_853_ = lean_st_ref_put(v_a_846_, v___x_852_);
return v___x_851_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_846_ = stack[0].m_obj;
lean_object* v_e_847_ = stack[1].m_obj;
lean_object* v_a_848_ = stack[2].m_obj;
lean_object* v_res_854_;
v_res_854_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(v_a_846_, v_e_847_, v_a_848_);
stack->m_obj
 = v_res_854_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed(lean_object* v_a_855_, lean_object* v_e_856_, lean_object* v_a_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(v_a_855_, v_e_856_, v_a_857_);
lean_dec(v_a_855_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed(lean_object* v_fvars_860_, lean_object* v_pre_861_, lean_object* v_post_862_, lean_object* v_usedLetOnly_863_, lean_object* v_skipConstInApp_864_, lean_object* v_skipInstances_865_, lean_object* v_body_866_, lean_object* v_x_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
uint8_t v_usedLetOnly_boxed_874_; uint8_t v_skipConstInApp_boxed_875_; uint8_t v_skipInstances_boxed_876_; lean_object* v_res_877_; 
v_usedLetOnly_boxed_874_ = lean_unbox(v_usedLetOnly_863_);
v_skipConstInApp_boxed_875_ = lean_unbox(v_skipConstInApp_864_);
v_skipInstances_boxed_876_ = lean_unbox(v_skipInstances_865_);
v_res_877_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(v_fvars_860_, v_pre_861_, v_post_862_, v_usedLetOnly_boxed_874_, v_skipConstInApp_boxed_875_, v_skipInstances_boxed_876_, v_body_866_, v_x_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
return v_res_877_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(lean_object* v_fvars_881_, lean_object* v_pre_882_, lean_object* v_post_883_, uint8_t v_usedLetOnly_884_, uint8_t v_skipConstInApp_885_, uint8_t v_skipInstances_886_, lean_object* v_body_887_, lean_object* v_x_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = lean_array_push(v_fvars_881_, v_x_888_);
v___x_896_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_882_, v_post_883_, v_usedLetOnly_884_, v_skipConstInApp_885_, v_skipInstances_886_, v___x_895_, v_body_887_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
return v___x_896_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_881_ = stack[0].m_obj;
lean_object* v_pre_882_ = stack[1].m_obj;
lean_object* v_post_883_ = stack[2].m_obj;
uint8_t v_usedLetOnly_884_ = stack[3].m_num;
uint8_t v_skipConstInApp_885_ = stack[4].m_num;
uint8_t v_skipInstances_886_ = stack[5].m_num;
lean_object* v_body_887_ = stack[6].m_obj;
lean_object* v_x_888_ = stack[7].m_obj;
lean_object* v___y_889_ = stack[8].m_obj;
lean_object* v___y_890_ = stack[9].m_obj;
lean_object* v___y_891_ = stack[10].m_obj;
lean_object* v___y_892_ = stack[11].m_obj;
lean_object* v___y_893_ = stack[12].m_obj;
lean_object* v_res_897_;
v_res_897_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(v_fvars_881_, v_pre_882_, v_post_883_, v_usedLetOnly_884_, v_skipConstInApp_885_, v_skipInstances_886_, v_body_887_, v_x_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
stack->m_obj
 = v_res_897_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed(lean_object* v_fvars_898_, lean_object* v_pre_899_, lean_object* v_post_900_, lean_object* v_usedLetOnly_901_, lean_object* v_skipConstInApp_902_, lean_object* v_skipInstances_903_, lean_object* v_body_904_, lean_object* v_x_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
uint8_t v_usedLetOnly_boxed_912_; uint8_t v_skipConstInApp_boxed_913_; uint8_t v_skipInstances_boxed_914_; lean_object* v_res_915_; 
v_usedLetOnly_boxed_912_ = lean_unbox(v_usedLetOnly_901_);
v_skipConstInApp_boxed_913_ = lean_unbox(v_skipConstInApp_902_);
v_skipInstances_boxed_914_ = lean_unbox(v_skipInstances_903_);
v_res_915_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(v_fvars_898_, v_pre_899_, v_post_900_, v_usedLetOnly_boxed_912_, v_skipConstInApp_boxed_913_, v_skipInstances_boxed_914_, v_body_904_, v_x_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
return v_res_915_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(lean_object* v_pre_916_, lean_object* v_post_917_, uint8_t v_usedLetOnly_918_, uint8_t v_skipConstInApp_919_, uint8_t v_skipInstances_920_, lean_object* v_e_921_, lean_object* v_a_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; 
lean_inc_ref(v_post_917_);
lean_inc(v___y_926_);
lean_inc_ref(v___y_925_);
lean_inc(v___y_924_);
lean_inc_ref(v___y_923_);
lean_inc_ref(v_e_921_);
v___x_928_ = lean_apply_6(v_post_917_, v_e_921_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, lean_box(0));
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_947_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_947_ == 0)
{
v___x_931_ = v___x_928_;
v_isShared_932_ = v_isSharedCheck_947_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_928_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_947_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
switch(lean_obj_tag(v_a_929_))
{
case 0:
{
lean_object* v_e_933_; lean_object* v___x_935_; 
lean_dec_ref(v_e_921_);
lean_dec_ref(v_post_917_);
lean_dec_ref(v_pre_916_);
v_e_933_ = lean_ctor_get(v_a_929_, 0);
lean_inc_ref(v_e_933_);
lean_dec_ref_known(v_a_929_, 1);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v_e_933_);
v___x_935_ = v___x_931_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_e_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
case 1:
{
lean_object* v_e_937_; lean_object* v___x_938_; 
lean_del_object(v___x_931_);
lean_dec_ref(v_e_921_);
v_e_937_ = lean_ctor_get(v_a_929_, 0);
lean_inc_ref(v_e_937_);
lean_dec_ref_known(v_a_929_, 1);
v___x_938_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_916_, v_post_917_, v_usedLetOnly_918_, v_skipConstInApp_919_, v_skipInstances_920_, v_e_937_, v_a_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
return v___x_938_;
}
default: 
{
lean_object* v_e_x3f_939_; 
lean_dec_ref(v_post_917_);
lean_dec_ref(v_pre_916_);
v_e_x3f_939_ = lean_ctor_get(v_a_929_, 0);
lean_inc(v_e_x3f_939_);
lean_dec_ref_known(v_a_929_, 1);
if (lean_obj_tag(v_e_x3f_939_) == 0)
{
lean_object* v___x_941_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v_e_921_);
v___x_941_ = v___x_931_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_e_921_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
else
{
lean_object* v_val_943_; lean_object* v___x_945_; 
lean_dec_ref(v_e_921_);
v_val_943_ = lean_ctor_get(v_e_x3f_939_, 0);
lean_inc(v_val_943_);
lean_dec_ref_known(v_e_x3f_939_, 1);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v_val_943_);
v___x_945_ = v___x_931_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_val_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref(v_e_921_);
lean_dec_ref(v_post_917_);
lean_dec_ref(v_pre_916_);
v_a_948_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_928_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_928_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_916_ = stack[0].m_obj;
lean_object* v_post_917_ = stack[1].m_obj;
uint8_t v_usedLetOnly_918_ = stack[2].m_num;
uint8_t v_skipConstInApp_919_ = stack[3].m_num;
uint8_t v_skipInstances_920_ = stack[4].m_num;
lean_object* v_e_921_ = stack[5].m_obj;
lean_object* v_a_922_ = stack[6].m_obj;
lean_object* v___y_923_ = stack[7].m_obj;
lean_object* v___y_924_ = stack[8].m_obj;
lean_object* v___y_925_ = stack[9].m_obj;
lean_object* v___y_926_ = stack[10].m_obj;
lean_object* v_res_956_;
v_res_956_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_916_, v_post_917_, v_usedLetOnly_918_, v_skipConstInApp_919_, v_skipInstances_920_, v_e_921_, v_a_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
stack->m_obj
 = v_res_956_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(lean_object* v_pre_957_, lean_object* v_post_958_, uint8_t v_usedLetOnly_959_, uint8_t v_skipConstInApp_960_, uint8_t v_skipInstances_961_, lean_object* v_fvars_962_, lean_object* v_e_963_, lean_object* v_a_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
if (lean_obj_tag(v_e_963_) == 6)
{
lean_object* v_binderName_970_; lean_object* v_binderType_971_; lean_object* v_body_972_; uint8_t v_binderInfo_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___f_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v_binderName_970_ = lean_ctor_get(v_e_963_, 0);
lean_inc(v_binderName_970_);
v_binderType_971_ = lean_ctor_get(v_e_963_, 1);
lean_inc_ref(v_binderType_971_);
v_body_972_ = lean_ctor_get(v_e_963_, 2);
lean_inc_ref(v_body_972_);
v_binderInfo_973_ = lean_ctor_get_uint8(v_e_963_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_963_, 3);
v___x_974_ = lean_box(v_usedLetOnly_959_);
v___x_975_ = lean_box(v_skipConstInApp_960_);
v___x_976_ = lean_box(v_skipInstances_961_);
lean_inc_ref(v_post_958_);
lean_inc_ref(v_pre_957_);
lean_inc_ref(v_fvars_962_);
v___f_977_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed), 14, 7);
lean_closure_set(v___f_977_, 0, v_fvars_962_);
lean_closure_set(v___f_977_, 1, v_pre_957_);
lean_closure_set(v___f_977_, 2, v_post_958_);
lean_closure_set(v___f_977_, 3, v___x_974_);
lean_closure_set(v___f_977_, 4, v___x_975_);
lean_closure_set(v___f_977_, 5, v___x_976_);
lean_closure_set(v___f_977_, 6, v_body_972_);
v___x_978_ = lean_expr_instantiate_rev(v_binderType_971_, v_fvars_962_);
lean_dec_ref(v_fvars_962_);
lean_dec_ref(v_binderType_971_);
v___x_979_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_957_, v_post_958_, v_usedLetOnly_959_, v_skipConstInApp_960_, v_skipInstances_961_, v___x_978_, v_a_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; uint8_t v___x_981_; lean_object* v___x_982_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
v___x_981_ = 0;
v___x_982_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_970_, v_binderInfo_973_, v_a_980_, v___f_977_, v___x_981_, v_a_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
return v___x_982_;
}
else
{
lean_dec_ref(v___f_977_);
lean_dec(v_binderName_970_);
return v___x_979_;
}
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_expr_instantiate_rev(v_e_963_, v_fvars_962_);
lean_dec_ref(v_e_963_);
lean_inc_ref(v_post_958_);
lean_inc_ref(v_pre_957_);
v___x_984_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_957_, v_post_958_, v_usedLetOnly_959_, v_skipConstInApp_960_, v_skipInstances_961_, v___x_983_, v_a_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; uint8_t v___x_986_; uint8_t v___x_987_; uint8_t v___x_988_; lean_object* v___x_989_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
v___x_986_ = 0;
v___x_987_ = 1;
v___x_988_ = 1;
v___x_989_ = l_Lean_Meta_mkLambdaFVars(v_fvars_962_, v_a_985_, v___x_986_, v_usedLetOnly_959_, v___x_986_, v___x_987_, v___x_988_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec_ref(v_fvars_962_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_991_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
v___x_991_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_957_, v_post_958_, v_usedLetOnly_959_, v_skipConstInApp_960_, v_skipInstances_961_, v_a_990_, v_a_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
return v___x_991_;
}
else
{
lean_dec_ref(v_post_958_);
lean_dec_ref(v_pre_957_);
return v___x_989_;
}
}
else
{
lean_dec_ref(v_fvars_962_);
lean_dec_ref(v_post_958_);
lean_dec_ref(v_pre_957_);
return v___x_984_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_957_ = stack[0].m_obj;
lean_object* v_post_958_ = stack[1].m_obj;
uint8_t v_usedLetOnly_959_ = stack[2].m_num;
uint8_t v_skipConstInApp_960_ = stack[3].m_num;
uint8_t v_skipInstances_961_ = stack[4].m_num;
lean_object* v_fvars_962_ = stack[5].m_obj;
lean_object* v_e_963_ = stack[6].m_obj;
lean_object* v_a_964_ = stack[7].m_obj;
lean_object* v___y_965_ = stack[8].m_obj;
lean_object* v___y_966_ = stack[9].m_obj;
lean_object* v___y_967_ = stack[10].m_obj;
lean_object* v___y_968_ = stack[11].m_obj;
lean_object* v_res_992_;
v_res_992_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_957_, v_post_958_, v_usedLetOnly_959_, v_skipConstInApp_960_, v_skipInstances_961_, v_fvars_962_, v_e_963_, v_a_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
stack->m_obj
 = v_res_992_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(lean_object* v_fvars_993_, lean_object* v_pre_994_, lean_object* v_post_995_, uint8_t v_usedLetOnly_996_, uint8_t v_skipConstInApp_997_, uint8_t v_skipInstances_998_, lean_object* v_body_999_, lean_object* v_x_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_array_push(v_fvars_993_, v_x_1000_);
v___x_1008_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_994_, v_post_995_, v_usedLetOnly_996_, v_skipConstInApp_997_, v_skipInstances_998_, v___x_1007_, v_body_999_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
return v___x_1008_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_993_ = stack[0].m_obj;
lean_object* v_pre_994_ = stack[1].m_obj;
lean_object* v_post_995_ = stack[2].m_obj;
uint8_t v_usedLetOnly_996_ = stack[3].m_num;
uint8_t v_skipConstInApp_997_ = stack[4].m_num;
uint8_t v_skipInstances_998_ = stack[5].m_num;
lean_object* v_body_999_ = stack[6].m_obj;
lean_object* v_x_1000_ = stack[7].m_obj;
lean_object* v___y_1001_ = stack[8].m_obj;
lean_object* v___y_1002_ = stack[9].m_obj;
lean_object* v___y_1003_ = stack[10].m_obj;
lean_object* v___y_1004_ = stack[11].m_obj;
lean_object* v___y_1005_ = stack[12].m_obj;
lean_object* v_res_1009_;
v_res_1009_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(v_fvars_993_, v_pre_994_, v_post_995_, v_usedLetOnly_996_, v_skipConstInApp_997_, v_skipInstances_998_, v_body_999_, v_x_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
stack->m_obj
 = v_res_1009_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_1010_, lean_object* v_pre_1011_, lean_object* v_post_1012_, lean_object* v_usedLetOnly_1013_, lean_object* v_skipConstInApp_1014_, lean_object* v_skipInstances_1015_, lean_object* v_body_1016_, lean_object* v_x_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
uint8_t v_usedLetOnly_boxed_1024_; uint8_t v_skipConstInApp_boxed_1025_; uint8_t v_skipInstances_boxed_1026_; lean_object* v_res_1027_; 
v_usedLetOnly_boxed_1024_ = lean_unbox(v_usedLetOnly_1013_);
v_skipConstInApp_boxed_1025_ = lean_unbox(v_skipConstInApp_1014_);
v_skipInstances_boxed_1026_ = lean_unbox(v_skipInstances_1015_);
v_res_1027_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(v_fvars_1010_, v_pre_1011_, v_post_1012_, v_usedLetOnly_boxed_1024_, v_skipConstInApp_boxed_1025_, v_skipInstances_boxed_1026_, v_body_1016_, v_x_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
return v_res_1027_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(lean_object* v_pre_1028_, lean_object* v_post_1029_, uint8_t v_usedLetOnly_1030_, uint8_t v_skipConstInApp_1031_, uint8_t v_skipInstances_1032_, lean_object* v_fvars_1033_, lean_object* v_e_1034_, lean_object* v_a_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
if (lean_obj_tag(v_e_1034_) == 8)
{
lean_object* v_declName_1041_; lean_object* v_type_1042_; lean_object* v_value_1043_; lean_object* v_body_1044_; uint8_t v_nondep_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___f_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_declName_1041_ = lean_ctor_get(v_e_1034_, 0);
lean_inc(v_declName_1041_);
v_type_1042_ = lean_ctor_get(v_e_1034_, 1);
lean_inc_ref(v_type_1042_);
v_value_1043_ = lean_ctor_get(v_e_1034_, 2);
lean_inc_ref(v_value_1043_);
v_body_1044_ = lean_ctor_get(v_e_1034_, 3);
lean_inc_ref(v_body_1044_);
v_nondep_1045_ = lean_ctor_get_uint8(v_e_1034_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1034_, 4);
v___x_1046_ = lean_box(v_usedLetOnly_1030_);
v___x_1047_ = lean_box(v_skipConstInApp_1031_);
v___x_1048_ = lean_box(v_skipInstances_1032_);
lean_inc_ref_n(v_post_1029_, 2);
lean_inc_ref_n(v_pre_1028_, 2);
lean_inc_ref(v_fvars_1033_);
v___f_1049_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1049_, 0, v_fvars_1033_);
lean_closure_set(v___f_1049_, 1, v_pre_1028_);
lean_closure_set(v___f_1049_, 2, v_post_1029_);
lean_closure_set(v___f_1049_, 3, v___x_1046_);
lean_closure_set(v___f_1049_, 4, v___x_1047_);
lean_closure_set(v___f_1049_, 5, v___x_1048_);
lean_closure_set(v___f_1049_, 6, v_body_1044_);
v___x_1050_ = lean_expr_instantiate_rev(v_type_1042_, v_fvars_1033_);
lean_dec_ref(v_type_1042_);
v___x_1051_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1028_, v_post_1029_, v_usedLetOnly_1030_, v_skipConstInApp_1031_, v_skipInstances_1032_, v___x_1050_, v_a_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v___x_1051_, 1);
v___x_1053_ = lean_expr_instantiate_rev(v_value_1043_, v_fvars_1033_);
lean_dec_ref(v_fvars_1033_);
lean_dec_ref(v_value_1043_);
v___x_1054_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1028_, v_post_1029_, v_usedLetOnly_1030_, v_skipConstInApp_1031_, v_skipInstances_1032_, v___x_1053_, v_a_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; uint8_t v___x_1056_; lean_object* v___x_1057_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1054_, 1);
v___x_1056_ = 0;
v___x_1057_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_declName_1041_, v_a_1052_, v_a_1055_, v___f_1049_, v_nondep_1045_, v___x_1056_, v_a_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
return v___x_1057_;
}
else
{
lean_dec(v_a_1052_);
lean_dec_ref(v___f_1049_);
lean_dec(v_declName_1041_);
return v___x_1054_;
}
}
else
{
lean_dec_ref(v___f_1049_);
lean_dec_ref(v_value_1043_);
lean_dec(v_declName_1041_);
lean_dec_ref(v_fvars_1033_);
lean_dec_ref(v_post_1029_);
lean_dec_ref(v_pre_1028_);
return v___x_1051_;
}
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_expr_instantiate_rev(v_e_1034_, v_fvars_1033_);
lean_dec_ref(v_e_1034_);
lean_inc_ref(v_post_1029_);
lean_inc_ref(v_pre_1028_);
v___x_1059_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1028_, v_post_1029_, v_usedLetOnly_1030_, v_skipConstInApp_1031_, v_skipInstances_1032_, v___x_1058_, v_a_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; uint8_t v___x_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1061_ = 0;
v___x_1062_ = 1;
v___x_1063_ = l_Lean_Meta_mkLetFVars(v_fvars_1033_, v_a_1060_, v_usedLetOnly_1030_, v___x_1061_, v___x_1062_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec_ref(v_fvars_1033_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1065_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref_known(v___x_1063_, 1);
v___x_1065_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1028_, v_post_1029_, v_usedLetOnly_1030_, v_skipConstInApp_1031_, v_skipInstances_1032_, v_a_1064_, v_a_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
return v___x_1065_;
}
else
{
lean_dec_ref(v_post_1029_);
lean_dec_ref(v_pre_1028_);
return v___x_1063_;
}
}
else
{
lean_dec_ref(v_fvars_1033_);
lean_dec_ref(v_post_1029_);
lean_dec_ref(v_pre_1028_);
return v___x_1059_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1028_ = stack[0].m_obj;
lean_object* v_post_1029_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1030_ = stack[2].m_num;
uint8_t v_skipConstInApp_1031_ = stack[3].m_num;
uint8_t v_skipInstances_1032_ = stack[4].m_num;
lean_object* v_fvars_1033_ = stack[5].m_obj;
lean_object* v_e_1034_ = stack[6].m_obj;
lean_object* v_a_1035_ = stack[7].m_obj;
lean_object* v___y_1036_ = stack[8].m_obj;
lean_object* v___y_1037_ = stack[9].m_obj;
lean_object* v___y_1038_ = stack[10].m_obj;
lean_object* v___y_1039_ = stack[11].m_obj;
lean_object* v_res_1066_;
v_res_1066_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1028_, v_post_1029_, v_usedLetOnly_1030_, v_skipConstInApp_1031_, v_skipInstances_1032_, v_fvars_1033_, v_e_1034_, v_a_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
stack->m_obj
 = v_res_1066_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(lean_object* v_pre_1067_, lean_object* v_post_1068_, uint8_t v_usedLetOnly_1069_, uint8_t v_skipConstInApp_1070_, uint8_t v_skipInstances_1071_, size_t v_sz_1072_, size_t v_i_1073_, lean_object* v_bs_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
uint8_t v___x_1081_; 
v___x_1081_ = lean_usize_dec_lt(v_i_1073_, v_sz_1072_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; 
lean_dec_ref(v_post_1068_);
lean_dec_ref(v_pre_1067_);
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v_bs_1074_);
return v___x_1082_;
}
else
{
lean_object* v_v_1083_; lean_object* v___x_1084_; lean_object* v_bs_x27_1085_; lean_object* v___x_1086_; 
v_v_1083_ = lean_array_uget(v_bs_1074_, v_i_1073_);
v___x_1084_ = lean_unsigned_to_nat(0u);
v_bs_x27_1085_ = lean_array_uset(v_bs_1074_, v_i_1073_, v___x_1084_);
lean_inc_ref(v_post_1068_);
lean_inc_ref(v_pre_1067_);
v___x_1086_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1067_, v_post_1068_, v_usedLetOnly_1069_, v_skipConstInApp_1070_, v_skipInstances_1071_, v_v_1083_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; size_t v___x_1088_; size_t v___x_1089_; lean_object* v___x_1090_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v___x_1088_ = ((size_t)1ULL);
v___x_1089_ = lean_usize_add(v_i_1073_, v___x_1088_);
v___x_1090_ = lean_array_uset(v_bs_x27_1085_, v_i_1073_, v_a_1087_);
v_i_1073_ = v___x_1089_;
v_bs_1074_ = v___x_1090_;
goto _start;
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec_ref(v_bs_x27_1085_);
lean_dec_ref(v_post_1068_);
lean_dec_ref(v_pre_1067_);
v_a_1092_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1086_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1086_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1067_ = stack[0].m_obj;
lean_object* v_post_1068_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1069_ = stack[2].m_num;
uint8_t v_skipConstInApp_1070_ = stack[3].m_num;
uint8_t v_skipInstances_1071_ = stack[4].m_num;
size_t v_sz_1072_ = stack[5].m_num;
size_t v_i_1073_ = stack[6].m_num;
lean_object* v_bs_1074_ = stack[7].m_obj;
lean_object* v___y_1075_ = stack[8].m_obj;
lean_object* v___y_1076_ = stack[9].m_obj;
lean_object* v___y_1077_ = stack[10].m_obj;
lean_object* v___y_1078_ = stack[11].m_obj;
lean_object* v___y_1079_ = stack[12].m_obj;
lean_object* v_res_1100_;
v_res_1100_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_1067_, v_post_1068_, v_usedLetOnly_1069_, v_skipConstInApp_1070_, v_skipInstances_1071_, v_sz_1072_, v_i_1073_, v_bs_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
stack->m_obj
 = v_res_1100_;
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(lean_object* v_pre_1101_, lean_object* v_post_1102_, uint8_t v_usedLetOnly_1103_, uint8_t v_skipConstInApp_1104_, uint8_t v_skipInstances_1105_, lean_object* v___x_1106_, lean_object* v___y_1107_, lean_object* v_b_1108_, lean_object* v_a_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1101_, v_post_1102_, v_usedLetOnly_1103_, v_skipConstInApp_1104_, v_skipInstances_1105_, v___x_1106_, v___y_1107_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1125_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1125_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1125_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___x_1120_ = lean_array_fset(v_b_1108_, v_a_1109_, v_a_1116_);
v___x_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v___x_1121_);
v___x_1123_ = v___x_1118_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec_ref(v_b_1108_);
v_a_1126_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1115_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1115_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1101_ = stack[0].m_obj;
lean_object* v_post_1102_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1103_ = stack[2].m_num;
uint8_t v_skipConstInApp_1104_ = stack[3].m_num;
uint8_t v_skipInstances_1105_ = stack[4].m_num;
lean_object* v___x_1106_ = stack[5].m_obj;
lean_object* v___y_1107_ = stack[6].m_obj;
lean_object* v_b_1108_ = stack[7].m_obj;
lean_object* v_a_1109_ = stack[8].m_obj;
lean_object* v___y_1110_ = stack[9].m_obj;
lean_object* v___y_1111_ = stack[10].m_obj;
lean_object* v___y_1112_ = stack[11].m_obj;
lean_object* v___y_1113_ = stack[12].m_obj;
lean_object* v_res_1134_;
v_res_1134_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(v_pre_1101_, v_post_1102_, v_usedLetOnly_1103_, v_skipConstInApp_1104_, v_skipInstances_1105_, v___x_1106_, v___y_1107_, v_b_1108_, v_a_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
stack->m_obj
 = v_res_1134_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed(lean_object* v_pre_1135_, lean_object* v_post_1136_, lean_object* v_usedLetOnly_1137_, lean_object* v_skipConstInApp_1138_, lean_object* v_skipInstances_1139_, lean_object* v___x_1140_, lean_object* v___y_1141_, lean_object* v_b_1142_, lean_object* v_a_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
uint8_t v_usedLetOnly_boxed_1149_; uint8_t v_skipConstInApp_boxed_1150_; uint8_t v_skipInstances_boxed_1151_; lean_object* v_res_1152_; 
v_usedLetOnly_boxed_1149_ = lean_unbox(v_usedLetOnly_1137_);
v_skipConstInApp_boxed_1150_ = lean_unbox(v_skipConstInApp_1138_);
v_skipInstances_boxed_1151_ = lean_unbox(v_skipInstances_1139_);
v_res_1152_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(v_pre_1135_, v_post_1136_, v_usedLetOnly_boxed_1149_, v_skipConstInApp_boxed_1150_, v_skipInstances_boxed_1151_, v___x_1140_, v___y_1141_, v_b_1142_, v_a_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v_a_1143_);
lean_dec(v___y_1141_);
return v_res_1152_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(lean_object* v_upperBound_1153_, lean_object* v___x_1154_, lean_object* v_pre_1155_, lean_object* v_post_1156_, uint8_t v_usedLetOnly_1157_, uint8_t v_skipConstInApp_1158_, uint8_t v_skipInstances_1159_, lean_object* v_a_1160_, lean_object* v_b_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v___y_1169_; uint8_t v___x_1192_; 
v___x_1192_ = lean_nat_dec_lt(v_a_1160_, v_upperBound_1153_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; 
lean_dec(v_a_1160_);
lean_dec_ref(v_post_1156_);
lean_dec_ref(v_pre_1155_);
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v_b_1161_);
return v___x_1193_;
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1194_ = lean_array_fget_borrowed(v_b_1161_, v_a_1160_);
v___x_1195_ = lean_array_get_size(v___x_1154_);
v___x_1196_ = lean_nat_dec_lt(v_a_1160_, v___x_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___f_1200_; 
lean_inc(v___x_1194_);
v___x_1197_ = lean_box(v_usedLetOnly_1157_);
v___x_1198_ = lean_box(v_skipConstInApp_1158_);
v___x_1199_ = lean_box(v_skipInstances_1159_);
lean_inc(v_a_1160_);
lean_inc(v___y_1162_);
lean_inc_ref(v_post_1156_);
lean_inc_ref(v_pre_1155_);
v___f_1200_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1200_, 0, v_pre_1155_);
lean_closure_set(v___f_1200_, 1, v_post_1156_);
lean_closure_set(v___f_1200_, 2, v___x_1197_);
lean_closure_set(v___f_1200_, 3, v___x_1198_);
lean_closure_set(v___f_1200_, 4, v___x_1199_);
lean_closure_set(v___f_1200_, 5, v___x_1194_);
lean_closure_set(v___f_1200_, 6, v___y_1162_);
lean_closure_set(v___f_1200_, 7, v_b_1161_);
lean_closure_set(v___f_1200_, 8, v_a_1160_);
v___y_1169_ = v___f_1200_;
goto v___jp_1168_;
}
else
{
lean_object* v___x_1201_; uint8_t v_isInstance_1202_; 
v___x_1201_ = lean_array_fget_borrowed(v___x_1154_, v_a_1160_);
v_isInstance_1202_ = lean_ctor_get_uint8(v___x_1201_, sizeof(void*)*1 + 4);
if (v_isInstance_1202_ == 0)
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___f_1206_; 
lean_inc(v___x_1194_);
v___x_1203_ = lean_box(v_usedLetOnly_1157_);
v___x_1204_ = lean_box(v_skipConstInApp_1158_);
v___x_1205_ = lean_box(v_skipInstances_1159_);
lean_inc(v_a_1160_);
lean_inc(v___y_1162_);
lean_inc_ref(v_post_1156_);
lean_inc_ref(v_pre_1155_);
v___f_1206_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1206_, 0, v_pre_1155_);
lean_closure_set(v___f_1206_, 1, v_post_1156_);
lean_closure_set(v___f_1206_, 2, v___x_1203_);
lean_closure_set(v___f_1206_, 3, v___x_1204_);
lean_closure_set(v___f_1206_, 4, v___x_1205_);
lean_closure_set(v___f_1206_, 5, v___x_1194_);
lean_closure_set(v___f_1206_, 6, v___y_1162_);
lean_closure_set(v___f_1206_, 7, v_b_1161_);
lean_closure_set(v___f_1206_, 8, v_a_1160_);
v___y_1169_ = v___f_1206_;
goto v___jp_1168_;
}
else
{
lean_object* v___x_1207_; lean_object* v___f_1208_; 
v___x_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1207_, 0, v_b_1161_);
v___f_1208_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1208_, 0, v___x_1207_);
v___y_1169_ = v___f_1208_;
goto v___jp_1168_;
}
}
}
v___jp_1168_:
{
lean_object* v___x_1170_; 
lean_inc(v___y_1166_);
lean_inc_ref(v___y_1165_);
lean_inc(v___y_1164_);
lean_inc_ref(v___y_1163_);
v___x_1170_ = lean_apply_5(v___y_1169_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, lean_box(0));
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1183_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1183_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1183_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
if (lean_obj_tag(v_a_1171_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1177_; 
lean_dec(v_a_1160_);
lean_dec_ref(v_post_1156_);
lean_dec_ref(v_pre_1155_);
v_a_1175_ = lean_ctor_get(v_a_1171_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v_a_1171_, 1);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v_a_1175_);
v___x_1177_ = v___x_1173_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
lean_del_object(v___x_1173_);
v_a_1179_ = lean_ctor_get(v_a_1171_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v_a_1171_, 1);
v___x_1180_ = lean_unsigned_to_nat(1u);
v___x_1181_ = lean_nat_add(v_a_1160_, v___x_1180_);
lean_dec(v_a_1160_);
v_a_1160_ = v___x_1181_;
v_b_1161_ = v_a_1179_;
goto _start;
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec(v_a_1160_);
lean_dec_ref(v_post_1156_);
lean_dec_ref(v_pre_1155_);
v_a_1184_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1170_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1170_);
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
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1153_ = stack[0].m_obj;
lean_object* v___x_1154_ = stack[1].m_obj;
lean_object* v_pre_1155_ = stack[2].m_obj;
lean_object* v_post_1156_ = stack[3].m_obj;
uint8_t v_usedLetOnly_1157_ = stack[4].m_num;
uint8_t v_skipConstInApp_1158_ = stack[5].m_num;
uint8_t v_skipInstances_1159_ = stack[6].m_num;
lean_object* v_a_1160_ = stack[7].m_obj;
lean_object* v_b_1161_ = stack[8].m_obj;
lean_object* v___y_1162_ = stack[9].m_obj;
lean_object* v___y_1163_ = stack[10].m_obj;
lean_object* v___y_1164_ = stack[11].m_obj;
lean_object* v___y_1165_ = stack[12].m_obj;
lean_object* v___y_1166_ = stack[13].m_obj;
lean_object* v_res_1209_;
v_res_1209_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_1153_, v___x_1154_, v_pre_1155_, v_post_1156_, v_usedLetOnly_1157_, v_skipConstInApp_1158_, v_skipInstances_1159_, v_a_1160_, v_b_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
stack->m_obj
 = v_res_1209_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(uint8_t v_skipInstances_1210_, lean_object* v_pre_1211_, lean_object* v_post_1212_, uint8_t v_usedLetOnly_1213_, uint8_t v_skipConstInApp_1214_, lean_object* v_x_1215_, lean_object* v_x_1216_, lean_object* v_x_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_f_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; 
if (lean_obj_tag(v_x_1215_) == 5)
{
lean_object* v_fn_1273_; lean_object* v_arg_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v_fn_1273_ = lean_ctor_get(v_x_1215_, 0);
lean_inc_ref(v_fn_1273_);
v_arg_1274_ = lean_ctor_get(v_x_1215_, 1);
lean_inc_ref(v_arg_1274_);
lean_dec_ref_known(v_x_1215_, 2);
v___x_1275_ = lean_array_set(v_x_1216_, v_x_1217_, v_arg_1274_);
v___x_1276_ = lean_unsigned_to_nat(1u);
v___x_1277_ = lean_nat_sub(v_x_1217_, v___x_1276_);
lean_dec(v_x_1217_);
v_x_1215_ = v_fn_1273_;
v_x_1216_ = v___x_1275_;
v_x_1217_ = v___x_1277_;
goto _start;
}
else
{
lean_dec(v_x_1217_);
if (v_skipConstInApp_1214_ == 0)
{
goto v___jp_1270_;
}
else
{
uint8_t v___x_1279_; 
v___x_1279_ = l_Lean_Expr_isConst(v_x_1215_);
if (v___x_1279_ == 0)
{
goto v___jp_1270_;
}
else
{
v_f_1225_ = v_x_1215_;
v___y_1226_ = v___y_1218_;
v___y_1227_ = v___y_1219_;
v___y_1228_ = v___y_1220_;
v___y_1229_ = v___y_1221_;
v___y_1230_ = v___y_1222_;
goto v___jp_1224_;
}
}
}
v___jp_1224_:
{
if (v_skipInstances_1210_ == 0)
{
size_t v_sz_1231_; size_t v___x_1232_; lean_object* v___x_1233_; 
v_sz_1231_ = lean_array_size(v_x_1216_);
v___x_1232_ = ((size_t)0ULL);
lean_inc_ref(v_post_1212_);
lean_inc_ref(v_pre_1211_);
v___x_1233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_1211_, v_post_1212_, v_usedLetOnly_1213_, v_skipConstInApp_1214_, v_skipInstances_1210_, v_sz_1231_, v___x_1232_, v_x_1216_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1234_);
lean_dec_ref_known(v___x_1233_, 1);
v___x_1235_ = l_Lean_mkAppN(v_f_1225_, v_a_1234_);
lean_dec(v_a_1234_);
v___x_1236_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1211_, v_post_1212_, v_usedLetOnly_1213_, v_skipConstInApp_1214_, v_skipInstances_1210_, v___x_1235_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
return v___x_1236_;
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec_ref(v_f_1225_);
lean_dec_ref(v_post_1212_);
lean_dec_ref(v_pre_1211_);
v_a_1237_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1233_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1233_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = lean_array_get_size(v_x_1216_);
lean_inc_ref(v_f_1225_);
v___x_1246_ = l_Lean_Meta_getFunInfoNArgs(v_f_1225_, v___x_1245_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v_paramInfo_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1246_, 1);
v_paramInfo_1248_ = lean_ctor_get(v_a_1247_, 0);
lean_inc_ref(v_paramInfo_1248_);
lean_dec(v_a_1247_);
v___x_1249_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1212_);
lean_inc_ref(v_pre_1211_);
v___x_1250_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v___x_1245_, v_paramInfo_1248_, v_pre_1211_, v_post_1212_, v_usedLetOnly_1213_, v_skipConstInApp_1214_, v_skipInstances_1210_, v___x_1249_, v_x_1216_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec_ref(v_paramInfo_1248_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
lean_dec_ref_known(v___x_1250_, 1);
v___x_1252_ = l_Lean_mkAppN(v_f_1225_, v_a_1251_);
lean_dec(v_a_1251_);
v___x_1253_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1211_, v_post_1212_, v_usedLetOnly_1213_, v_skipConstInApp_1214_, v_skipInstances_1210_, v___x_1252_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
return v___x_1253_;
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec_ref(v_f_1225_);
lean_dec_ref(v_post_1212_);
lean_dec_ref(v_pre_1211_);
v_a_1254_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1250_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1250_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec_ref(v_f_1225_);
lean_dec_ref(v_x_1216_);
lean_dec_ref(v_post_1212_);
lean_dec_ref(v_pre_1211_);
v_a_1262_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1246_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1246_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
v___jp_1270_:
{
lean_object* v___x_1271_; 
lean_inc_ref(v_post_1212_);
lean_inc_ref(v_pre_1211_);
v___x_1271_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1211_, v_post_1212_, v_usedLetOnly_1213_, v_skipConstInApp_1214_, v_skipInstances_1210_, v_x_1215_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___x_1271_, 1);
v_f_1225_ = v_a_1272_;
v___y_1226_ = v___y_1218_;
v___y_1227_ = v___y_1219_;
v___y_1228_ = v___y_1220_;
v___y_1229_ = v___y_1221_;
v___y_1230_ = v___y_1222_;
goto v___jp_1224_;
}
else
{
lean_dec_ref(v_x_1216_);
lean_dec_ref(v_post_1212_);
lean_dec_ref(v_pre_1211_);
return v___x_1271_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13_0interp(lean_interpreter_value* stack)
{
uint8_t v_skipInstances_1210_ = stack[0].m_num;
lean_object* v_pre_1211_ = stack[1].m_obj;
lean_object* v_post_1212_ = stack[2].m_obj;
uint8_t v_usedLetOnly_1213_ = stack[3].m_num;
uint8_t v_skipConstInApp_1214_ = stack[4].m_num;
lean_object* v_x_1215_ = stack[5].m_obj;
lean_object* v_x_1216_ = stack[6].m_obj;
lean_object* v_x_1217_ = stack[7].m_obj;
lean_object* v___y_1218_ = stack[8].m_obj;
lean_object* v___y_1219_ = stack[9].m_obj;
lean_object* v___y_1220_ = stack[10].m_obj;
lean_object* v___y_1221_ = stack[11].m_obj;
lean_object* v___y_1222_ = stack[12].m_obj;
lean_object* v_res_1280_;
v_res_1280_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_1210_, v_pre_1211_, v_post_1212_, v_usedLetOnly_1213_, v_skipConstInApp_1214_, v_x_1215_, v_x_1216_, v_x_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
stack->m_obj
 = v_res_1280_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(lean_object* v___x_1281_, lean_object* v_pre_1282_, lean_object* v_e_1283_, lean_object* v_post_1284_, uint8_t v_usedLetOnly_1285_, uint8_t v_skipConstInApp_1286_, uint8_t v_skipInstances_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Lean_Core_checkSystem(v___x_1281_, v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v___x_1295_; 
lean_dec_ref_known(v___x_1294_, 1);
lean_inc_ref(v_pre_1282_);
lean_inc(v___y_1292_);
lean_inc_ref(v___y_1291_);
lean_inc(v___y_1290_);
lean_inc_ref(v___y_1289_);
lean_inc_ref(v_e_1283_);
v___x_1295_ = lean_apply_6(v_pre_1282_, v_e_1283_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, lean_box(0));
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1344_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1344_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1344_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___y_1301_; 
switch(lean_obj_tag(v_a_1296_))
{
case 0:
{
lean_object* v_e_1336_; lean_object* v___x_1338_; 
lean_dec_ref(v_post_1284_);
lean_dec_ref(v_e_1283_);
lean_dec_ref(v_pre_1282_);
v_e_1336_ = lean_ctor_get(v_a_1296_, 0);
lean_inc_ref(v_e_1336_);
lean_dec_ref_known(v_a_1296_, 1);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v_e_1336_);
v___x_1338_ = v___x_1298_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_e_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
case 1:
{
lean_object* v_e_1340_; lean_object* v___x_1341_; 
lean_del_object(v___x_1298_);
lean_dec_ref(v_e_1283_);
v_e_1340_ = lean_ctor_get(v_a_1296_, 0);
lean_inc_ref(v_e_1340_);
lean_dec_ref_known(v_a_1296_, 1);
v___x_1341_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1282_, v_post_1284_, v_usedLetOnly_1285_, v_skipConstInApp_1286_, v_skipInstances_1287_, v_e_1340_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
return v___x_1341_;
}
default: 
{
lean_object* v_e_x3f_1342_; 
lean_del_object(v___x_1298_);
v_e_x3f_1342_ = lean_ctor_get(v_a_1296_, 0);
lean_inc(v_e_x3f_1342_);
lean_dec_ref_known(v_a_1296_, 1);
if (lean_obj_tag(v_e_x3f_1342_) == 0)
{
v___y_1301_ = v_e_1283_;
goto v___jp_1300_;
}
else
{
lean_object* v_val_1343_; 
lean_dec_ref(v_e_1283_);
v_val_1343_ = lean_ctor_get(v_e_x3f_1342_, 0);
lean_inc(v_val_1343_);
lean_dec_ref_known(v_e_x3f_1342_, 1);
v___y_1301_ = v_val_1343_;
goto v___jp_1300_;
}
}
}
v___jp_1300_:
{
switch(lean_obj_tag(v___y_1301_))
{
case 7:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1303_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1282_, v_post_1284_, v_usedLetOnly_1285_, v_skipConstInApp_1286_, v_skipInstances_1287_, v___x_1302_, v___y_1301_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
return v___x_1303_;
}
case 6:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1305_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1282_, v_post_1284_, v_usedLetOnly_1285_, v_skipConstInApp_1286_, v_skipInstances_1287_, v___x_1304_, v___y_1301_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
return v___x_1305_;
}
case 8:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1307_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1282_, v_post_1284_, v_usedLetOnly_1285_, v_skipConstInApp_1286_, v_skipInstances_1287_, v___x_1306_, v___y_1301_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
return v___x_1307_;
}
case 5:
{
lean_object* v_dummy_1308_; lean_object* v_nargs_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v_dummy_1308_ = lean_obj_once(&l_Lean_Elab_WF_withAppN___closed__0, &l_Lean_Elab_WF_withAppN___closed__0_once, _init_l_Lean_Elab_WF_withAppN___closed__0);
v_nargs_1309_ = l_Lean_Expr_getAppNumArgs(v___y_1301_);
lean_inc(v_nargs_1309_);
v___x_1310_ = lean_mk_array(v_nargs_1309_, v_dummy_1308_);
v___x_1311_ = lean_unsigned_to_nat(1u);
v___x_1312_ = lean_nat_sub(v_nargs_1309_, v___x_1311_);
lean_dec(v_nargs_1309_);
v___x_1313_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_1287_, v_pre_1282_, v_post_1284_, v_usedLetOnly_1285_, v_skipConstInApp_1286_, v___y_1301_, v___x_1310_, v___x_1312_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
return v___x_1313_;
}
case 10:
{
lean_object* v_data_1314_; lean_object* v_expr_1315_; lean_object* v___x_1316_; 
v_data_1314_ = lean_ctor_get(v___y_1301_, 0);
v_expr_1315_ = lean_ctor_get(v___y_1301_, 1);
lean_inc_ref(v_expr_1315_);
lean_inc_ref(v_post_1284_);
lean_inc_ref(v_pre_1282_);
v___x_1316_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1282_, v_post_1284_, v_usedLetOnly_1285_, v_skipConstInApp_1286_, v_skipInstances_1287_, v_expr_1315_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; size_t v___x_1318_; size_t v___x_1319_; uint8_t v___x_1320_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_a_1317_);
lean_dec_ref_known(v___x_1316_, 1);
v___x_1318_ = lean_ptr_addr(v_expr_1315_);
v___x_1319_ = lean_ptr_addr(v_a_1317_);
v___x_1320_ = lean_usize_dec_eq(v___x_1318_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_inc(v_data_1314_);
lean_dec_ref_known(v___y_1301_, 2);
v___x_1321_ = l_Lean_Expr_mdata___override(v_data_1314_, v_a_1317_);
v___x_1322_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1282_, v_post_1284_, v_usedLetOnly_1285_, v_skipConstInApp_1286_, v_skipInstances_1287_, v___x_1321_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; 
lean_dec(v_a_1317_);
v___x_1323_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1282_, v_post_1284_, v_usedLetOnly_1285_, v_skipConstInApp_1286_, v_skipInstances_1287_, v___y_1301_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
return v___x_1323_;
}
}
else
{
lean_dec_ref_known(v___y_1301_, 2);
lean_dec_ref(v_post_1284_);
lean_dec_ref(v_pre_1282_);
return v___x_1316_;
}
}
case 11:
{
lean_object* v_typeName_1324_; lean_object* v_idx_1325_; lean_object* v_struct_1326_; lean_object* v___x_1327_; 
v_typeName_1324_ = lean_ctor_get(v___y_1301_, 0);
v_idx_1325_ = lean_ctor_get(v___y_1301_, 1);
v_struct_1326_ = lean_ctor_get(v___y_1301_, 2);
lean_inc_ref(v_struct_1326_);
lean_inc_ref(v_post_1284_);
lean_inc_ref(v_pre_1282_);
v___x_1327_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1282_, v_post_1284_, v_usedLetOnly_1285_, v_skipConstInApp_1286_, v_skipInstances_1287_, v_struct_1326_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; size_t v___x_1329_; size_t v___x_1330_; uint8_t v___x_1331_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1327_, 1);
v___x_1329_ = lean_ptr_addr(v_struct_1326_);
v___x_1330_ = lean_ptr_addr(v_a_1328_);
v___x_1331_ = lean_usize_dec_eq(v___x_1329_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_inc(v_idx_1325_);
lean_inc(v_typeName_1324_);
lean_dec_ref_known(v___y_1301_, 3);
v___x_1332_ = l_Lean_Expr_proj___override(v_typeName_1324_, v_idx_1325_, v_a_1328_);
v___x_1333_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1282_, v_post_1284_, v_usedLetOnly_1285_, v_skipConstInApp_1286_, v_skipInstances_1287_, v___x_1332_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
return v___x_1333_;
}
else
{
lean_object* v___x_1334_; 
lean_dec(v_a_1328_);
v___x_1334_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1282_, v_post_1284_, v_usedLetOnly_1285_, v_skipConstInApp_1286_, v_skipInstances_1287_, v___y_1301_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
return v___x_1334_;
}
}
else
{
lean_dec_ref_known(v___y_1301_, 3);
lean_dec_ref(v_post_1284_);
lean_dec_ref(v_pre_1282_);
return v___x_1327_;
}
}
default: 
{
lean_object* v___x_1335_; 
v___x_1335_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1282_, v_post_1284_, v_usedLetOnly_1285_, v_skipConstInApp_1286_, v_skipInstances_1287_, v___y_1301_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
return v___x_1335_;
}
}
}
}
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec_ref(v_post_1284_);
lean_dec_ref(v_e_1283_);
lean_dec_ref(v_pre_1282_);
v_a_1345_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1295_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1295_);
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
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec_ref(v_post_1284_);
lean_dec_ref(v_e_1283_);
lean_dec_ref(v_pre_1282_);
v_a_1353_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1294_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1294_);
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
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1281_ = stack[0].m_obj;
lean_object* v_pre_1282_ = stack[1].m_obj;
lean_object* v_e_1283_ = stack[2].m_obj;
lean_object* v_post_1284_ = stack[3].m_obj;
uint8_t v_usedLetOnly_1285_ = stack[4].m_num;
uint8_t v_skipConstInApp_1286_ = stack[5].m_num;
uint8_t v_skipInstances_1287_ = stack[6].m_num;
lean_object* v___y_1288_ = stack[7].m_obj;
lean_object* v___y_1289_ = stack[8].m_obj;
lean_object* v___y_1290_ = stack[9].m_obj;
lean_object* v___y_1291_ = stack[10].m_obj;
lean_object* v___y_1292_ = stack[11].m_obj;
lean_object* v_res_1361_;
v_res_1361_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(v___x_1281_, v_pre_1282_, v_e_1283_, v_post_1284_, v_usedLetOnly_1285_, v_skipConstInApp_1286_, v_skipInstances_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
stack->m_obj
 = v_res_1361_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed(lean_object* v___x_1362_, lean_object* v_pre_1363_, lean_object* v_e_1364_, lean_object* v_post_1365_, lean_object* v_usedLetOnly_1366_, lean_object* v_skipConstInApp_1367_, lean_object* v_skipInstances_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
uint8_t v_usedLetOnly_boxed_1375_; uint8_t v_skipConstInApp_boxed_1376_; uint8_t v_skipInstances_boxed_1377_; lean_object* v_res_1378_; 
v_usedLetOnly_boxed_1375_ = lean_unbox(v_usedLetOnly_1366_);
v_skipConstInApp_boxed_1376_ = lean_unbox(v_skipConstInApp_1367_);
v_skipInstances_boxed_1377_ = lean_unbox(v_skipInstances_1368_);
v_res_1378_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(v___x_1362_, v_pre_1363_, v_e_1364_, v_post_1365_, v_usedLetOnly_boxed_1375_, v_skipConstInApp_boxed_1376_, v_skipInstances_boxed_1377_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
return v_res_1378_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(lean_object* v_pre_1379_, lean_object* v_post_1380_, uint8_t v_usedLetOnly_1381_, uint8_t v_skipConstInApp_1382_, uint8_t v_skipInstances_1383_, lean_object* v_e_1384_, lean_object* v_a_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_inc(v_a_1385_);
v___x_1391_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1391_, 0, lean_box(0));
lean_closure_set(v___x_1391_, 1, lean_box(0));
lean_closure_set(v___x_1391_, 2, v_a_1385_);
v___x_1392_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___x_1391_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1427_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1395_ = v___x_1392_;
v_isShared_1396_ = v_isSharedCheck_1427_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1392_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1427_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_a_1393_, v_e_1384_);
lean_dec(v_a_1393_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___f_1402_; lean_object* v___x_1403_; 
lean_del_object(v___x_1395_);
v___x_1398_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0));
v___x_1399_ = lean_box(v_usedLetOnly_1381_);
v___x_1400_ = lean_box(v_skipConstInApp_1382_);
v___x_1401_ = lean_box(v_skipInstances_1383_);
lean_inc_ref(v_e_1384_);
v___f_1402_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed), 13, 7);
lean_closure_set(v___f_1402_, 0, v___x_1398_);
lean_closure_set(v___f_1402_, 1, v_pre_1379_);
lean_closure_set(v___f_1402_, 2, v_e_1384_);
lean_closure_set(v___f_1402_, 3, v_post_1380_);
lean_closure_set(v___f_1402_, 4, v___x_1399_);
lean_closure_set(v___f_1402_, 5, v___x_1400_);
lean_closure_set(v___f_1402_, 6, v___x_1401_);
v___x_1403_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v___f_1402_, v_a_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v___f_1405_; lean_object* v___x_1406_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc_n(v_a_1404_, 2);
lean_dec_ref_known(v___x_1403_, 1);
lean_inc(v_a_1385_);
v___f_1405_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1405_, 0, v_a_1385_);
lean_closure_set(v___f_1405_, 1, v_e_1384_);
lean_closure_set(v___f_1405_, 2, v_a_1404_);
v___x_1406_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___f_1405_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; 
v_unused_1414_ = lean_ctor_get(v___x_1406_, 0);
lean_dec(v_unused_1414_);
v___x_1408_ = v___x_1406_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_dec(v___x_1406_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v_a_1404_);
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1404_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec(v_a_1404_);
v_a_1415_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1406_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1406_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
else
{
lean_dec_ref(v_e_1384_);
return v___x_1403_;
}
}
else
{
lean_object* v_val_1423_; lean_object* v___x_1425_; 
lean_dec_ref(v_e_1384_);
lean_dec_ref(v_post_1380_);
lean_dec_ref(v_pre_1379_);
v_val_1423_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_val_1423_);
lean_dec_ref_known(v___x_1397_, 1);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v_val_1423_);
v___x_1425_ = v___x_1395_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_val_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec_ref(v_e_1384_);
lean_dec_ref(v_post_1380_);
lean_dec_ref(v_pre_1379_);
v_a_1428_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1392_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1392_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1379_ = stack[0].m_obj;
lean_object* v_post_1380_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1381_ = stack[2].m_num;
uint8_t v_skipConstInApp_1382_ = stack[3].m_num;
uint8_t v_skipInstances_1383_ = stack[4].m_num;
lean_object* v_e_1384_ = stack[5].m_obj;
lean_object* v_a_1385_ = stack[6].m_obj;
lean_object* v___y_1386_ = stack[7].m_obj;
lean_object* v___y_1387_ = stack[8].m_obj;
lean_object* v___y_1388_ = stack[9].m_obj;
lean_object* v___y_1389_ = stack[10].m_obj;
lean_object* v_res_1436_;
v_res_1436_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1379_, v_post_1380_, v_usedLetOnly_1381_, v_skipConstInApp_1382_, v_skipInstances_1383_, v_e_1384_, v_a_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
stack->m_obj
 = v_res_1436_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(lean_object* v_pre_1437_, lean_object* v_post_1438_, uint8_t v_usedLetOnly_1439_, uint8_t v_skipConstInApp_1440_, uint8_t v_skipInstances_1441_, lean_object* v_fvars_1442_, lean_object* v_e_1443_, lean_object* v_a_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
if (lean_obj_tag(v_e_1443_) == 7)
{
lean_object* v_binderName_1450_; lean_object* v_binderType_1451_; lean_object* v_body_1452_; uint8_t v_binderInfo_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___f_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_binderName_1450_ = lean_ctor_get(v_e_1443_, 0);
lean_inc(v_binderName_1450_);
v_binderType_1451_ = lean_ctor_get(v_e_1443_, 1);
lean_inc_ref(v_binderType_1451_);
v_body_1452_ = lean_ctor_get(v_e_1443_, 2);
lean_inc_ref(v_body_1452_);
v_binderInfo_1453_ = lean_ctor_get_uint8(v_e_1443_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1443_, 3);
v___x_1454_ = lean_box(v_usedLetOnly_1439_);
v___x_1455_ = lean_box(v_skipConstInApp_1440_);
v___x_1456_ = lean_box(v_skipInstances_1441_);
lean_inc_ref(v_post_1438_);
lean_inc_ref(v_pre_1437_);
lean_inc_ref(v_fvars_1442_);
v___f_1457_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1457_, 0, v_fvars_1442_);
lean_closure_set(v___f_1457_, 1, v_pre_1437_);
lean_closure_set(v___f_1457_, 2, v_post_1438_);
lean_closure_set(v___f_1457_, 3, v___x_1454_);
lean_closure_set(v___f_1457_, 4, v___x_1455_);
lean_closure_set(v___f_1457_, 5, v___x_1456_);
lean_closure_set(v___f_1457_, 6, v_body_1452_);
v___x_1458_ = lean_expr_instantiate_rev(v_binderType_1451_, v_fvars_1442_);
lean_dec_ref(v_fvars_1442_);
lean_dec_ref(v_binderType_1451_);
v___x_1459_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1437_, v_post_1438_, v_usedLetOnly_1439_, v_skipConstInApp_1440_, v_skipInstances_1441_, v___x_1458_, v_a_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; uint8_t v___x_1461_; lean_object* v___x_1462_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref_known(v___x_1459_, 1);
v___x_1461_ = 0;
v___x_1462_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_1450_, v_binderInfo_1453_, v_a_1460_, v___f_1457_, v___x_1461_, v_a_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1462_;
}
else
{
lean_dec_ref(v___f_1457_);
lean_dec(v_binderName_1450_);
return v___x_1459_;
}
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = lean_expr_instantiate_rev(v_e_1443_, v_fvars_1442_);
lean_dec_ref(v_e_1443_);
lean_inc_ref(v_post_1438_);
lean_inc_ref(v_pre_1437_);
v___x_1464_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1437_, v_post_1438_, v_usedLetOnly_1439_, v_skipConstInApp_1440_, v_skipInstances_1441_, v___x_1463_, v_a_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; uint8_t v___x_1466_; uint8_t v___x_1467_; uint8_t v___x_1468_; lean_object* v___x_1469_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1465_);
lean_dec_ref_known(v___x_1464_, 1);
v___x_1466_ = 0;
v___x_1467_ = 1;
v___x_1468_ = 1;
v___x_1469_ = l_Lean_Meta_mkForallFVars(v_fvars_1442_, v_a_1465_, v___x_1466_, v_usedLetOnly_1439_, v___x_1467_, v___x_1468_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec_ref(v_fvars_1442_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1471_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref_known(v___x_1469_, 1);
v___x_1471_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1437_, v_post_1438_, v_usedLetOnly_1439_, v_skipConstInApp_1440_, v_skipInstances_1441_, v_a_1470_, v_a_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1471_;
}
else
{
lean_dec_ref(v_post_1438_);
lean_dec_ref(v_pre_1437_);
return v___x_1469_;
}
}
else
{
lean_dec_ref(v_fvars_1442_);
lean_dec_ref(v_post_1438_);
lean_dec_ref(v_pre_1437_);
return v___x_1464_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1437_ = stack[0].m_obj;
lean_object* v_post_1438_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1439_ = stack[2].m_num;
uint8_t v_skipConstInApp_1440_ = stack[3].m_num;
uint8_t v_skipInstances_1441_ = stack[4].m_num;
lean_object* v_fvars_1442_ = stack[5].m_obj;
lean_object* v_e_1443_ = stack[6].m_obj;
lean_object* v_a_1444_ = stack[7].m_obj;
lean_object* v___y_1445_ = stack[8].m_obj;
lean_object* v___y_1446_ = stack[9].m_obj;
lean_object* v___y_1447_ = stack[10].m_obj;
lean_object* v___y_1448_ = stack[11].m_obj;
lean_object* v_res_1472_;
v_res_1472_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1437_, v_post_1438_, v_usedLetOnly_1439_, v_skipConstInApp_1440_, v_skipInstances_1441_, v_fvars_1442_, v_e_1443_, v_a_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
stack->m_obj
 = v_res_1472_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(lean_object* v_fvars_1473_, lean_object* v_pre_1474_, lean_object* v_post_1475_, uint8_t v_usedLetOnly_1476_, uint8_t v_skipConstInApp_1477_, uint8_t v_skipInstances_1478_, lean_object* v_body_1479_, lean_object* v_x_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = lean_array_push(v_fvars_1473_, v_x_1480_);
v___x_1488_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1474_, v_post_1475_, v_usedLetOnly_1476_, v_skipConstInApp_1477_, v_skipInstances_1478_, v___x_1487_, v_body_1479_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
return v___x_1488_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1473_ = stack[0].m_obj;
lean_object* v_pre_1474_ = stack[1].m_obj;
lean_object* v_post_1475_ = stack[2].m_obj;
uint8_t v_usedLetOnly_1476_ = stack[3].m_num;
uint8_t v_skipConstInApp_1477_ = stack[4].m_num;
uint8_t v_skipInstances_1478_ = stack[5].m_num;
lean_object* v_body_1479_ = stack[6].m_obj;
lean_object* v_x_1480_ = stack[7].m_obj;
lean_object* v___y_1481_ = stack[8].m_obj;
lean_object* v___y_1482_ = stack[9].m_obj;
lean_object* v___y_1483_ = stack[10].m_obj;
lean_object* v___y_1484_ = stack[11].m_obj;
lean_object* v___y_1485_ = stack[12].m_obj;
lean_object* v_res_1489_;
v_res_1489_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(v_fvars_1473_, v_pre_1474_, v_post_1475_, v_usedLetOnly_1476_, v_skipConstInApp_1477_, v_skipInstances_1478_, v_body_1479_, v_x_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
stack->m_obj
 = v_res_1489_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7___boxed(lean_object* v_pre_1490_, lean_object* v_post_1491_, lean_object* v_usedLetOnly_1492_, lean_object* v_skipConstInApp_1493_, lean_object* v_skipInstances_1494_, lean_object* v_e_1495_, lean_object* v_a_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
uint8_t v_usedLetOnly_boxed_1502_; uint8_t v_skipConstInApp_boxed_1503_; uint8_t v_skipInstances_boxed_1504_; lean_object* v_res_1505_; 
v_usedLetOnly_boxed_1502_ = lean_unbox(v_usedLetOnly_1492_);
v_skipConstInApp_boxed_1503_ = lean_unbox(v_skipConstInApp_1493_);
v_skipInstances_boxed_1504_ = lean_unbox(v_skipInstances_1494_);
v_res_1505_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1490_, v_post_1491_, v_usedLetOnly_boxed_1502_, v_skipConstInApp_boxed_1503_, v_skipInstances_boxed_1504_, v_e_1495_, v_a_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v_a_1496_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___boxed(lean_object* v_pre_1506_, lean_object* v_post_1507_, lean_object* v_usedLetOnly_1508_, lean_object* v_skipConstInApp_1509_, lean_object* v_skipInstances_1510_, lean_object* v_sz_1511_, lean_object* v_i_1512_, lean_object* v_bs_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
uint8_t v_usedLetOnly_boxed_1520_; uint8_t v_skipConstInApp_boxed_1521_; uint8_t v_skipInstances_boxed_1522_; size_t v_sz_boxed_1523_; size_t v_i_boxed_1524_; lean_object* v_res_1525_; 
v_usedLetOnly_boxed_1520_ = lean_unbox(v_usedLetOnly_1508_);
v_skipConstInApp_boxed_1521_ = lean_unbox(v_skipConstInApp_1509_);
v_skipInstances_boxed_1522_ = lean_unbox(v_skipInstances_1510_);
v_sz_boxed_1523_ = lean_unbox_usize(v_sz_1511_);
lean_dec(v_sz_1511_);
v_i_boxed_1524_ = lean_unbox_usize(v_i_1512_);
lean_dec(v_i_1512_);
v_res_1525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_1506_, v_post_1507_, v_usedLetOnly_boxed_1520_, v_skipConstInApp_boxed_1521_, v_skipInstances_boxed_1522_, v_sz_boxed_1523_, v_i_boxed_1524_, v_bs_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___boxed(lean_object* v_pre_1526_, lean_object* v_post_1527_, lean_object* v_usedLetOnly_1528_, lean_object* v_skipConstInApp_1529_, lean_object* v_skipInstances_1530_, lean_object* v_e_1531_, lean_object* v_a_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
uint8_t v_usedLetOnly_boxed_1538_; uint8_t v_skipConstInApp_boxed_1539_; uint8_t v_skipInstances_boxed_1540_; lean_object* v_res_1541_; 
v_usedLetOnly_boxed_1538_ = lean_unbox(v_usedLetOnly_1528_);
v_skipConstInApp_boxed_1539_ = lean_unbox(v_skipConstInApp_1529_);
v_skipInstances_boxed_1540_ = lean_unbox(v_skipInstances_1530_);
v_res_1541_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1526_, v_post_1527_, v_usedLetOnly_boxed_1538_, v_skipConstInApp_boxed_1539_, v_skipInstances_boxed_1540_, v_e_1531_, v_a_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v_a_1532_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___boxed(lean_object* v_pre_1542_, lean_object* v_post_1543_, lean_object* v_usedLetOnly_1544_, lean_object* v_skipConstInApp_1545_, lean_object* v_skipInstances_1546_, lean_object* v_fvars_1547_, lean_object* v_e_1548_, lean_object* v_a_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
uint8_t v_usedLetOnly_boxed_1555_; uint8_t v_skipConstInApp_boxed_1556_; uint8_t v_skipInstances_boxed_1557_; lean_object* v_res_1558_; 
v_usedLetOnly_boxed_1555_ = lean_unbox(v_usedLetOnly_1544_);
v_skipConstInApp_boxed_1556_ = lean_unbox(v_skipConstInApp_1545_);
v_skipInstances_boxed_1557_ = lean_unbox(v_skipInstances_1546_);
v_res_1558_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1542_, v_post_1543_, v_usedLetOnly_boxed_1555_, v_skipConstInApp_boxed_1556_, v_skipInstances_boxed_1557_, v_fvars_1547_, v_e_1548_, v_a_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v_a_1549_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___boxed(lean_object* v_pre_1559_, lean_object* v_post_1560_, lean_object* v_usedLetOnly_1561_, lean_object* v_skipConstInApp_1562_, lean_object* v_skipInstances_1563_, lean_object* v_fvars_1564_, lean_object* v_e_1565_, lean_object* v_a_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
uint8_t v_usedLetOnly_boxed_1572_; uint8_t v_skipConstInApp_boxed_1573_; uint8_t v_skipInstances_boxed_1574_; lean_object* v_res_1575_; 
v_usedLetOnly_boxed_1572_ = lean_unbox(v_usedLetOnly_1561_);
v_skipConstInApp_boxed_1573_ = lean_unbox(v_skipConstInApp_1562_);
v_skipInstances_boxed_1574_ = lean_unbox(v_skipInstances_1563_);
v_res_1575_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1559_, v_post_1560_, v_usedLetOnly_boxed_1572_, v_skipConstInApp_boxed_1573_, v_skipInstances_boxed_1574_, v_fvars_1564_, v_e_1565_, v_a_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v_a_1566_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___boxed(lean_object* v_pre_1576_, lean_object* v_post_1577_, lean_object* v_usedLetOnly_1578_, lean_object* v_skipConstInApp_1579_, lean_object* v_skipInstances_1580_, lean_object* v_fvars_1581_, lean_object* v_e_1582_, lean_object* v_a_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
uint8_t v_usedLetOnly_boxed_1589_; uint8_t v_skipConstInApp_boxed_1590_; uint8_t v_skipInstances_boxed_1591_; lean_object* v_res_1592_; 
v_usedLetOnly_boxed_1589_ = lean_unbox(v_usedLetOnly_1578_);
v_skipConstInApp_boxed_1590_ = lean_unbox(v_skipConstInApp_1579_);
v_skipInstances_boxed_1591_ = lean_unbox(v_skipInstances_1580_);
v_res_1592_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1576_, v_post_1577_, v_usedLetOnly_boxed_1589_, v_skipConstInApp_boxed_1590_, v_skipInstances_boxed_1591_, v_fvars_1581_, v_e_1582_, v_a_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v_a_1583_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___boxed(lean_object* v_upperBound_1593_, lean_object* v___x_1594_, lean_object* v_pre_1595_, lean_object* v_post_1596_, lean_object* v_usedLetOnly_1597_, lean_object* v_skipConstInApp_1598_, lean_object* v_skipInstances_1599_, lean_object* v_a_1600_, lean_object* v_b_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
uint8_t v_usedLetOnly_boxed_1608_; uint8_t v_skipConstInApp_boxed_1609_; uint8_t v_skipInstances_boxed_1610_; lean_object* v_res_1611_; 
v_usedLetOnly_boxed_1608_ = lean_unbox(v_usedLetOnly_1597_);
v_skipConstInApp_boxed_1609_ = lean_unbox(v_skipConstInApp_1598_);
v_skipInstances_boxed_1610_ = lean_unbox(v_skipInstances_1599_);
v_res_1611_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_1593_, v___x_1594_, v_pre_1595_, v_post_1596_, v_usedLetOnly_boxed_1608_, v_skipConstInApp_boxed_1609_, v_skipInstances_boxed_1610_, v_a_1600_, v_b_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___x_1594_);
lean_dec(v_upperBound_1593_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13___boxed(lean_object* v_skipInstances_1612_, lean_object* v_pre_1613_, lean_object* v_post_1614_, lean_object* v_usedLetOnly_1615_, lean_object* v_skipConstInApp_1616_, lean_object* v_x_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
uint8_t v_skipInstances_boxed_1626_; uint8_t v_usedLetOnly_boxed_1627_; uint8_t v_skipConstInApp_boxed_1628_; lean_object* v_res_1629_; 
v_skipInstances_boxed_1626_ = lean_unbox(v_skipInstances_1612_);
v_usedLetOnly_boxed_1627_ = lean_unbox(v_usedLetOnly_1615_);
v_skipConstInApp_boxed_1628_ = lean_unbox(v_skipConstInApp_1616_);
v_res_1629_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_boxed_1626_, v_pre_1613_, v_post_1614_, v_usedLetOnly_boxed_1627_, v_skipConstInApp_boxed_1628_, v_x_1617_, v_x_1618_, v_x_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
return v_res_1629_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = lean_box(0);
v___x_1631_ = lean_unsigned_to_nat(16u);
v___x_1632_ = lean_mk_array(v___x_1631_, v___x_1630_);
return v___x_1632_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1633_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0);
v___x_1634_ = lean_unsigned_to_nat(0u);
v___x_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
lean_ctor_set(v___x_1635_, 1, v___x_1633_);
return v___x_1635_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1);
v___x_1637_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1637_, 0, lean_box(0));
lean_closure_set(v___x_1637_, 1, lean_box(0));
lean_closure_set(v___x_1637_, 2, v___x_1636_);
return v___x_1637_;
}
}
lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(lean_object* v_input_1638_, lean_object* v_pre_1639_, lean_object* v_post_1640_, uint8_t v_usedLetOnly_1641_, uint8_t v_skipConstInApp_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
uint8_t v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v_a_1651_; lean_object* v___x_1652_; 
v___x_1648_ = 0;
v___x_1649_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2);
v___x_1650_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1649_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref(v___x_1650_);
v___x_1652_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1639_, v_post_1640_, v_usedLetOnly_1641_, v_skipConstInApp_1642_, v___x_1648_, v_input_1638_, v_a_1651_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref_known(v___x_1652_, 1);
v___x_1654_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1654_, 0, lean_box(0));
lean_closure_set(v___x_1654_, 1, lean_box(0));
lean_closure_set(v___x_1654_, 2, v_a_1651_);
v___x_1655_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1654_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1662_ == 0)
{
lean_object* v_unused_1663_; 
v_unused_1663_ = lean_ctor_get(v___x_1655_, 0);
lean_dec(v_unused_1663_);
v___x_1657_ = v___x_1655_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_dec(v___x_1655_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v_a_1653_);
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1653_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
else
{
lean_dec(v_a_1651_);
return v___x_1652_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_1638_ = stack[0].m_obj;
lean_object* v_pre_1639_ = stack[1].m_obj;
lean_object* v_post_1640_ = stack[2].m_obj;
uint8_t v_usedLetOnly_1641_ = stack[3].m_num;
uint8_t v_skipConstInApp_1642_ = stack[4].m_num;
lean_object* v___y_1643_ = stack[5].m_obj;
lean_object* v___y_1644_ = stack[6].m_obj;
lean_object* v___y_1645_ = stack[7].m_obj;
lean_object* v___y_1646_ = stack[8].m_obj;
lean_object* v_res_1664_;
v_res_1664_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_input_1638_, v_pre_1639_, v_post_1640_, v_usedLetOnly_1641_, v_skipConstInApp_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
stack->m_obj
 = v_res_1664_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___boxed(lean_object* v_input_1665_, lean_object* v_pre_1666_, lean_object* v_post_1667_, lean_object* v_usedLetOnly_1668_, lean_object* v_skipConstInApp_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
uint8_t v_usedLetOnly_boxed_1675_; uint8_t v_skipConstInApp_boxed_1676_; lean_object* v_res_1677_; 
v_usedLetOnly_boxed_1675_ = lean_unbox(v_usedLetOnly_1668_);
v_skipConstInApp_boxed_1676_ = lean_unbox(v_skipConstInApp_1669_);
v_res_1677_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_input_1665_, v_pre_1666_, v_post_1667_, v_usedLetOnly_boxed_1675_, v_skipConstInApp_boxed_1676_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
return v_res_1677_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__1(void){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Array_instInhabited___redArg();
return v___x_1679_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__3(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__2));
v___x_1682_ = l_Lean_stringToMessageData(v___x_1681_);
return v___x_1682_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__5(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__4));
v___x_1685_ = l_Lean_stringToMessageData(v___x_1684_);
return v___x_1685_;
}
}
lean_object* l_Lean_Elab_WF_packCalls(lean_object* v_fixedParamPerms_1686_, lean_object* v_argsPacker_1687_, lean_object* v_funNames_1688_, lean_object* v_newF_1689_, lean_object* v_e_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_){
_start:
{
lean_object* v___f_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___f_1696_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__0));
v___x_1697_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
lean_inc(v_a_1694_);
lean_inc_ref(v_a_1693_);
lean_inc(v_a_1692_);
lean_inc_ref(v_a_1691_);
lean_inc_ref(v_newF_1689_);
v___x_1698_ = lean_infer_type(v_newF_1689_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; uint8_t v___x_1710_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1698_, 1);
v___x_1710_ = l_Lean_Expr_isForall(v_a_1699_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec_ref(v_e_1690_);
lean_dec_ref(v_funNames_1688_);
lean_dec_ref(v_argsPacker_1687_);
lean_dec_ref(v_fixedParamPerms_1686_);
v___x_1711_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__3, &l_Lean_Elab_WF_packCalls___closed__3_once, _init_l_Lean_Elab_WF_packCalls___closed__3);
v___x_1712_ = l_Lean_MessageData_ofExpr(v_newF_1689_);
v___x_1713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1711_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
v___x_1714_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__5, &l_Lean_Elab_WF_packCalls___closed__5_once, _init_l_Lean_Elab_WF_packCalls___closed__5);
v___x_1715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1713_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = l_Lean_MessageData_ofExpr(v_a_1699_);
v___x_1717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v___x_1717_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
else
{
v___y_1701_ = v_a_1691_;
v___y_1702_ = v_a_1692_;
v___y_1703_ = v_a_1693_;
v___y_1704_ = v_a_1694_;
goto v___jp_1700_;
}
v___jp_1700_:
{
lean_object* v___x_1705_; lean_object* v___f_1706_; uint8_t v___x_1707_; uint8_t v___x_1708_; lean_object* v___x_1709_; 
v___x_1705_ = l_Lean_Expr_bindingDomain_x21(v_a_1699_);
lean_dec(v_a_1699_);
v___f_1706_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packCalls___lam__2___boxed), 12, 6);
lean_closure_set(v___f_1706_, 0, v_funNames_1688_);
lean_closure_set(v___f_1706_, 1, v_fixedParamPerms_1686_);
lean_closure_set(v___f_1706_, 2, v___x_1697_);
lean_closure_set(v___f_1706_, 3, v_argsPacker_1687_);
lean_closure_set(v___f_1706_, 4, v___x_1705_);
lean_closure_set(v___f_1706_, 5, v_newF_1689_);
v___x_1707_ = 0;
v___x_1708_ = 1;
v___x_1709_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_e_1690_, v___f_1696_, v___f_1706_, v___x_1707_, v___x_1708_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
return v___x_1709_;
}
}
else
{
lean_dec_ref(v_e_1690_);
lean_dec_ref(v_newF_1689_);
lean_dec_ref(v_funNames_1688_);
lean_dec_ref(v_argsPacker_1687_);
lean_dec_ref(v_fixedParamPerms_1686_);
return v___x_1698_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_WF_packCalls_0interp(lean_interpreter_value* stack)
{
lean_object* v_fixedParamPerms_1686_ = stack[0].m_obj;
lean_object* v_argsPacker_1687_ = stack[1].m_obj;
lean_object* v_funNames_1688_ = stack[2].m_obj;
lean_object* v_newF_1689_ = stack[3].m_obj;
lean_object* v_e_1690_ = stack[4].m_obj;
lean_object* v_a_1691_ = stack[5].m_obj;
lean_object* v_a_1692_ = stack[6].m_obj;
lean_object* v_a_1693_ = stack[7].m_obj;
lean_object* v_a_1694_ = stack[8].m_obj;
lean_object* v_res_1727_;
v_res_1727_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_1686_, v_argsPacker_1687_, v_funNames_1688_, v_newF_1689_, v_e_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
stack->m_obj
 = v_res_1727_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___boxed(lean_object* v_fixedParamPerms_1728_, lean_object* v_argsPacker_1729_, lean_object* v_funNames_1730_, lean_object* v_newF_1731_, lean_object* v_e_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_1728_, v_argsPacker_1729_, v_funNames_1730_, v_newF_1731_, v_e_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
return v_res_1738_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(lean_object* v_upperBound_1739_, lean_object* v___x_1740_, lean_object* v_pre_1741_, lean_object* v_post_1742_, uint8_t v_usedLetOnly_1743_, uint8_t v_skipConstInApp_1744_, uint8_t v_skipInstances_1745_, lean_object* v___x_1746_, lean_object* v_inst_1747_, lean_object* v_R_1748_, lean_object* v_a_1749_, lean_object* v_b_1750_, lean_object* v_c_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_1739_, v___x_1740_, v_pre_1741_, v_post_1742_, v_usedLetOnly_1743_, v_skipConstInApp_1744_, v_skipInstances_1745_, v_a_1749_, v_b_1750_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
return v___x_1758_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1739_ = stack[0].m_obj;
lean_object* v___x_1740_ = stack[1].m_obj;
lean_object* v_pre_1741_ = stack[2].m_obj;
lean_object* v_post_1742_ = stack[3].m_obj;
uint8_t v_usedLetOnly_1743_ = stack[4].m_num;
uint8_t v_skipConstInApp_1744_ = stack[5].m_num;
uint8_t v_skipInstances_1745_ = stack[6].m_num;
lean_object* v___x_1746_ = stack[7].m_obj;
lean_object* v_a_1749_ = stack[10].m_obj;
lean_object* v_b_1750_ = stack[11].m_obj;
lean_object* v___y_1752_ = stack[13].m_obj;
lean_object* v___y_1753_ = stack[14].m_obj;
lean_object* v___y_1754_ = stack[15].m_obj;
lean_object* v___y_1755_ = stack[16].m_obj;
lean_object* v___y_1756_ = stack[17].m_obj;
lean_object* v_res_1759_;
v_res_1759_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_upperBound_1739_, v___x_1740_, v_pre_1741_, v_post_1742_, v_usedLetOnly_1743_, v_skipConstInApp_1744_, v_skipInstances_1745_, v___x_1746_, lean_box(0), lean_box(0), v_a_1749_, v_b_1750_, lean_box(0), v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
stack->m_obj
 = v_res_1759_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1760_ = _args[0];
lean_object* v___x_1761_ = _args[1];
lean_object* v_pre_1762_ = _args[2];
lean_object* v_post_1763_ = _args[3];
lean_object* v_usedLetOnly_1764_ = _args[4];
lean_object* v_skipConstInApp_1765_ = _args[5];
lean_object* v_skipInstances_1766_ = _args[6];
lean_object* v___x_1767_ = _args[7];
lean_object* v_inst_1768_ = _args[8];
lean_object* v_R_1769_ = _args[9];
lean_object* v_a_1770_ = _args[10];
lean_object* v_b_1771_ = _args[11];
lean_object* v_c_1772_ = _args[12];
lean_object* v___y_1773_ = _args[13];
lean_object* v___y_1774_ = _args[14];
lean_object* v___y_1775_ = _args[15];
lean_object* v___y_1776_ = _args[16];
lean_object* v___y_1777_ = _args[17];
lean_object* v___y_1778_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_1779_; uint8_t v_skipConstInApp_boxed_1780_; uint8_t v_skipInstances_boxed_1781_; lean_object* v_res_1782_; 
v_usedLetOnly_boxed_1779_ = lean_unbox(v_usedLetOnly_1764_);
v_skipConstInApp_boxed_1780_ = lean_unbox(v_skipConstInApp_1765_);
v_skipInstances_boxed_1781_ = lean_unbox(v_skipInstances_1766_);
v_res_1782_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_upperBound_1760_, v___x_1761_, v_pre_1762_, v_post_1763_, v_usedLetOnly_boxed_1779_, v_skipConstInApp_boxed_1780_, v_skipInstances_boxed_1781_, v___x_1767_, v_inst_1768_, v_R_1769_, v_a_1770_, v_b_1771_, v_c_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec(v___x_1767_);
lean_dec_ref(v___x_1761_);
lean_dec(v_upperBound_1760_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1783_, lean_object* v_m_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_m_1784_, v_a_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___boxed(lean_object* v_00_u03b2_1787_, lean_object* v_m_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(v_00_u03b2_1787_, v_m_1788_, v_a_1789_);
lean_dec_ref(v_a_1789_);
lean_dec_ref(v_m_1788_);
return v_res_1790_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_1791_, lean_object* v_name_1792_, uint8_t v_bi_1793_, lean_object* v_type_1794_, lean_object* v_k_1795_, uint8_t v_kind_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_1792_, v_bi_1793_, v_type_1794_, v_k_1795_, v_kind_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
return v___x_1803_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1792_ = stack[1].m_obj;
uint8_t v_bi_1793_ = stack[2].m_num;
lean_object* v_type_1794_ = stack[3].m_obj;
lean_object* v_k_1795_ = stack[4].m_obj;
uint8_t v_kind_1796_ = stack[5].m_num;
lean_object* v___y_1797_ = stack[6].m_obj;
lean_object* v___y_1798_ = stack[7].m_obj;
lean_object* v___y_1799_ = stack[8].m_obj;
lean_object* v___y_1800_ = stack[9].m_obj;
lean_object* v___y_1801_ = stack[10].m_obj;
lean_object* v_res_1804_;
v_res_1804_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(lean_box(0), v_name_1792_, v_bi_1793_, v_type_1794_, v_k_1795_, v_kind_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
stack->m_obj
 = v_res_1804_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_1805_, lean_object* v_name_1806_, lean_object* v_bi_1807_, lean_object* v_type_1808_, lean_object* v_k_1809_, lean_object* v_kind_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
uint8_t v_bi_boxed_1817_; uint8_t v_kind_boxed_1818_; lean_object* v_res_1819_; 
v_bi_boxed_1817_ = lean_unbox(v_bi_1807_);
v_kind_boxed_1818_ = lean_unbox(v_kind_1810_);
v_res_1819_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(v_00_u03b1_1805_, v_name_1806_, v_bi_boxed_1817_, v_type_1808_, v_k_1809_, v_kind_boxed_1818_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
return v_res_1819_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(lean_object* v_00_u03b1_1820_, lean_object* v_name_1821_, lean_object* v_type_1822_, lean_object* v_val_1823_, lean_object* v_k_1824_, uint8_t v_nondep_1825_, uint8_t v_kind_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_1821_, v_type_1822_, v_val_1823_, v_k_1824_, v_nondep_1825_, v_kind_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
return v___x_1833_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1821_ = stack[1].m_obj;
lean_object* v_type_1822_ = stack[2].m_obj;
lean_object* v_val_1823_ = stack[3].m_obj;
lean_object* v_k_1824_ = stack[4].m_obj;
uint8_t v_nondep_1825_ = stack[5].m_num;
uint8_t v_kind_1826_ = stack[6].m_num;
lean_object* v___y_1827_ = stack[7].m_obj;
lean_object* v___y_1828_ = stack[8].m_obj;
lean_object* v___y_1829_ = stack[9].m_obj;
lean_object* v___y_1830_ = stack[10].m_obj;
lean_object* v___y_1831_ = stack[11].m_obj;
lean_object* v_res_1834_;
v_res_1834_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(lean_box(0), v_name_1821_, v_type_1822_, v_val_1823_, v_k_1824_, v_nondep_1825_, v_kind_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
stack->m_obj
 = v_res_1834_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___boxed(lean_object* v_00_u03b1_1835_, lean_object* v_name_1836_, lean_object* v_type_1837_, lean_object* v_val_1838_, lean_object* v_k_1839_, lean_object* v_nondep_1840_, lean_object* v_kind_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
uint8_t v_nondep_boxed_1848_; uint8_t v_kind_boxed_1849_; lean_object* v_res_1850_; 
v_nondep_boxed_1848_ = lean_unbox(v_nondep_1840_);
v_kind_boxed_1849_ = lean_unbox(v_kind_1841_);
v_res_1850_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(v_00_u03b1_1835_, v_name_1836_, v_type_1837_, v_val_1838_, v_k_1839_, v_nondep_boxed_1848_, v_kind_boxed_1849_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
return v_res_1850_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(lean_object* v_00_u03b1_1851_, lean_object* v_ref_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_1852_);
return v___x_1858_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1852_ = stack[1].m_obj;
lean_object* v___y_1853_ = stack[2].m_obj;
lean_object* v___y_1854_ = stack[3].m_obj;
lean_object* v___y_1855_ = stack[4].m_obj;
lean_object* v___y_1856_ = stack[5].m_obj;
lean_object* v_res_1859_;
v_res_1859_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(lean_box(0), v_ref_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
stack->m_obj
 = v_res_1859_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___boxed(lean_object* v_00_u03b1_1860_, lean_object* v_ref_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(v_00_u03b1_1860_, v_ref_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
return v_res_1867_;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(lean_object* v_00_u03b1_1868_, lean_object* v_x_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
return v___x_1876_;
}
}
LEAN_EXPORT void l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1869_ = stack[1].m_obj;
lean_object* v___y_1870_ = stack[2].m_obj;
lean_object* v___y_1871_ = stack[3].m_obj;
lean_object* v___y_1872_ = stack[4].m_obj;
lean_object* v___y_1873_ = stack[5].m_obj;
lean_object* v___y_1874_ = stack[6].m_obj;
lean_object* v_res_1877_;
v_res_1877_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(lean_box(0), v_x_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
stack->m_obj
 = v_res_1877_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___boxed(lean_object* v_00_u03b1_1878_, lean_object* v_x_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(v_00_u03b1_1878_, v_x_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15(lean_object* v_00_u03b2_1887_, lean_object* v_m_1888_, lean_object* v_a_1889_, lean_object* v_b_1890_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v_m_1888_, v_a_1889_, v_b_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(lean_object* v_00_u03b2_1892_, lean_object* v_a_1893_, lean_object* v_x_1894_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_1893_, v_x_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___boxed(lean_object* v_00_u03b2_1896_, lean_object* v_a_1897_, lean_object* v_x_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(v_00_u03b2_1896_, v_a_1897_, v_x_1898_);
lean_dec(v_x_1898_);
lean_dec_ref(v_a_1897_);
return v_res_1899_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(lean_object* v_00_u03b2_1900_, lean_object* v_a_1901_, lean_object* v_x_1902_){
_start:
{
uint8_t v___x_1903_; 
v___x_1903_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_1901_, v_x_1902_);
return v___x_1903_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1901_ = stack[1].m_obj;
lean_object* v_x_1902_ = stack[2].m_obj;
uint8_t v_res_1904_;
v_res_1904_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(lean_box(0), v_a_1901_, v_x_1902_);
stack->m_num = v_res_1904_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___boxed(lean_object* v_00_u03b2_1905_, lean_object* v_a_1906_, lean_object* v_x_1907_){
_start:
{
uint8_t v_res_1908_; lean_object* v_r_1909_; 
v_res_1908_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(v_00_u03b2_1905_, v_a_1906_, v_x_1907_);
lean_dec(v_x_1907_);
lean_dec_ref(v_a_1906_);
v_r_1909_ = lean_box(v_res_1908_);
return v_r_1909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21(lean_object* v_00_u03b2_1910_, lean_object* v_data_1911_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_data_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22(lean_object* v_00_u03b2_1913_, lean_object* v_a_1914_, lean_object* v_b_1915_, lean_object* v_x_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_1914_, v_b_1915_, v_x_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22(lean_object* v_00_u03b2_1918_, lean_object* v_i_1919_, lean_object* v_source_1920_, lean_object* v_target_1921_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v_i_1919_, v_source_1920_, v_target_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23(lean_object* v_00_u03b2_1923_, lean_object* v_x_1924_, lean_object* v_x_1925_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(v_x_1924_, v_x_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName(lean_object* v_fixedParamPerms_1933_, lean_object* v_argsPacker_1934_, lean_object* v_preDefs_1935_){
_start:
{
lean_object* v___x_1936_; uint8_t v___y_1938_; uint8_t v___x_1955_; 
v___x_1936_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1955_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_1933_);
if (v___x_1955_ == 0)
{
v___y_1938_ = v___x_1955_;
goto v___jp_1937_;
}
else
{
uint8_t v___x_1956_; 
v___x_1956_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_1934_);
v___y_1938_ = v___x_1956_;
goto v___jp_1937_;
}
v___jp_1937_:
{
if (v___y_1938_ == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; 
v___x_1939_ = lean_unsigned_to_nat(1u);
v___x_1940_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_1934_);
v___x_1941_ = lean_nat_dec_lt(v___x_1939_, v___x_1940_);
lean_dec(v___x_1940_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v_declName_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1942_ = lean_unsigned_to_nat(0u);
v___x_1943_ = lean_array_get_borrowed(v___x_1936_, v_preDefs_1935_, v___x_1942_);
v_declName_1944_ = lean_ctor_get(v___x_1943_, 3);
v___x_1945_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__1));
lean_inc(v_declName_1944_);
v___x_1946_ = l_Lean_Name_append(v_declName_1944_, v___x_1945_);
return v___x_1946_;
}
else
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v_declName_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1947_ = lean_unsigned_to_nat(0u);
v___x_1948_ = lean_array_get_borrowed(v___x_1936_, v_preDefs_1935_, v___x_1947_);
v_declName_1949_ = lean_ctor_get(v___x_1948_, 3);
v___x_1950_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__3));
lean_inc(v_declName_1949_);
v___x_1951_ = l_Lean_Name_append(v_declName_1949_, v___x_1950_);
return v___x_1951_;
}
}
else
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v_declName_1954_; 
v___x_1952_ = lean_unsigned_to_nat(0u);
v___x_1953_ = lean_array_get_borrowed(v___x_1936_, v_preDefs_1935_, v___x_1952_);
v_declName_1954_ = lean_ctor_get(v___x_1953_, 3);
lean_inc(v_declName_1954_);
return v_declName_1954_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName___boxed(lean_object* v_fixedParamPerms_1957_, lean_object* v_argsPacker_1958_, lean_object* v_preDefs_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_1957_, v_argsPacker_1958_, v_preDefs_1959_);
lean_dec_ref(v_preDefs_1959_);
lean_dec_ref(v_argsPacker_1958_);
return v_res_1960_;
}
}
lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(lean_object* v_k_1961_, lean_object* v_b_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v___x_1968_; 
lean_inc(v___y_1966_);
lean_inc_ref(v___y_1965_);
lean_inc(v___y_1964_);
lean_inc_ref(v___y_1963_);
v___x_1968_ = lean_apply_6(v_k_1961_, v_b_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, lean_box(0));
return v___x_1968_;
}
}
LEAN_EXPORT void l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1961_ = stack[0].m_obj;
lean_object* v_b_1962_ = stack[1].m_obj;
lean_object* v___y_1963_ = stack[2].m_obj;
lean_object* v___y_1964_ = stack[3].m_obj;
lean_object* v___y_1965_ = stack[4].m_obj;
lean_object* v___y_1966_ = stack[5].m_obj;
lean_object* v_res_1969_;
v_res_1969_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(v_k_1961_, v_b_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
stack->m_obj
 = v_res_1969_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed(lean_object* v_k_1970_, lean_object* v_b_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(v_k_1970_, v_b_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
return v_res_1977_;
}
}
lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(lean_object* v_perm_1978_, lean_object* v_type_1979_, lean_object* v_k_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v___f_1986_; lean_object* v___x_1987_; 
v___f_1986_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1986_, 0, v_k_1980_);
v___x_1987_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_1978_, v_type_1979_, v___f_1986_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1987_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
v_a_1996_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1987_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1987_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
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
LEAN_EXPORT void l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_perm_1978_ = stack[0].m_obj;
lean_object* v_type_1979_ = stack[1].m_obj;
lean_object* v_k_1980_ = stack[2].m_obj;
lean_object* v___y_1981_ = stack[3].m_obj;
lean_object* v___y_1982_ = stack[4].m_obj;
lean_object* v___y_1983_ = stack[5].m_obj;
lean_object* v___y_1984_ = stack[6].m_obj;
lean_object* v_res_2004_;
v_res_2004_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_1978_, v_type_1979_, v_k_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
stack->m_obj
 = v_res_2004_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___boxed(lean_object* v_perm_2005_, lean_object* v_type_2006_, lean_object* v_k_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_2005_, v_type_2006_, v_k_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
return v_res_2013_;
}
}
lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(lean_object* v_00_u03b1_2014_, lean_object* v_perm_2015_, lean_object* v_type_2016_, lean_object* v_k_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_2015_, v_type_2016_, v_k_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
return v___x_2023_;
}
}
LEAN_EXPORT void l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_perm_2015_ = stack[1].m_obj;
lean_object* v_type_2016_ = stack[2].m_obj;
lean_object* v_k_2017_ = stack[3].m_obj;
lean_object* v___y_2018_ = stack[4].m_obj;
lean_object* v___y_2019_ = stack[5].m_obj;
lean_object* v___y_2020_ = stack[6].m_obj;
lean_object* v___y_2021_ = stack[7].m_obj;
lean_object* v_res_2024_;
v_res_2024_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(lean_box(0), v_perm_2015_, v_type_2016_, v_k_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
stack->m_obj
 = v_res_2024_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___boxed(lean_object* v_00_u03b1_2025_, lean_object* v_perm_2026_, lean_object* v_type_2027_, lean_object* v_k_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(v_00_u03b1_2025_, v_perm_2026_, v_type_2027_, v_k_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
return v_res_2034_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(lean_object* v___x_2035_, lean_object* v_ys_2036_, size_t v_sz_2037_, size_t v_i_2038_, lean_object* v_bs_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
uint8_t v___x_2045_; 
v___x_2045_ = lean_usize_dec_lt(v_i_2038_, v_sz_2037_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; 
lean_dec_ref(v_ys_2036_);
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_bs_2039_);
return v___x_2046_;
}
else
{
lean_object* v_v_2047_; lean_object* v_value_2048_; lean_object* v___x_2049_; lean_object* v_bs_x27_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v_v_2047_ = lean_array_uget_borrowed(v_bs_2039_, v_i_2038_);
v_value_2048_ = lean_ctor_get(v_v_2047_, 7);
lean_inc_ref(v_value_2048_);
v___x_2049_ = lean_unsigned_to_nat(0u);
v_bs_x27_2050_ = lean_array_uset(v_bs_2039_, v_i_2038_, v___x_2049_);
v___x_2051_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2052_ = lean_usize_to_nat(v_i_2038_);
v___x_2053_ = lean_array_get_borrowed(v___x_2051_, v___x_2035_, v___x_2052_);
lean_dec(v___x_2052_);
lean_inc_ref(v_ys_2036_);
lean_inc(v___x_2053_);
v___x_2054_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_2053_, v_value_2048_, v_ys_2036_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; size_t v___x_2056_; size_t v___x_2057_; lean_object* v___x_2058_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref_known(v___x_2054_, 1);
v___x_2056_ = ((size_t)1ULL);
v___x_2057_ = lean_usize_add(v_i_2038_, v___x_2056_);
v___x_2058_ = lean_array_uset(v_bs_x27_2050_, v_i_2038_, v_a_2055_);
v_i_2038_ = v___x_2057_;
v_bs_2039_ = v___x_2058_;
goto _start;
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec_ref(v_bs_x27_2050_);
lean_dec_ref(v_ys_2036_);
v_a_2060_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2054_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2054_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2035_ = stack[0].m_obj;
lean_object* v_ys_2036_ = stack[1].m_obj;
size_t v_sz_2037_ = stack[2].m_num;
size_t v_i_2038_ = stack[3].m_num;
lean_object* v_bs_2039_ = stack[4].m_obj;
lean_object* v___y_2040_ = stack[5].m_obj;
lean_object* v___y_2041_ = stack[6].m_obj;
lean_object* v___y_2042_ = stack[7].m_obj;
lean_object* v___y_2043_ = stack[8].m_obj;
lean_object* v_res_2068_;
v_res_2068_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2035_, v_ys_2036_, v_sz_2037_, v_i_2038_, v_bs_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
stack->m_obj
 = v_res_2068_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg___boxed(lean_object* v___x_2069_, lean_object* v_ys_2070_, lean_object* v_sz_2071_, lean_object* v_i_2072_, lean_object* v_bs_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
size_t v_sz_boxed_2079_; size_t v_i_boxed_2080_; lean_object* v_res_2081_; 
v_sz_boxed_2079_ = lean_unbox_usize(v_sz_2071_);
lean_dec(v_sz_2071_);
v_i_boxed_2080_ = lean_unbox_usize(v_i_2072_);
lean_dec(v_i_2072_);
v_res_2081_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2069_, v_ys_2070_, v_sz_boxed_2079_, v_i_boxed_2080_, v_bs_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec_ref(v___x_2069_);
return v_res_2081_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(lean_object* v___x_2082_, lean_object* v_ys_2083_, size_t v_sz_2084_, size_t v_i_2085_, lean_object* v_bs_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
uint8_t v___x_2092_; 
v___x_2092_ = lean_usize_dec_lt(v_i_2085_, v_sz_2084_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; 
lean_dec_ref(v_ys_2083_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_bs_2086_);
return v___x_2093_;
}
else
{
lean_object* v_v_2094_; lean_object* v_type_2095_; lean_object* v___x_2096_; lean_object* v_bs_x27_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v_v_2094_ = lean_array_uget_borrowed(v_bs_2086_, v_i_2085_);
v_type_2095_ = lean_ctor_get(v_v_2094_, 6);
lean_inc_ref(v_type_2095_);
v___x_2096_ = lean_unsigned_to_nat(0u);
v_bs_x27_2097_ = lean_array_uset(v_bs_2086_, v_i_2085_, v___x_2096_);
v___x_2098_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2099_ = lean_usize_to_nat(v_i_2085_);
v___x_2100_ = lean_array_get_borrowed(v___x_2098_, v___x_2082_, v___x_2099_);
lean_dec(v___x_2099_);
lean_inc_ref(v_ys_2083_);
lean_inc(v___x_2100_);
v___x_2101_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_2100_, v_type_2095_, v_ys_2083_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; size_t v___x_2103_; size_t v___x_2104_; lean_object* v___x_2105_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v___x_2101_, 1);
v___x_2103_ = ((size_t)1ULL);
v___x_2104_ = lean_usize_add(v_i_2085_, v___x_2103_);
v___x_2105_ = lean_array_uset(v_bs_x27_2097_, v_i_2085_, v_a_2102_);
v_i_2085_ = v___x_2104_;
v_bs_2086_ = v___x_2105_;
goto _start;
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec_ref(v_bs_x27_2097_);
lean_dec_ref(v_ys_2083_);
v_a_2107_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2101_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2101_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2082_ = stack[0].m_obj;
lean_object* v_ys_2083_ = stack[1].m_obj;
size_t v_sz_2084_ = stack[2].m_num;
size_t v_i_2085_ = stack[3].m_num;
lean_object* v_bs_2086_ = stack[4].m_obj;
lean_object* v___y_2087_ = stack[5].m_obj;
lean_object* v___y_2088_ = stack[6].m_obj;
lean_object* v___y_2089_ = stack[7].m_obj;
lean_object* v___y_2090_ = stack[8].m_obj;
lean_object* v_res_2115_;
v_res_2115_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2082_, v_ys_2083_, v_sz_2084_, v_i_2085_, v_bs_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
stack->m_obj
 = v_res_2115_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg___boxed(lean_object* v___x_2116_, lean_object* v_ys_2117_, lean_object* v_sz_2118_, lean_object* v_i_2119_, lean_object* v_bs_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
size_t v_sz_boxed_2126_; size_t v_i_boxed_2127_; lean_object* v_res_2128_; 
v_sz_boxed_2126_ = lean_unbox_usize(v_sz_2118_);
lean_dec(v_sz_2118_);
v_i_boxed_2127_ = lean_unbox_usize(v_i_2119_);
lean_dec(v_i_2119_);
v_res_2128_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2116_, v_ys_2117_, v_sz_boxed_2126_, v_i_boxed_2127_, v_bs_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec_ref(v___x_2116_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
if (lean_obj_tag(v_a_2129_) == 0)
{
lean_object* v___x_2131_; 
v___x_2131_ = l_List_reverse___redArg(v_a_2130_);
return v___x_2131_;
}
else
{
lean_object* v_head_2132_; lean_object* v_tail_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2142_; 
v_head_2132_ = lean_ctor_get(v_a_2129_, 0);
v_tail_2133_ = lean_ctor_get(v_a_2129_, 1);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_a_2129_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2135_ = v_a_2129_;
v_isShared_2136_ = v_isSharedCheck_2142_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_tail_2133_);
lean_inc(v_head_2132_);
lean_dec(v_a_2129_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2142_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2137_ = l_Lean_mkLevelParam(v_head_2132_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 1, v_a_2130_);
lean_ctor_set(v___x_2135_, 0, v___x_2137_);
v___x_2139_ = v___x_2135_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_a_2130_);
v___x_2139_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
v_a_2129_ = v_tail_2133_;
v_a_2130_ = v___x_2139_;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(size_t v_sz_2143_, size_t v_i_2144_, lean_object* v_bs_2145_){
_start:
{
uint8_t v___x_2146_; 
v___x_2146_ = lean_usize_dec_lt(v_i_2144_, v_sz_2143_);
if (v___x_2146_ == 0)
{
return v_bs_2145_;
}
else
{
lean_object* v_v_2147_; lean_object* v_declName_2148_; lean_object* v___x_2149_; lean_object* v_bs_x27_2150_; size_t v___x_2151_; size_t v___x_2152_; lean_object* v___x_2153_; 
v_v_2147_ = lean_array_uget_borrowed(v_bs_2145_, v_i_2144_);
v_declName_2148_ = lean_ctor_get(v_v_2147_, 3);
lean_inc(v_declName_2148_);
v___x_2149_ = lean_unsigned_to_nat(0u);
v_bs_x27_2150_ = lean_array_uset(v_bs_2145_, v_i_2144_, v___x_2149_);
v___x_2151_ = ((size_t)1ULL);
v___x_2152_ = lean_usize_add(v_i_2144_, v___x_2151_);
v___x_2153_ = lean_array_uset(v_bs_x27_2150_, v_i_2144_, v_declName_2148_);
v_i_2144_ = v___x_2152_;
v_bs_2145_ = v___x_2153_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2143_ = stack[0].m_num;
size_t v_i_2144_ = stack[1].m_num;
lean_object* v_bs_2145_ = stack[2].m_obj;
lean_object* v_res_2155_;
v_res_2155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_2143_, v_i_2144_, v_bs_2145_);
stack->m_obj
 = v_res_2155_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3___boxed(lean_object* v_sz_2156_, lean_object* v_i_2157_, lean_object* v_bs_2158_){
_start:
{
size_t v_sz_boxed_2159_; size_t v_i_boxed_2160_; lean_object* v_res_2161_; 
v_sz_boxed_2159_ = lean_unbox_usize(v_sz_2156_);
lean_dec(v_sz_2156_);
v_i_boxed_2160_ = lean_unbox_usize(v_i_2157_);
lean_dec(v_i_2157_);
v_res_2161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_boxed_2159_, v_i_boxed_2160_, v_bs_2158_);
return v_res_2161_;
}
}
lean_object* l_Lean_Elab_WF_packMutual___lam__0(lean_object* v_preDefs_2162_, lean_object* v_perms_2163_, lean_object* v_argsPacker_2164_, uint8_t v___x_2165_, lean_object* v_ref_2166_, uint8_t v_kind_2167_, lean_object* v_levelParams_2168_, lean_object* v_modifiers_2169_, lean_object* v_newFn_2170_, lean_object* v_binders_2171_, lean_object* v_numSectionVars_2172_, lean_object* v_value_2173_, lean_object* v_termination_2174_, lean_object* v_fixedParamPerms_2175_, lean_object* v_ys_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
size_t v_sz_2182_; size_t v___x_2183_; lean_object* v___x_2184_; 
v_sz_2182_ = lean_array_size(v_preDefs_2162_);
v___x_2183_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_2162_);
lean_inc_ref(v_ys_2176_);
v___x_2184_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v_perms_2163_, v_ys_2176_, v_sz_2182_, v___x_2183_, v_preDefs_2162_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2186_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___x_2184_, 1);
lean_inc_ref(v_preDefs_2162_);
lean_inc_ref(v_ys_2176_);
v___x_2186_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v_perms_2163_, v_ys_2176_, v_sz_2182_, v___x_2183_, v_preDefs_2162_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___x_2188_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2186_, 1);
v___x_2188_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_2164_, v_a_2185_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec(v_a_2185_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; uint8_t v___x_2190_; uint8_t v___x_2191_; lean_object* v___x_2192_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
lean_dec_ref_known(v___x_2188_, 1);
v___x_2190_ = 1;
v___x_2191_ = 1;
v___x_2192_ = l_Lean_Meta_mkForallFVars(v_ys_2176_, v_a_2189_, v___x_2165_, v___x_2190_, v___x_2190_, v___x_2191_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc_n(v_a_2193_, 2);
lean_dec_ref_known(v___x_2192_, 1);
lean_inc_ref(v_termination_2174_);
lean_inc(v_numSectionVars_2172_);
lean_inc(v_binders_2171_);
lean_inc(v_newFn_2170_);
lean_inc_ref(v_modifiers_2169_);
lean_inc(v_levelParams_2168_);
lean_inc(v_ref_2166_);
v___x_2194_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2194_, 0, v_ref_2166_);
lean_ctor_set(v___x_2194_, 1, v_levelParams_2168_);
lean_ctor_set(v___x_2194_, 2, v_modifiers_2169_);
lean_ctor_set(v___x_2194_, 3, v_newFn_2170_);
lean_ctor_set(v___x_2194_, 4, v_binders_2171_);
lean_ctor_set(v___x_2194_, 5, v_numSectionVars_2172_);
lean_ctor_set(v___x_2194_, 6, v_a_2193_);
lean_ctor_set(v___x_2194_, 7, v_value_2173_);
lean_ctor_set(v___x_2194_, 8, v_termination_2174_);
lean_ctor_set_uint8(v___x_2194_, sizeof(void*)*9, v_kind_2167_);
v___x_2195_ = l_Lean_Elab_addAsAxiom___redArg(v___x_2194_, v___y_2179_, v___y_2180_);
lean_dec_ref_known(v___x_2194_, 9);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
lean_dec_ref_known(v___x_2195_, 1);
v___x_2196_ = lean_box(0);
lean_inc(v_levelParams_2168_);
v___x_2197_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_2168_, v___x_2196_);
lean_inc(v_newFn_2170_);
v___x_2198_ = l_Lean_mkConst(v_newFn_2170_, v___x_2197_);
v___x_2199_ = l_Lean_mkAppN(v___x_2198_, v_ys_2176_);
v___x_2200_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_2164_, v_a_2187_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec(v_a_2187_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref_known(v___x_2200_, 1);
v___x_2202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_2182_, v___x_2183_, v_preDefs_2162_);
v___x_2203_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_2175_, v_argsPacker_2164_, v___x_2202_, v___x_2199_, v_a_2201_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2205_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2204_);
lean_dec_ref_known(v___x_2203_, 1);
v___x_2205_ = l_Lean_Meta_mkLambdaFVars(v_ys_2176_, v_a_2204_, v___x_2165_, v___x_2190_, v___x_2165_, v___x_2190_, v___x_2191_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec_ref(v_ys_2176_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2214_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2208_ = v___x_2205_;
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2210_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2210_, 0, v_ref_2166_);
lean_ctor_set(v___x_2210_, 1, v_levelParams_2168_);
lean_ctor_set(v___x_2210_, 2, v_modifiers_2169_);
lean_ctor_set(v___x_2210_, 3, v_newFn_2170_);
lean_ctor_set(v___x_2210_, 4, v_binders_2171_);
lean_ctor_set(v___x_2210_, 5, v_numSectionVars_2172_);
lean_ctor_set(v___x_2210_, 6, v_a_2193_);
lean_ctor_set(v___x_2210_, 7, v_a_2206_);
lean_ctor_set(v___x_2210_, 8, v_termination_2174_);
lean_ctor_set_uint8(v___x_2210_, sizeof(void*)*9, v_kind_2167_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2210_);
v___x_2212_ = v___x_2208_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec(v_a_2193_);
lean_dec_ref(v_termination_2174_);
lean_dec(v_numSectionVars_2172_);
lean_dec(v_binders_2171_);
lean_dec(v_newFn_2170_);
lean_dec_ref(v_modifiers_2169_);
lean_dec(v_levelParams_2168_);
lean_dec(v_ref_2166_);
v_a_2215_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2205_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2205_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec(v_a_2193_);
lean_dec_ref(v_ys_2176_);
lean_dec_ref(v_termination_2174_);
lean_dec(v_numSectionVars_2172_);
lean_dec(v_binders_2171_);
lean_dec(v_newFn_2170_);
lean_dec_ref(v_modifiers_2169_);
lean_dec(v_levelParams_2168_);
lean_dec(v_ref_2166_);
v_a_2223_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2203_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2203_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec_ref(v___x_2199_);
lean_dec(v_a_2193_);
lean_dec_ref(v_ys_2176_);
lean_dec_ref(v_fixedParamPerms_2175_);
lean_dec_ref(v_termination_2174_);
lean_dec(v_numSectionVars_2172_);
lean_dec(v_binders_2171_);
lean_dec(v_newFn_2170_);
lean_dec_ref(v_modifiers_2169_);
lean_dec(v_levelParams_2168_);
lean_dec(v_ref_2166_);
lean_dec_ref(v_argsPacker_2164_);
lean_dec_ref(v_preDefs_2162_);
v_a_2231_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2200_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2200_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec(v_a_2193_);
lean_dec(v_a_2187_);
lean_dec_ref(v_ys_2176_);
lean_dec_ref(v_fixedParamPerms_2175_);
lean_dec_ref(v_termination_2174_);
lean_dec(v_numSectionVars_2172_);
lean_dec(v_binders_2171_);
lean_dec(v_newFn_2170_);
lean_dec_ref(v_modifiers_2169_);
lean_dec(v_levelParams_2168_);
lean_dec(v_ref_2166_);
lean_dec_ref(v_argsPacker_2164_);
lean_dec_ref(v_preDefs_2162_);
v_a_2239_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2195_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2195_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v_a_2187_);
lean_dec_ref(v_ys_2176_);
lean_dec_ref(v_fixedParamPerms_2175_);
lean_dec_ref(v_termination_2174_);
lean_dec_ref(v_value_2173_);
lean_dec(v_numSectionVars_2172_);
lean_dec(v_binders_2171_);
lean_dec(v_newFn_2170_);
lean_dec_ref(v_modifiers_2169_);
lean_dec(v_levelParams_2168_);
lean_dec(v_ref_2166_);
lean_dec_ref(v_argsPacker_2164_);
lean_dec_ref(v_preDefs_2162_);
v_a_2247_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2192_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2192_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v_a_2187_);
lean_dec_ref(v_ys_2176_);
lean_dec_ref(v_fixedParamPerms_2175_);
lean_dec_ref(v_termination_2174_);
lean_dec_ref(v_value_2173_);
lean_dec(v_numSectionVars_2172_);
lean_dec(v_binders_2171_);
lean_dec(v_newFn_2170_);
lean_dec_ref(v_modifiers_2169_);
lean_dec(v_levelParams_2168_);
lean_dec(v_ref_2166_);
lean_dec_ref(v_argsPacker_2164_);
lean_dec_ref(v_preDefs_2162_);
v_a_2255_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2188_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2188_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec(v_a_2185_);
lean_dec_ref(v_ys_2176_);
lean_dec_ref(v_fixedParamPerms_2175_);
lean_dec_ref(v_termination_2174_);
lean_dec_ref(v_value_2173_);
lean_dec(v_numSectionVars_2172_);
lean_dec(v_binders_2171_);
lean_dec(v_newFn_2170_);
lean_dec_ref(v_modifiers_2169_);
lean_dec(v_levelParams_2168_);
lean_dec(v_ref_2166_);
lean_dec_ref(v_argsPacker_2164_);
lean_dec_ref(v_preDefs_2162_);
v_a_2263_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2186_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2186_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_dec_ref(v_ys_2176_);
lean_dec_ref(v_fixedParamPerms_2175_);
lean_dec_ref(v_termination_2174_);
lean_dec_ref(v_value_2173_);
lean_dec(v_numSectionVars_2172_);
lean_dec(v_binders_2171_);
lean_dec(v_newFn_2170_);
lean_dec_ref(v_modifiers_2169_);
lean_dec(v_levelParams_2168_);
lean_dec(v_ref_2166_);
lean_dec_ref(v_argsPacker_2164_);
lean_dec_ref(v_preDefs_2162_);
v_a_2271_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2184_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2184_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_WF_packMutual___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_preDefs_2162_ = stack[0].m_obj;
lean_object* v_perms_2163_ = stack[1].m_obj;
lean_object* v_argsPacker_2164_ = stack[2].m_obj;
uint8_t v___x_2165_ = stack[3].m_num;
lean_object* v_ref_2166_ = stack[4].m_obj;
uint8_t v_kind_2167_ = stack[5].m_num;
lean_object* v_levelParams_2168_ = stack[6].m_obj;
lean_object* v_modifiers_2169_ = stack[7].m_obj;
lean_object* v_newFn_2170_ = stack[8].m_obj;
lean_object* v_binders_2171_ = stack[9].m_obj;
lean_object* v_numSectionVars_2172_ = stack[10].m_obj;
lean_object* v_value_2173_ = stack[11].m_obj;
lean_object* v_termination_2174_ = stack[12].m_obj;
lean_object* v_fixedParamPerms_2175_ = stack[13].m_obj;
lean_object* v_ys_2176_ = stack[14].m_obj;
lean_object* v___y_2177_ = stack[15].m_obj;
lean_object* v___y_2178_ = stack[16].m_obj;
lean_object* v___y_2179_ = stack[17].m_obj;
lean_object* v___y_2180_ = stack[18].m_obj;
lean_object* v_res_2279_;
v_res_2279_ = l_Lean_Elab_WF_packMutual___lam__0(v_preDefs_2162_, v_perms_2163_, v_argsPacker_2164_, v___x_2165_, v_ref_2166_, v_kind_2167_, v_levelParams_2168_, v_modifiers_2169_, v_newFn_2170_, v_binders_2171_, v_numSectionVars_2172_, v_value_2173_, v_termination_2174_, v_fixedParamPerms_2175_, v_ys_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
stack->m_obj
 = v_res_2279_;
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
uint8_t v___x_2643__boxed_2300_; uint8_t v_kind_boxed_2301_; lean_object* v_res_2302_; 
v___x_2643__boxed_2300_ = lean_unbox(v___x_2283_);
v_kind_boxed_2301_ = lean_unbox(v_kind_2285_);
v_res_2302_ = l_Lean_Elab_WF_packMutual___lam__0(v_preDefs_2280_, v_perms_2281_, v_argsPacker_2282_, v___x_2643__boxed_2300_, v_ref_2284_, v_kind_boxed_2301_, v_levelParams_2286_, v_modifiers_2287_, v_newFn_2288_, v_binders_2289_, v_numSectionVars_2290_, v_value_2291_, v_termination_2292_, v_fixedParamPerms_2293_, v_ys_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec_ref(v_perms_2281_);
return v_res_2302_;
}
}
lean_object* l_Lean_Elab_WF_packMutual(lean_object* v_fixedParamPerms_2303_, lean_object* v_argsPacker_2304_, lean_object* v_preDefs_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
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
LEAN_EXPORT void l_Lean_Elab_WF_packMutual_0interp(lean_interpreter_value* stack)
{
lean_object* v_fixedParamPerms_2303_ = stack[0].m_obj;
lean_object* v_argsPacker_2304_ = stack[1].m_obj;
lean_object* v_preDefs_2305_ = stack[2].m_obj;
lean_object* v_a_2306_ = stack[3].m_obj;
lean_object* v_a_2307_ = stack[4].m_obj;
lean_object* v_a_2308_ = stack[5].m_obj;
lean_object* v_a_2309_ = stack[6].m_obj;
lean_object* v_res_2334_;
v_res_2334_ = l_Lean_Elab_WF_packMutual(v_fixedParamPerms_2303_, v_argsPacker_2304_, v_preDefs_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
stack->m_obj
 = v_res_2334_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___boxed(lean_object* v_fixedParamPerms_2335_, lean_object* v_argsPacker_2336_, lean_object* v_preDefs_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Lean_Elab_WF_packMutual(v_fixedParamPerms_2335_, v_argsPacker_2336_, v_preDefs_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
lean_dec(v_a_2341_);
lean_dec_ref(v_a_2340_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2338_);
return v_res_2343_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(lean_object* v___x_2344_, lean_object* v_ys_2345_, lean_object* v_as_2346_, size_t v_sz_2347_, size_t v_i_2348_, lean_object* v_bs_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2344_, v_ys_2345_, v_sz_2347_, v_i_2348_, v_bs_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
return v___x_2355_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2344_ = stack[0].m_obj;
lean_object* v_ys_2345_ = stack[1].m_obj;
lean_object* v_as_2346_ = stack[2].m_obj;
size_t v_sz_2347_ = stack[3].m_num;
size_t v_i_2348_ = stack[4].m_num;
lean_object* v_bs_2349_ = stack[5].m_obj;
lean_object* v___y_2350_ = stack[6].m_obj;
lean_object* v___y_2351_ = stack[7].m_obj;
lean_object* v___y_2352_ = stack[8].m_obj;
lean_object* v___y_2353_ = stack[9].m_obj;
lean_object* v_res_2356_;
v_res_2356_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(v___x_2344_, v_ys_2345_, v_as_2346_, v_sz_2347_, v_i_2348_, v_bs_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
stack->m_obj
 = v_res_2356_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___boxed(lean_object* v___x_2357_, lean_object* v_ys_2358_, lean_object* v_as_2359_, lean_object* v_sz_2360_, lean_object* v_i_2361_, lean_object* v_bs_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
size_t v_sz_boxed_2368_; size_t v_i_boxed_2369_; lean_object* v_res_2370_; 
v_sz_boxed_2368_ = lean_unbox_usize(v_sz_2360_);
lean_dec(v_sz_2360_);
v_i_boxed_2369_ = lean_unbox_usize(v_i_2361_);
lean_dec(v_i_2361_);
v_res_2370_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(v___x_2357_, v_ys_2358_, v_as_2359_, v_sz_boxed_2368_, v_i_boxed_2369_, v_bs_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec_ref(v_as_2359_);
lean_dec_ref(v___x_2357_);
return v_res_2370_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(lean_object* v___x_2371_, lean_object* v_ys_2372_, lean_object* v_as_2373_, size_t v_sz_2374_, size_t v_i_2375_, lean_object* v_bs_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2371_, v_ys_2372_, v_sz_2374_, v_i_2375_, v_bs_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
return v___x_2382_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2371_ = stack[0].m_obj;
lean_object* v_ys_2372_ = stack[1].m_obj;
lean_object* v_as_2373_ = stack[2].m_obj;
size_t v_sz_2374_ = stack[3].m_num;
size_t v_i_2375_ = stack[4].m_num;
lean_object* v_bs_2376_ = stack[5].m_obj;
lean_object* v___y_2377_ = stack[6].m_obj;
lean_object* v___y_2378_ = stack[7].m_obj;
lean_object* v___y_2379_ = stack[8].m_obj;
lean_object* v___y_2380_ = stack[9].m_obj;
lean_object* v_res_2383_;
v_res_2383_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(v___x_2371_, v_ys_2372_, v_as_2373_, v_sz_2374_, v_i_2375_, v_bs_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
stack->m_obj
 = v_res_2383_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___boxed(lean_object* v___x_2384_, lean_object* v_ys_2385_, lean_object* v_as_2386_, lean_object* v_sz_2387_, lean_object* v_i_2388_, lean_object* v_bs_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
size_t v_sz_boxed_2395_; size_t v_i_boxed_2396_; lean_object* v_res_2397_; 
v_sz_boxed_2395_ = lean_unbox_usize(v_sz_2387_);
lean_dec(v_sz_2387_);
v_i_boxed_2396_ = lean_unbox_usize(v_i_2388_);
lean_dec(v_i_2388_);
v_res_2397_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(v___x_2384_, v_ys_2385_, v_as_2386_, v_sz_boxed_2395_, v_i_boxed_2396_, v_bs_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec_ref(v_as_2386_);
lean_dec_ref(v___x_2384_);
return v_res_2397_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(lean_object* v_e_2398_, lean_object* v_k_2399_, uint8_t v_cleanupAnnotations_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v___f_2406_; uint8_t v___x_2407_; uint8_t v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___f_2406_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2406_, 0, v_k_2399_);
v___x_2407_ = 1;
v___x_2408_ = 0;
v___x_2409_ = lean_box(0);
v___x_2410_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2398_, v___x_2407_, v___x_2408_, v___x_2407_, v___x_2408_, v___x_2409_, v___f_2406_, v_cleanupAnnotations_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2410_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2410_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
v_a_2419_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2410_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2410_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2398_ = stack[0].m_obj;
lean_object* v_k_2399_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_2400_ = stack[2].m_num;
lean_object* v___y_2401_ = stack[3].m_obj;
lean_object* v___y_2402_ = stack[4].m_obj;
lean_object* v___y_2403_ = stack[5].m_obj;
lean_object* v___y_2404_ = stack[6].m_obj;
lean_object* v_res_2427_;
v_res_2427_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2398_, v_k_2399_, v_cleanupAnnotations_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
stack->m_obj
 = v_res_2427_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg___boxed(lean_object* v_e_2428_, lean_object* v_k_2429_, lean_object* v_cleanupAnnotations_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2436_; lean_object* v_res_2437_; 
v_cleanupAnnotations_boxed_2436_ = lean_unbox(v_cleanupAnnotations_2430_);
v_res_2437_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2428_, v_k_2429_, v_cleanupAnnotations_boxed_2436_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
return v_res_2437_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(lean_object* v_00_u03b1_2438_, lean_object* v_e_2439_, lean_object* v_k_2440_, uint8_t v_cleanupAnnotations_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2439_, v_k_2440_, v_cleanupAnnotations_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
return v___x_2447_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2439_ = stack[1].m_obj;
lean_object* v_k_2440_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_2441_ = stack[3].m_num;
lean_object* v___y_2442_ = stack[4].m_obj;
lean_object* v___y_2443_ = stack[5].m_obj;
lean_object* v___y_2444_ = stack[6].m_obj;
lean_object* v___y_2445_ = stack[7].m_obj;
lean_object* v_res_2448_;
v_res_2448_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(lean_box(0), v_e_2439_, v_k_2440_, v_cleanupAnnotations_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
stack->m_obj
 = v_res_2448_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___boxed(lean_object* v_00_u03b1_2449_, lean_object* v_e_2450_, lean_object* v_k_2451_, lean_object* v_cleanupAnnotations_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2458_; lean_object* v_res_2459_; 
v_cleanupAnnotations_boxed_2458_ = lean_unbox(v_cleanupAnnotations_2452_);
v_res_2459_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(v_00_u03b1_2449_, v_e_2450_, v_k_2451_, v_cleanupAnnotations_boxed_2458_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
return v_res_2459_;
}
}
lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(lean_object* v_msg_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___f_2466_; lean_object* v___x_1649__overap_2467_; lean_object* v___x_2468_; 
v___f_2466_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1649__overap_2467_ = lean_panic_fn_borrowed(v___f_2466_, v_msg_2460_);
lean_inc(v___y_2464_);
lean_inc_ref(v___y_2463_);
lean_inc(v___y_2462_);
lean_inc_ref(v___y_2461_);
v___x_2468_ = lean_apply_5(v___x_1649__overap_2467_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, lean_box(0));
return v___x_2468_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2460_ = stack[0].m_obj;
lean_object* v___y_2461_ = stack[1].m_obj;
lean_object* v___y_2462_ = stack[2].m_obj;
lean_object* v___y_2463_ = stack[3].m_obj;
lean_object* v___y_2464_ = stack[4].m_obj;
lean_object* v_res_2469_;
v_res_2469_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v_msg_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
stack->m_obj
 = v_res_2469_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1___boxed(lean_object* v_msg_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v_msg_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
return v_res_2476_;
}
}
lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0(lean_object* v_xs_2477_, lean_object* v_x_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2484_ = lean_array_get_size(v_xs_2477_);
v___x_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT void l_Lean_Elab_WF_varyingVarNames___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2477_ = stack[0].m_obj;
lean_object* v_x_2478_ = stack[1].m_obj;
lean_object* v___y_2479_ = stack[2].m_obj;
lean_object* v___y_2480_ = stack[3].m_obj;
lean_object* v___y_2481_ = stack[4].m_obj;
lean_object* v___y_2482_ = stack[5].m_obj;
lean_object* v_res_2486_;
v_res_2486_ = l_Lean_Elab_WF_varyingVarNames___lam__0(v_xs_2477_, v_x_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
stack->m_obj
 = v_res_2486_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0___boxed(lean_object* v_xs_2487_, lean_object* v_x_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Lean_Elab_WF_varyingVarNames___lam__0(v_xs_2487_, v_x_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec_ref(v_x_2488_);
lean_dec_ref(v_xs_2487_);
return v_res_2494_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(lean_object* v_as_2495_, size_t v_sz_2496_, size_t v_i_2497_, lean_object* v_b_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v_a_2504_; uint8_t v___x_2508_; 
v___x_2508_ = lean_usize_dec_lt(v_i_2497_, v_sz_2496_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v_b_2498_);
return v___x_2509_;
}
else
{
lean_object* v_snd_2510_; lean_object* v_fst_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2555_; 
v_snd_2510_ = lean_ctor_get(v_b_2498_, 1);
v_fst_2511_ = lean_ctor_get(v_b_2498_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_b_2498_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2513_ = v_b_2498_;
v_isShared_2514_ = v_isSharedCheck_2555_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_snd_2510_);
lean_inc(v_fst_2511_);
lean_dec(v_b_2498_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2555_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v_array_2515_; lean_object* v_start_2516_; lean_object* v_stop_2517_; uint8_t v___x_2518_; 
v_array_2515_ = lean_ctor_get(v_snd_2510_, 0);
v_start_2516_ = lean_ctor_get(v_snd_2510_, 1);
v_stop_2517_ = lean_ctor_get(v_snd_2510_, 2);
v___x_2518_ = lean_nat_dec_lt(v_start_2516_, v_stop_2517_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2520_; 
if (v_isShared_2514_ == 0)
{
v___x_2520_ = v___x_2513_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_fst_2511_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_snd_2510_);
v___x_2520_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2521_; 
v___x_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
return v___x_2521_;
}
}
else
{
lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2551_; 
lean_inc(v_stop_2517_);
lean_inc(v_start_2516_);
lean_inc_ref(v_array_2515_);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_snd_2510_);
if (v_isSharedCheck_2551_ == 0)
{
lean_object* v_unused_2552_; lean_object* v_unused_2553_; lean_object* v_unused_2554_; 
v_unused_2552_ = lean_ctor_get(v_snd_2510_, 2);
lean_dec(v_unused_2552_);
v_unused_2553_ = lean_ctor_get(v_snd_2510_, 1);
lean_dec(v_unused_2553_);
v_unused_2554_ = lean_ctor_get(v_snd_2510_, 0);
lean_dec(v_unused_2554_);
v___x_2524_ = v_snd_2510_;
v_isShared_2525_ = v_isSharedCheck_2551_;
goto v_resetjp_2523_;
}
else
{
lean_dec(v_snd_2510_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2551_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2530_; 
v___x_2526_ = lean_array_fget(v_array_2515_, v_start_2516_);
v___x_2527_ = lean_unsigned_to_nat(1u);
v___x_2528_ = lean_nat_add(v_start_2516_, v___x_2527_);
lean_dec(v_start_2516_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 1, v___x_2528_);
v___x_2530_ = v___x_2524_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_array_2515_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v___x_2528_);
lean_ctor_set(v_reuseFailAlloc_2550_, 2, v_stop_2517_);
v___x_2530_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v_a_2531_ = lean_array_uget_borrowed(v_as_2495_, v_i_2497_);
v___x_2532_ = l_Lean_Expr_fvarId_x21(v_a_2531_);
v___x_2533_ = l_Lean_FVarId_getUserName___redArg(v___x_2532_, v___y_2499_, v___y_2500_, v___y_2501_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; lean_object* v___x_2535_; lean_object* v___x_2537_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2534_);
lean_dec_ref_known(v___x_2533_, 1);
v___x_2535_ = lean_array_push(v_fst_2511_, v_a_2534_);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 1, v___x_2530_);
lean_ctor_set(v___x_2513_, 0, v___x_2535_);
v___x_2537_ = v___x_2513_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2535_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v___x_2530_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
v_a_2504_ = v___x_2537_;
goto v___jp_2503_;
}
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
lean_dec_ref(v___x_2530_);
lean_del_object(v___x_2513_);
lean_dec(v_fst_2511_);
v_a_2539_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2533_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2533_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
else
{
lean_object* v___x_2548_; 
lean_dec_ref_known(v___x_2526_, 1);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 1, v___x_2530_);
v___x_2548_ = v___x_2513_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_fst_2511_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v___x_2530_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
v_a_2504_ = v___x_2548_;
goto v___jp_2503_;
}
}
}
}
}
}
}
v___jp_2503_:
{
size_t v___x_2505_; size_t v___x_2506_; 
v___x_2505_ = ((size_t)1ULL);
v___x_2506_ = lean_usize_add(v_i_2497_, v___x_2505_);
v_i_2497_ = v___x_2506_;
v_b_2498_ = v_a_2504_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2495_ = stack[0].m_obj;
size_t v_sz_2496_ = stack[1].m_num;
size_t v_i_2497_ = stack[2].m_num;
lean_object* v_b_2498_ = stack[3].m_obj;
lean_object* v___y_2499_ = stack[4].m_obj;
lean_object* v___y_2500_ = stack[5].m_obj;
lean_object* v___y_2501_ = stack[6].m_obj;
lean_object* v_res_2556_;
v_res_2556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2495_, v_sz_2496_, v_i_2497_, v_b_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
stack->m_obj
 = v_res_2556_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg___boxed(lean_object* v_as_2557_, lean_object* v_sz_2558_, lean_object* v_i_2559_, lean_object* v_b_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
size_t v_sz_boxed_2565_; size_t v_i_boxed_2566_; lean_object* v_res_2567_; 
v_sz_boxed_2565_ = lean_unbox_usize(v_sz_2558_);
lean_dec(v_sz_2558_);
v_i_boxed_2566_ = lean_unbox_usize(v_i_2559_);
lean_dec(v_i_2559_);
v_res_2567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2557_, v_sz_boxed_2565_, v_i_boxed_2566_, v_b_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec_ref(v_as_2557_);
return v_res_2567_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2570_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1));
v___x_2571_ = lean_unsigned_to_nat(4u);
v___x_2572_ = lean_unsigned_to_nat(119u);
v___x_2573_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2574_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2575_ = l_mkPanicMessageWithDecl(v___x_2574_, v___x_2573_, v___x_2572_, v___x_2571_, v___x_2570_);
return v___x_2575_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2577_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3));
v___x_2578_ = lean_unsigned_to_nat(4u);
v___x_2579_ = lean_unsigned_to_nat(120u);
v___x_2580_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2581_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2582_ = l_mkPanicMessageWithDecl(v___x_2581_, v___x_2580_, v___x_2579_, v___x_2578_, v___x_2577_);
return v___x_2582_;
}
}
lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1(lean_object* v_a_2585_, lean_object* v_fixedParamPerms_2586_, lean_object* v___x_2587_, lean_object* v_preDefIdx_2588_, lean_object* v_xs_2589_, lean_object* v_x_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v___x_2596_; uint8_t v___x_2597_; 
v___x_2596_ = lean_array_get_size(v_xs_2589_);
v___x_2597_ = lean_nat_dec_eq(v___x_2596_, v_a_2585_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2);
v___x_2599_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2598_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
return v___x_2599_;
}
else
{
lean_object* v_perms_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; uint8_t v___x_2603_; 
v_perms_2600_ = lean_ctor_get(v_fixedParamPerms_2586_, 1);
v___x_2601_ = lean_array_get_borrowed(v___x_2587_, v_perms_2600_, v_preDefIdx_2588_);
v___x_2602_ = lean_array_get_size(v___x_2601_);
v___x_2603_ = lean_nat_dec_eq(v___x_2602_, v_a_2585_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4);
v___x_2605_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2604_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
return v___x_2605_;
}
else
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; size_t v_sz_2610_; size_t v___x_2611_; lean_object* v___x_2612_; 
v___x_2606_ = lean_unsigned_to_nat(0u);
v___x_2607_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5));
lean_inc(v___x_2601_);
v___x_2608_ = l_Array_toSubarray___redArg(v___x_2601_, v___x_2606_, v___x_2602_);
v___x_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2607_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
v_sz_2610_ = lean_array_size(v_xs_2589_);
v___x_2611_ = ((size_t)0ULL);
v___x_2612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_xs_2589_, v_sz_2610_, v___x_2611_, v___x_2609_, v___y_2591_, v___y_2593_, v___y_2594_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2621_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2615_ = v___x_2612_;
v_isShared_2616_ = v_isSharedCheck_2621_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2621_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v_fst_2617_; lean_object* v___x_2619_; 
v_fst_2617_ = lean_ctor_get(v_a_2613_, 0);
lean_inc(v_fst_2617_);
lean_dec(v_a_2613_);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v_fst_2617_);
v___x_2619_ = v___x_2615_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_fst_2617_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
v_a_2622_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2612_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2612_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_WF_varyingVarNames___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2585_ = stack[0].m_obj;
lean_object* v_fixedParamPerms_2586_ = stack[1].m_obj;
lean_object* v___x_2587_ = stack[2].m_obj;
lean_object* v_preDefIdx_2588_ = stack[3].m_obj;
lean_object* v_xs_2589_ = stack[4].m_obj;
lean_object* v_x_2590_ = stack[5].m_obj;
lean_object* v___y_2591_ = stack[6].m_obj;
lean_object* v___y_2592_ = stack[7].m_obj;
lean_object* v___y_2593_ = stack[8].m_obj;
lean_object* v___y_2594_ = stack[9].m_obj;
lean_object* v_res_2630_;
v_res_2630_ = l_Lean_Elab_WF_varyingVarNames___lam__1(v_a_2585_, v_fixedParamPerms_2586_, v___x_2587_, v_preDefIdx_2588_, v_xs_2589_, v_x_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
stack->m_obj
 = v_res_2630_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___boxed(lean_object* v_a_2631_, lean_object* v_fixedParamPerms_2632_, lean_object* v___x_2633_, lean_object* v_preDefIdx_2634_, lean_object* v_xs_2635_, lean_object* v_x_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_Lean_Elab_WF_varyingVarNames___lam__1(v_a_2631_, v_fixedParamPerms_2632_, v___x_2633_, v_preDefIdx_2634_, v_xs_2635_, v_x_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec_ref(v_x_2636_);
lean_dec_ref(v_xs_2635_);
lean_dec(v_preDefIdx_2634_);
lean_dec_ref(v___x_2633_);
lean_dec_ref(v_fixedParamPerms_2632_);
lean_dec(v_a_2631_);
return v_res_2642_;
}
}
lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object* v_fixedParamPerms_2644_, lean_object* v_preDefIdx_2645_, lean_object* v_preDef_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v_type_2652_; lean_object* v_value_2653_; lean_object* v___f_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; lean_object* v___x_2657_; 
v_type_2652_ = lean_ctor_get(v_preDef_2646_, 6);
lean_inc_ref(v_type_2652_);
v_value_2653_ = lean_ctor_get(v_preDef_2646_, 7);
lean_inc_ref(v_value_2653_);
lean_dec_ref(v_preDef_2646_);
v___f_2654_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___closed__0));
v___x_2655_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2656_ = 0;
v___x_2657_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_value_2653_, v___f_2654_, v___x_2656_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v___f_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc_n(v_a_2658_, 2);
lean_dec_ref_known(v___x_2657_, 1);
v___f_2659_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_varyingVarNames___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2659_, 0, v_a_2658_);
lean_closure_set(v___f_2659_, 1, v_fixedParamPerms_2644_);
lean_closure_set(v___f_2659_, 2, v___x_2655_);
lean_closure_set(v___f_2659_, 3, v_preDefIdx_2645_);
v___x_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2660_, 0, v_a_2658_);
v___x_2661_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2652_, v___x_2660_, v___f_2659_, v___x_2656_, v___x_2656_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_);
return v___x_2661_;
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
lean_dec_ref(v_type_2652_);
lean_dec(v_preDefIdx_2645_);
lean_dec_ref(v_fixedParamPerms_2644_);
v_a_2662_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2657_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2657_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_WF_varyingVarNames_0interp(lean_interpreter_value* stack)
{
lean_object* v_fixedParamPerms_2644_ = stack[0].m_obj;
lean_object* v_preDefIdx_2645_ = stack[1].m_obj;
lean_object* v_preDef_2646_ = stack[2].m_obj;
lean_object* v_a_2647_ = stack[3].m_obj;
lean_object* v_a_2648_ = stack[4].m_obj;
lean_object* v_a_2649_ = stack[5].m_obj;
lean_object* v_a_2650_ = stack[6].m_obj;
lean_object* v_res_2670_;
v_res_2670_ = l_Lean_Elab_WF_varyingVarNames(v_fixedParamPerms_2644_, v_preDefIdx_2645_, v_preDef_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_);
stack->m_obj
 = v_res_2670_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___boxed(lean_object* v_fixedParamPerms_2671_, lean_object* v_preDefIdx_2672_, lean_object* v_preDef_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean_Elab_WF_varyingVarNames(v_fixedParamPerms_2671_, v_preDefIdx_2672_, v_preDef_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
return v_res_2679_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(lean_object* v_as_2680_, size_t v_sz_2681_, size_t v_i_2682_, lean_object* v_b_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v___x_2689_; 
v___x_2689_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2680_, v_sz_2681_, v_i_2682_, v_b_2683_, v___y_2684_, v___y_2686_, v___y_2687_);
return v___x_2689_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2680_ = stack[0].m_obj;
size_t v_sz_2681_ = stack[1].m_num;
size_t v_i_2682_ = stack[2].m_num;
lean_object* v_b_2683_ = stack[3].m_obj;
lean_object* v___y_2684_ = stack[4].m_obj;
lean_object* v___y_2685_ = stack[5].m_obj;
lean_object* v___y_2686_ = stack[6].m_obj;
lean_object* v___y_2687_ = stack[7].m_obj;
lean_object* v_res_2690_;
v_res_2690_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(v_as_2680_, v_sz_2681_, v_i_2682_, v_b_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
stack->m_obj
 = v_res_2690_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___boxed(lean_object* v_as_2691_, lean_object* v_sz_2692_, lean_object* v_i_2693_, lean_object* v_b_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
size_t v_sz_boxed_2700_; size_t v_i_boxed_2701_; lean_object* v_res_2702_; 
v_sz_boxed_2700_ = lean_unbox_usize(v_sz_2692_);
lean_dec(v_sz_2692_);
v_i_boxed_2701_ = lean_unbox_usize(v_i_2693_);
lean_dec(v_i_2693_);
v_res_2702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(v_as_2691_, v_sz_boxed_2700_, v_i_boxed_2701_, v_b_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec_ref(v_as_2691_);
return v_res_2702_;
}
}
lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(lean_object* v_msg_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___f_2709_; lean_object* v___x_1596__overap_2710_; lean_object* v___x_2711_; 
v___f_2709_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1596__overap_2710_ = lean_panic_fn_borrowed(v___f_2709_, v_msg_2703_);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
lean_inc(v___y_2705_);
lean_inc_ref(v___y_2704_);
v___x_2711_ = lean_apply_5(v___x_1596__overap_2710_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, lean_box(0));
return v___x_2711_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2703_ = stack[0].m_obj;
lean_object* v___y_2704_ = stack[1].m_obj;
lean_object* v___y_2705_ = stack[2].m_obj;
lean_object* v___y_2706_ = stack[3].m_obj;
lean_object* v___y_2707_ = stack[4].m_obj;
lean_object* v_res_2712_;
v_res_2712_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v_msg_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
stack->m_obj
 = v_res_2712_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0___boxed(lean_object* v_msg_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v_msg_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
return v_res_2719_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2720_; double v___x_2721_; 
v___x_2720_ = lean_unsigned_to_nat(0u);
v___x_2721_ = lean_float_of_nat(v___x_2720_);
return v___x_2721_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(lean_object* v_cls_2725_, lean_object* v_msg_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_ref_2732_; lean_object* v___x_2733_; lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2779_; 
v_ref_2732_ = lean_ctor_get(v___y_2729_, 2);
v___x_2733_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msg_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2736_ = v___x_2733_;
v_isShared_2737_ = v_isSharedCheck_2779_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2733_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2779_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2738_; lean_object* v_traceState_2739_; lean_object* v_env_2740_; lean_object* v_nextMacroScope_2741_; lean_object* v_ngen_2742_; lean_object* v_auxDeclNGen_2743_; lean_object* v_cache_2744_; lean_object* v_recordedDeps_2745_; lean_object* v_messages_2746_; lean_object* v_infoState_2747_; lean_object* v_snapshotTasks_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2778_; 
v___x_2738_ = lean_st_ref_take(v___y_2730_);
v_traceState_2739_ = lean_ctor_get(v___x_2738_, 4);
v_env_2740_ = lean_ctor_get(v___x_2738_, 0);
v_nextMacroScope_2741_ = lean_ctor_get(v___x_2738_, 1);
v_ngen_2742_ = lean_ctor_get(v___x_2738_, 2);
v_auxDeclNGen_2743_ = lean_ctor_get(v___x_2738_, 3);
v_cache_2744_ = lean_ctor_get(v___x_2738_, 5);
v_recordedDeps_2745_ = lean_ctor_get(v___x_2738_, 6);
v_messages_2746_ = lean_ctor_get(v___x_2738_, 7);
v_infoState_2747_ = lean_ctor_get(v___x_2738_, 8);
v_snapshotTasks_2748_ = lean_ctor_get(v___x_2738_, 9);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2750_ = v___x_2738_;
v_isShared_2751_ = v_isSharedCheck_2778_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_snapshotTasks_2748_);
lean_inc(v_infoState_2747_);
lean_inc(v_messages_2746_);
lean_inc(v_recordedDeps_2745_);
lean_inc(v_cache_2744_);
lean_inc(v_traceState_2739_);
lean_inc(v_auxDeclNGen_2743_);
lean_inc(v_ngen_2742_);
lean_inc(v_nextMacroScope_2741_);
lean_inc(v_env_2740_);
lean_dec(v___x_2738_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2778_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
uint64_t v_tid_2752_; lean_object* v_traces_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2777_; 
v_tid_2752_ = lean_ctor_get_uint64(v_traceState_2739_, sizeof(void*)*1);
v_traces_2753_ = lean_ctor_get(v_traceState_2739_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v_traceState_2739_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2755_ = v_traceState_2739_;
v_isShared_2756_ = v_isSharedCheck_2777_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_traces_2753_);
lean_dec(v_traceState_2739_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2777_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; double v___x_2759_; uint8_t v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2768_; 
v___x_2757_ = lean_box(0);
v___x_2758_ = lean_box(0);
v___x_2759_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0);
v___x_2760_ = 0;
v___x_2761_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1));
v___x_2762_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2762_, 0, v_cls_2725_);
lean_ctor_set(v___x_2762_, 1, v___x_2758_);
lean_ctor_set(v___x_2762_, 2, v___x_2761_);
lean_ctor_set_float(v___x_2762_, sizeof(void*)*3, v___x_2759_);
lean_ctor_set_float(v___x_2762_, sizeof(void*)*3 + 8, v___x_2759_);
lean_ctor_set_uint8(v___x_2762_, sizeof(void*)*3 + 16, v___x_2760_);
v___x_2763_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2));
v___x_2764_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2762_);
lean_ctor_set(v___x_2764_, 1, v_a_2734_);
lean_ctor_set(v___x_2764_, 2, v___x_2763_);
lean_inc(v_ref_2732_);
v___x_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2765_, 0, v_ref_2732_);
lean_ctor_set(v___x_2765_, 1, v___x_2764_);
v___x_2766_ = l_Lean_PersistentArray_push___redArg(v_traces_2753_, v___x_2765_);
if (v_isShared_2756_ == 0)
{
lean_ctor_set(v___x_2755_, 0, v___x_2766_);
v___x_2768_ = v___x_2755_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2766_);
lean_ctor_set_uint64(v_reuseFailAlloc_2776_, sizeof(void*)*1, v_tid_2752_);
v___x_2768_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
lean_object* v___x_2770_; 
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 4, v___x_2768_);
v___x_2770_ = v___x_2750_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_env_2740_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_nextMacroScope_2741_);
lean_ctor_set(v_reuseFailAlloc_2775_, 2, v_ngen_2742_);
lean_ctor_set(v_reuseFailAlloc_2775_, 3, v_auxDeclNGen_2743_);
lean_ctor_set(v_reuseFailAlloc_2775_, 4, v___x_2768_);
lean_ctor_set(v_reuseFailAlloc_2775_, 5, v_cache_2744_);
lean_ctor_set(v_reuseFailAlloc_2775_, 6, v_recordedDeps_2745_);
lean_ctor_set(v_reuseFailAlloc_2775_, 7, v_messages_2746_);
lean_ctor_set(v_reuseFailAlloc_2775_, 8, v_infoState_2747_);
lean_ctor_set(v_reuseFailAlloc_2775_, 9, v_snapshotTasks_2748_);
v___x_2770_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v___x_2771_; lean_object* v___x_2773_; 
v___x_2771_ = lean_st_ref_put(v___y_2730_, v___x_2770_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 0, v___x_2757_);
v___x_2773_ = v___x_2736_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2757_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2725_ = stack[0].m_obj;
lean_object* v_msg_2726_ = stack[1].m_obj;
lean_object* v___y_2727_ = stack[2].m_obj;
lean_object* v___y_2728_ = stack[3].m_obj;
lean_object* v___y_2729_ = stack[4].m_obj;
lean_object* v___y_2730_ = stack[5].m_obj;
lean_object* v_res_2780_;
v_res_2780_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v_cls_2725_, v_msg_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
stack->m_obj
 = v_res_2780_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___boxed(lean_object* v_cls_2781_, lean_object* v_msg_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v_cls_2781_, v_msg_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
return v_res_2788_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1));
v___x_2792_ = lean_unsigned_to_nat(8u);
v___x_2793_ = lean_unsigned_to_nat(135u);
v___x_2794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0));
v___x_2795_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2796_ = l_mkPanicMessageWithDecl(v___x_2795_, v___x_2794_, v___x_2793_, v___x_2792_, v___x_2791_);
return v___x_2796_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(lean_object* v___x_2797_, lean_object* v_unaryPreDefNonRec_2798_, lean_object* v___x_2799_, lean_object* v_us_2800_, lean_object* v_argsPacker_2801_, lean_object* v___x_2802_, lean_object* v_params_2803_, lean_object* v_x_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v___x_2810_; uint8_t v___x_2811_; 
v___x_2810_ = lean_array_get_size(v_params_2803_);
v___x_2811_ = lean_nat_dec_eq(v___x_2797_, v___x_2810_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
lean_dec(v___x_2802_);
lean_dec(v_us_2800_);
lean_dec_ref(v_unaryPreDefNonRec_2798_);
v___x_2812_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2);
v___x_2813_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v___x_2812_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
return v___x_2813_;
}
else
{
lean_object* v_declName_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v_declName_2814_ = lean_ctor_get(v_unaryPreDefNonRec_2798_, 3);
lean_inc(v_declName_2814_);
lean_dec_ref(v_unaryPreDefNonRec_2798_);
v___x_2815_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v___x_2799_, v_params_2803_);
v___x_2816_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_2799_, v_params_2803_);
v___x_2817_ = l_Lean_mkConst(v_declName_2814_, v_us_2800_);
v___x_2818_ = l_Lean_mkAppN(v___x_2817_, v___x_2815_);
lean_dec_ref(v___x_2815_);
v___x_2819_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_2801_, v___x_2818_, v___x_2802_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; uint8_t v___x_2823_; lean_object* v___x_2824_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
lean_dec_ref_known(v___x_2819_, 1);
v___x_2821_ = l_Lean_Expr_beta(v_a_2820_, v___x_2816_);
v___x_2822_ = 0;
v___x_2823_ = 1;
v___x_2824_ = l_Lean_Meta_mkLambdaFVars(v_params_2803_, v___x_2821_, v___x_2822_, v___x_2811_, v___x_2822_, v___x_2811_, v___x_2823_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
return v___x_2824_;
}
else
{
lean_dec_ref(v___x_2816_);
return v___x_2819_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2797_ = stack[0].m_obj;
lean_object* v_unaryPreDefNonRec_2798_ = stack[1].m_obj;
lean_object* v___x_2799_ = stack[2].m_obj;
lean_object* v_us_2800_ = stack[3].m_obj;
lean_object* v_argsPacker_2801_ = stack[4].m_obj;
lean_object* v___x_2802_ = stack[5].m_obj;
lean_object* v_params_2803_ = stack[6].m_obj;
lean_object* v_x_2804_ = stack[7].m_obj;
lean_object* v___y_2805_ = stack[8].m_obj;
lean_object* v___y_2806_ = stack[9].m_obj;
lean_object* v___y_2807_ = stack[10].m_obj;
lean_object* v___y_2808_ = stack[11].m_obj;
lean_object* v_res_2825_;
v_res_2825_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(v___x_2797_, v_unaryPreDefNonRec_2798_, v___x_2799_, v_us_2800_, v_argsPacker_2801_, v___x_2802_, v_params_2803_, v_x_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
stack->m_obj
 = v_res_2825_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed(lean_object* v___x_2826_, lean_object* v_unaryPreDefNonRec_2827_, lean_object* v___x_2828_, lean_object* v_us_2829_, lean_object* v_argsPacker_2830_, lean_object* v___x_2831_, lean_object* v_params_2832_, lean_object* v_x_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(v___x_2826_, v_unaryPreDefNonRec_2827_, v___x_2828_, v_us_2829_, v_argsPacker_2830_, v___x_2831_, v_params_2832_, v_x_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec_ref(v_x_2833_);
lean_dec_ref(v_params_2832_);
lean_dec_ref(v_argsPacker_2830_);
lean_dec_ref(v___x_2828_);
lean_dec(v___x_2826_);
return v_res_2839_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2850_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5));
v___x_2852_ = l_Lean_Name_append(v___x_2851_, v___x_2850_);
return v___x_2852_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7));
v___x_2855_ = l_Lean_stringToMessageData(v___x_2854_);
return v___x_2855_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(lean_object* v_fixedParamPerms_2856_, lean_object* v_unaryPreDefNonRec_2857_, lean_object* v_us_2858_, lean_object* v_argsPacker_2859_, size_t v_sz_2860_, size_t v_i_2861_, lean_object* v_bs_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
uint8_t v___x_2868_; 
v___x_2868_ = lean_usize_dec_lt(v_i_2861_, v_sz_2860_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2869_; 
lean_dec_ref(v_argsPacker_2859_);
lean_dec(v_us_2858_);
lean_dec_ref(v_unaryPreDefNonRec_2857_);
v___x_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2869_, 0, v_bs_2862_);
return v___x_2869_;
}
else
{
lean_object* v_v_2870_; lean_object* v_perms_2871_; lean_object* v_ref_2872_; uint8_t v_kind_2873_; lean_object* v_levelParams_2874_; lean_object* v_modifiers_2875_; lean_object* v_declName_2876_; lean_object* v_binders_2877_; lean_object* v_numSectionVars_2878_; lean_object* v_type_2879_; lean_object* v_termination_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2932_; 
v_v_2870_ = lean_array_uget(v_bs_2862_, v_i_2861_);
v_perms_2871_ = lean_ctor_get(v_fixedParamPerms_2856_, 1);
v_ref_2872_ = lean_ctor_get(v_v_2870_, 0);
v_kind_2873_ = lean_ctor_get_uint8(v_v_2870_, sizeof(void*)*9);
v_levelParams_2874_ = lean_ctor_get(v_v_2870_, 1);
v_modifiers_2875_ = lean_ctor_get(v_v_2870_, 2);
v_declName_2876_ = lean_ctor_get(v_v_2870_, 3);
v_binders_2877_ = lean_ctor_get(v_v_2870_, 4);
v_numSectionVars_2878_ = lean_ctor_get(v_v_2870_, 5);
v_type_2879_ = lean_ctor_get(v_v_2870_, 6);
v_termination_2880_ = lean_ctor_get(v_v_2870_, 8);
v_isSharedCheck_2932_ = !lean_is_exclusive(v_v_2870_);
if (v_isSharedCheck_2932_ == 0)
{
lean_object* v_unused_2933_; 
v_unused_2933_ = lean_ctor_get(v_v_2870_, 7);
lean_dec(v_unused_2933_);
v___x_2882_ = v_v_2870_;
v_isShared_2883_ = v_isSharedCheck_2932_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_termination_2880_);
lean_inc(v_type_2879_);
lean_inc(v_numSectionVars_2878_);
lean_inc(v_binders_2877_);
lean_inc(v_declName_2876_);
lean_inc(v_modifiers_2875_);
lean_inc(v_levelParams_2874_);
lean_inc(v_ref_2872_);
lean_dec(v_v_2870_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2932_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2884_; lean_object* v_bs_x27_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___f_2890_; lean_object* v___x_2891_; uint8_t v___x_2892_; lean_object* v___x_2893_; 
v___x_2884_ = lean_unsigned_to_nat(0u);
v_bs_x27_2885_ = lean_array_uset(v_bs_2862_, v_i_2861_, v___x_2884_);
v___x_2886_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2887_ = lean_usize_to_nat(v_i_2861_);
v___x_2888_ = lean_array_get_borrowed(v___x_2886_, v_perms_2871_, v___x_2887_);
v___x_2889_ = lean_array_get_size(v___x_2888_);
lean_inc_ref(v_argsPacker_2859_);
lean_inc(v_us_2858_);
lean_inc(v___x_2888_);
lean_inc_ref(v_unaryPreDefNonRec_2857_);
v___f_2890_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2890_, 0, v___x_2889_);
lean_closure_set(v___f_2890_, 1, v_unaryPreDefNonRec_2857_);
lean_closure_set(v___f_2890_, 2, v___x_2888_);
lean_closure_set(v___f_2890_, 3, v_us_2858_);
lean_closure_set(v___f_2890_, 4, v_argsPacker_2859_);
lean_closure_set(v___f_2890_, 5, v___x_2887_);
v___x_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2889_);
v___x_2892_ = 0;
lean_inc_ref(v_type_2879_);
v___x_2893_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2879_, v___x_2891_, v___f_2890_, v___x_2892_, v___x_2892_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v_toCold_2903_; lean_object* v_options_2904_; uint8_t v_hasTrace_2905_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2893_, 1);
v_toCold_2903_ = lean_ctor_get(v___y_2865_, 0);
v_options_2904_ = lean_ctor_get(v_toCold_2903_, 2);
v_hasTrace_2905_ = lean_ctor_get_uint8(v_options_2904_, sizeof(void*)*1);
if (v_hasTrace_2905_ == 0)
{
goto v___jp_2895_;
}
else
{
lean_object* v_inheritedTraceOptions_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; uint8_t v___x_2909_; 
v_inheritedTraceOptions_2906_ = lean_ctor_get(v_toCold_2903_, 11);
v___x_2907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2908_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6);
v___x_2909_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2906_, v_options_2904_, v___x_2908_);
if (v___x_2909_ == 0)
{
goto v___jp_2895_;
}
else
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
lean_inc(v_declName_2876_);
v___x_2910_ = l_Lean_MessageData_ofName(v_declName_2876_);
v___x_2911_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8);
v___x_2912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2910_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
lean_inc(v_a_2894_);
v___x_2913_ = l_Lean_MessageData_ofExpr(v_a_2894_);
v___x_2914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2912_);
lean_ctor_set(v___x_2914_, 1, v___x_2913_);
v___x_2915_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v___x_2907_, v___x_2914_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_dec_ref_known(v___x_2915_, 1);
goto v___jp_2895_;
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec(v_a_2894_);
lean_dec_ref(v_bs_x27_2885_);
lean_del_object(v___x_2882_);
lean_dec_ref(v_termination_2880_);
lean_dec_ref(v_type_2879_);
lean_dec(v_numSectionVars_2878_);
lean_dec(v_binders_2877_);
lean_dec(v_declName_2876_);
lean_dec_ref(v_modifiers_2875_);
lean_dec(v_levelParams_2874_);
lean_dec(v_ref_2872_);
lean_dec_ref(v_argsPacker_2859_);
lean_dec(v_us_2858_);
lean_dec_ref(v_unaryPreDefNonRec_2857_);
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2915_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2915_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
}
v___jp_2895_:
{
lean_object* v___x_2897_; 
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 7, v_a_2894_);
v___x_2897_ = v___x_2882_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_ref_2872_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v_levelParams_2874_);
lean_ctor_set(v_reuseFailAlloc_2902_, 2, v_modifiers_2875_);
lean_ctor_set(v_reuseFailAlloc_2902_, 3, v_declName_2876_);
lean_ctor_set(v_reuseFailAlloc_2902_, 4, v_binders_2877_);
lean_ctor_set(v_reuseFailAlloc_2902_, 5, v_numSectionVars_2878_);
lean_ctor_set(v_reuseFailAlloc_2902_, 6, v_type_2879_);
lean_ctor_set(v_reuseFailAlloc_2902_, 7, v_a_2894_);
lean_ctor_set(v_reuseFailAlloc_2902_, 8, v_termination_2880_);
lean_ctor_set_uint8(v_reuseFailAlloc_2902_, sizeof(void*)*9, v_kind_2873_);
v___x_2897_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
size_t v___x_2898_; size_t v___x_2899_; lean_object* v___x_2900_; 
v___x_2898_ = ((size_t)1ULL);
v___x_2899_ = lean_usize_add(v_i_2861_, v___x_2898_);
v___x_2900_ = lean_array_uset(v_bs_x27_2885_, v_i_2861_, v___x_2897_);
v_i_2861_ = v___x_2899_;
v_bs_2862_ = v___x_2900_;
goto _start;
}
}
}
else
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
lean_dec_ref(v_bs_x27_2885_);
lean_del_object(v___x_2882_);
lean_dec_ref(v_termination_2880_);
lean_dec_ref(v_type_2879_);
lean_dec(v_numSectionVars_2878_);
lean_dec(v_binders_2877_);
lean_dec(v_declName_2876_);
lean_dec_ref(v_modifiers_2875_);
lean_dec(v_levelParams_2874_);
lean_dec(v_ref_2872_);
lean_dec_ref(v_argsPacker_2859_);
lean_dec(v_us_2858_);
lean_dec_ref(v_unaryPreDefNonRec_2857_);
v_a_2924_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2893_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2893_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fixedParamPerms_2856_ = stack[0].m_obj;
lean_object* v_unaryPreDefNonRec_2857_ = stack[1].m_obj;
lean_object* v_us_2858_ = stack[2].m_obj;
lean_object* v_argsPacker_2859_ = stack[3].m_obj;
size_t v_sz_2860_ = stack[4].m_num;
size_t v_i_2861_ = stack[5].m_num;
lean_object* v_bs_2862_ = stack[6].m_obj;
lean_object* v___y_2863_ = stack[7].m_obj;
lean_object* v___y_2864_ = stack[8].m_obj;
lean_object* v___y_2865_ = stack[9].m_obj;
lean_object* v___y_2866_ = stack[10].m_obj;
lean_object* v_res_2934_;
v_res_2934_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2856_, v_unaryPreDefNonRec_2857_, v_us_2858_, v_argsPacker_2859_, v_sz_2860_, v_i_2861_, v_bs_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
stack->m_obj
 = v_res_2934_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_2935_, lean_object* v_unaryPreDefNonRec_2936_, lean_object* v_us_2937_, lean_object* v_argsPacker_2938_, lean_object* v_sz_2939_, lean_object* v_i_2940_, lean_object* v_bs_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
size_t v_sz_boxed_2947_; size_t v_i_boxed_2948_; lean_object* v_res_2949_; 
v_sz_boxed_2947_ = lean_unbox_usize(v_sz_2939_);
lean_dec(v_sz_2939_);
v_i_boxed_2948_ = lean_unbox_usize(v_i_2940_);
lean_dec(v_i_2940_);
v_res_2949_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2935_, v_unaryPreDefNonRec_2936_, v_us_2937_, v_argsPacker_2938_, v_sz_boxed_2947_, v_i_boxed_2948_, v_bs_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec_ref(v_fixedParamPerms_2935_);
return v_res_2949_;
}
}
lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(lean_object* v_unaryPreDefNonRec_2950_, lean_object* v_preDefs_2951_, lean_object* v_fixedParamPerms_2952_, lean_object* v_us_2953_, lean_object* v_argsPacker_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Lean_Elab_addAsAxiom___redArg(v_unaryPreDefNonRec_2950_, v___y_2957_, v___y_2958_);
if (lean_obj_tag(v___x_2960_) == 0)
{
size_t v_sz_2961_; size_t v___x_2962_; lean_object* v___x_2963_; 
lean_dec_ref_known(v___x_2960_, 1);
v_sz_2961_ = lean_array_size(v_preDefs_2951_);
v___x_2962_ = ((size_t)0ULL);
v___x_2963_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2952_, v_unaryPreDefNonRec_2950_, v_us_2953_, v_argsPacker_2954_, v_sz_2961_, v___x_2962_, v_preDefs_2951_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
return v___x_2963_;
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_dec_ref(v_argsPacker_2954_);
lean_dec(v_us_2953_);
lean_dec_ref(v_preDefs_2951_);
lean_dec_ref(v_unaryPreDefNonRec_2950_);
v_a_2964_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2960_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2960_);
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
LEAN_EXPORT void l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_unaryPreDefNonRec_2950_ = stack[0].m_obj;
lean_object* v_preDefs_2951_ = stack[1].m_obj;
lean_object* v_fixedParamPerms_2952_ = stack[2].m_obj;
lean_object* v_us_2953_ = stack[3].m_obj;
lean_object* v_argsPacker_2954_ = stack[4].m_obj;
lean_object* v___y_2955_ = stack[5].m_obj;
lean_object* v___y_2956_ = stack[6].m_obj;
lean_object* v___y_2957_ = stack[7].m_obj;
lean_object* v___y_2958_ = stack[8].m_obj;
lean_object* v_res_2972_;
v_res_2972_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(v_unaryPreDefNonRec_2950_, v_preDefs_2951_, v_fixedParamPerms_2952_, v_us_2953_, v_argsPacker_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
stack->m_obj
 = v_res_2972_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed(lean_object* v_unaryPreDefNonRec_2973_, lean_object* v_preDefs_2974_, lean_object* v_fixedParamPerms_2975_, lean_object* v_us_2976_, lean_object* v_argsPacker_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(v_unaryPreDefNonRec_2973_, v_preDefs_2974_, v_fixedParamPerms_2975_, v_us_2976_, v_argsPacker_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec_ref(v_fixedParamPerms_2975_);
return v_res_2983_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2984_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0);
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
return v___x_2986_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
v___x_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
return v___x_2988_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2989_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
v___x_2990_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
lean_ctor_set(v___x_2990_, 2, v___x_2989_);
lean_ctor_set(v___x_2990_, 3, v___x_2989_);
lean_ctor_set(v___x_2990_, 4, v___x_2989_);
lean_ctor_set(v___x_2990_, 5, v___x_2989_);
return v___x_2990_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(lean_object* v_env_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v___x_2995_; lean_object* v_nextMacroScope_2996_; lean_object* v_ngen_2997_; lean_object* v_auxDeclNGen_2998_; lean_object* v_traceState_2999_; lean_object* v_recordedDeps_3000_; lean_object* v_messages_3001_; lean_object* v_infoState_3002_; lean_object* v_snapshotTasks_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3029_; 
v___x_2995_ = lean_st_ref_take(v___y_2993_);
v_nextMacroScope_2996_ = lean_ctor_get(v___x_2995_, 1);
v_ngen_2997_ = lean_ctor_get(v___x_2995_, 2);
v_auxDeclNGen_2998_ = lean_ctor_get(v___x_2995_, 3);
v_traceState_2999_ = lean_ctor_get(v___x_2995_, 4);
v_recordedDeps_3000_ = lean_ctor_get(v___x_2995_, 6);
v_messages_3001_ = lean_ctor_get(v___x_2995_, 7);
v_infoState_3002_ = lean_ctor_get(v___x_2995_, 8);
v_snapshotTasks_3003_ = lean_ctor_get(v___x_2995_, 9);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3029_ == 0)
{
lean_object* v_unused_3030_; lean_object* v_unused_3031_; 
v_unused_3030_ = lean_ctor_get(v___x_2995_, 5);
lean_dec(v_unused_3030_);
v_unused_3031_ = lean_ctor_get(v___x_2995_, 0);
lean_dec(v_unused_3031_);
v___x_3005_ = v___x_2995_;
v_isShared_3006_ = v_isSharedCheck_3029_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_snapshotTasks_3003_);
lean_inc(v_infoState_3002_);
lean_inc(v_messages_3001_);
lean_inc(v_recordedDeps_3000_);
lean_inc(v_traceState_2999_);
lean_inc(v_auxDeclNGen_2998_);
lean_inc(v_ngen_2997_);
lean_inc(v_nextMacroScope_2996_);
lean_dec(v___x_2995_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3029_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3007_; lean_object* v___x_3009_; 
v___x_3007_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2);
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 5, v___x_3007_);
lean_ctor_set(v___x_3005_, 0, v_env_2991_);
v___x_3009_ = v___x_3005_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_env_2991_);
lean_ctor_set(v_reuseFailAlloc_3028_, 1, v_nextMacroScope_2996_);
lean_ctor_set(v_reuseFailAlloc_3028_, 2, v_ngen_2997_);
lean_ctor_set(v_reuseFailAlloc_3028_, 3, v_auxDeclNGen_2998_);
lean_ctor_set(v_reuseFailAlloc_3028_, 4, v_traceState_2999_);
lean_ctor_set(v_reuseFailAlloc_3028_, 5, v___x_3007_);
lean_ctor_set(v_reuseFailAlloc_3028_, 6, v_recordedDeps_3000_);
lean_ctor_set(v_reuseFailAlloc_3028_, 7, v_messages_3001_);
lean_ctor_set(v_reuseFailAlloc_3028_, 8, v_infoState_3002_);
lean_ctor_set(v_reuseFailAlloc_3028_, 9, v_snapshotTasks_3003_);
v___x_3009_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v_mctx_3012_; lean_object* v_zetaDeltaFVarIds_3013_; lean_object* v_postponed_3014_; lean_object* v_diag_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3026_; 
v___x_3010_ = lean_st_ref_put(v___y_2993_, v___x_3009_);
v___x_3011_ = lean_st_ref_take(v___y_2992_);
v_mctx_3012_ = lean_ctor_get(v___x_3011_, 0);
v_zetaDeltaFVarIds_3013_ = lean_ctor_get(v___x_3011_, 2);
v_postponed_3014_ = lean_ctor_get(v___x_3011_, 3);
v_diag_3015_ = lean_ctor_get(v___x_3011_, 4);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3026_ == 0)
{
lean_object* v_unused_3027_; 
v_unused_3027_ = lean_ctor_get(v___x_3011_, 1);
lean_dec(v_unused_3027_);
v___x_3017_ = v___x_3011_;
v_isShared_3018_ = v_isSharedCheck_3026_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_diag_3015_);
lean_inc(v_postponed_3014_);
lean_inc(v_zetaDeltaFVarIds_3013_);
lean_inc(v_mctx_3012_);
lean_dec(v___x_3011_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3026_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3022_; 
v___x_3019_ = lean_box(0);
v___x_3020_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3);
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 1, v___x_3020_);
v___x_3022_ = v___x_3017_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_mctx_3012_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v___x_3020_);
lean_ctor_set(v_reuseFailAlloc_3025_, 2, v_zetaDeltaFVarIds_3013_);
lean_ctor_set(v_reuseFailAlloc_3025_, 3, v_postponed_3014_);
lean_ctor_set(v_reuseFailAlloc_3025_, 4, v_diag_3015_);
v___x_3022_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = lean_st_ref_put(v___y_2992_, v___x_3022_);
v___x_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3019_);
return v___x_3024_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2991_ = stack[0].m_obj;
lean_object* v___y_2992_ = stack[1].m_obj;
lean_object* v___y_2993_ = stack[2].m_obj;
lean_object* v_res_3032_;
v_res_3032_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2991_, v___y_2992_, v___y_2993_);
stack->m_obj
 = v_res_3032_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___boxed(lean_object* v_env_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3033_, v___y_3034_, v___y_3035_);
lean_dec(v___y_3035_);
lean_dec(v___y_3034_);
return v_res_3037_;
}
}
lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(lean_object* v_env_3038_, lean_object* v_x_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v___x_3045_; lean_object* v_env_3046_; lean_object* v_a_3048_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3045_ = lean_st_ref_get(v___y_3043_);
v_env_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc_ref(v_env_3046_);
lean_dec(v___x_3045_);
v___x_3058_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3038_, v___y_3041_, v___y_3043_);
lean_dec_ref(v___x_3058_);
lean_inc(v___y_3043_);
lean_inc_ref(v___y_3042_);
lean_inc(v___y_3041_);
lean_inc_ref(v___y_3040_);
v___x_3059_ = lean_apply_5(v_x_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, lean_box(0));
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; lean_object* v___x_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3060_);
lean_dec_ref_known(v___x_3059_, 1);
v___x_3061_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3046_, v___y_3041_, v___y_3043_);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3068_ == 0)
{
lean_object* v_unused_3069_; 
v_unused_3069_ = lean_ctor_get(v___x_3061_, 0);
lean_dec(v_unused_3069_);
v___x_3063_ = v___x_3061_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_dec(v___x_3061_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
lean_ctor_set(v___x_3063_, 0, v_a_3060_);
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3060_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
else
{
lean_object* v_a_3070_; 
v_a_3070_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3070_);
lean_dec_ref_known(v___x_3059_, 1);
v_a_3048_ = v_a_3070_;
goto v___jp_3047_;
}
v___jp_3047_:
{
lean_object* v___x_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
v___x_3049_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3046_, v___y_3041_, v___y_3043_);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3056_ == 0)
{
lean_object* v_unused_3057_; 
v_unused_3057_ = lean_ctor_get(v___x_3049_, 0);
lean_dec(v_unused_3057_);
v___x_3051_ = v___x_3049_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_dec(v___x_3049_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
lean_ctor_set_tag(v___x_3051_, 1);
lean_ctor_set(v___x_3051_, 0, v_a_3048_);
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3048_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_3038_ = stack[0].m_obj;
lean_object* v_x_3039_ = stack[1].m_obj;
lean_object* v___y_3040_ = stack[2].m_obj;
lean_object* v___y_3041_ = stack[3].m_obj;
lean_object* v___y_3042_ = stack[4].m_obj;
lean_object* v___y_3043_ = stack[5].m_obj;
lean_object* v_res_3071_;
v_res_3071_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_3038_, v_x_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
stack->m_obj
 = v_res_3071_;
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___boxed(lean_object* v_env_3072_, lean_object* v_x_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_3072_, v_x_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
return v_res_3079_;
}
}
lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object* v_fixedParamPerms_3080_, lean_object* v_argsPacker_3081_, lean_object* v_preDefs_3082_, lean_object* v_unaryPreDefNonRec_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_){
_start:
{
lean_object* v_levelParams_3089_; lean_object* v___x_3090_; lean_object* v_us_3091_; lean_object* v___f_3092_; lean_object* v___x_3093_; lean_object* v_env_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v_levelParams_3089_ = lean_ctor_get(v_unaryPreDefNonRec_3083_, 1);
v___x_3090_ = lean_box(0);
lean_inc(v_levelParams_3089_);
v_us_3091_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_3089_, v___x_3090_);
v___f_3092_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3092_, 0, v_unaryPreDefNonRec_3083_);
lean_closure_set(v___f_3092_, 1, v_preDefs_3082_);
lean_closure_set(v___f_3092_, 2, v_fixedParamPerms_3080_);
lean_closure_set(v___f_3092_, 3, v_us_3091_);
lean_closure_set(v___f_3092_, 4, v_argsPacker_3081_);
v___x_3093_ = lean_st_ref_get(v_a_3087_);
v_env_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc_ref(v_env_3094_);
lean_dec(v___x_3093_);
v___x_3095_ = l_Lean_Environment_unlockAsync(v_env_3094_);
v___x_3096_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v___x_3095_, v___f_3092_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
return v___x_3096_;
}
}
LEAN_EXPORT void l_Lean_Elab_WF_preDefsFromUnaryNonRec_0interp(lean_interpreter_value* stack)
{
lean_object* v_fixedParamPerms_3080_ = stack[0].m_obj;
lean_object* v_argsPacker_3081_ = stack[1].m_obj;
lean_object* v_preDefs_3082_ = stack[2].m_obj;
lean_object* v_unaryPreDefNonRec_3083_ = stack[3].m_obj;
lean_object* v_a_3084_ = stack[4].m_obj;
lean_object* v_a_3085_ = stack[5].m_obj;
lean_object* v_a_3086_ = stack[6].m_obj;
lean_object* v_a_3087_ = stack[7].m_obj;
lean_object* v_res_3097_;
v_res_3097_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fixedParamPerms_3080_, v_argsPacker_3081_, v_preDefs_3082_, v_unaryPreDefNonRec_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
stack->m_obj
 = v_res_3097_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___boxed(lean_object* v_fixedParamPerms_3098_, lean_object* v_argsPacker_3099_, lean_object* v_preDefs_3100_, lean_object* v_unaryPreDefNonRec_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fixedParamPerms_3098_, v_argsPacker_3099_, v_preDefs_3100_, v_unaryPreDefNonRec_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
lean_dec(v_a_3105_);
lean_dec_ref(v_a_3104_);
lean_dec(v_a_3103_);
lean_dec_ref(v_a_3102_);
return v_res_3107_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(lean_object* v_fixedParamPerms_3108_, lean_object* v_unaryPreDefNonRec_3109_, lean_object* v_us_3110_, lean_object* v_argsPacker_3111_, lean_object* v_as_3112_, size_t v_sz_3113_, size_t v_i_3114_, lean_object* v_bs_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_3108_, v_unaryPreDefNonRec_3109_, v_us_3110_, v_argsPacker_3111_, v_sz_3113_, v_i_3114_, v_bs_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
return v___x_3121_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_fixedParamPerms_3108_ = stack[0].m_obj;
lean_object* v_unaryPreDefNonRec_3109_ = stack[1].m_obj;
lean_object* v_us_3110_ = stack[2].m_obj;
lean_object* v_argsPacker_3111_ = stack[3].m_obj;
lean_object* v_as_3112_ = stack[4].m_obj;
size_t v_sz_3113_ = stack[5].m_num;
size_t v_i_3114_ = stack[6].m_num;
lean_object* v_bs_3115_ = stack[7].m_obj;
lean_object* v___y_3116_ = stack[8].m_obj;
lean_object* v___y_3117_ = stack[9].m_obj;
lean_object* v___y_3118_ = stack[10].m_obj;
lean_object* v___y_3119_ = stack[11].m_obj;
lean_object* v_res_3122_;
v_res_3122_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(v_fixedParamPerms_3108_, v_unaryPreDefNonRec_3109_, v_us_3110_, v_argsPacker_3111_, v_as_3112_, v_sz_3113_, v_i_3114_, v_bs_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
stack->m_obj
 = v_res_3122_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___boxed(lean_object* v_fixedParamPerms_3123_, lean_object* v_unaryPreDefNonRec_3124_, lean_object* v_us_3125_, lean_object* v_argsPacker_3126_, lean_object* v_as_3127_, lean_object* v_sz_3128_, lean_object* v_i_3129_, lean_object* v_bs_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
size_t v_sz_boxed_3136_; size_t v_i_boxed_3137_; lean_object* v_res_3138_; 
v_sz_boxed_3136_ = lean_unbox_usize(v_sz_3128_);
lean_dec(v_sz_3128_);
v_i_boxed_3137_ = lean_unbox_usize(v_i_3129_);
lean_dec(v_i_3129_);
v_res_3138_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(v_fixedParamPerms_3123_, v_unaryPreDefNonRec_3124_, v_us_3125_, v_argsPacker_3126_, v_as_3127_, v_sz_boxed_3136_, v_i_boxed_3137_, v_bs_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec_ref(v_as_3127_);
lean_dec_ref(v_fixedParamPerms_3123_);
return v_res_3138_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(lean_object* v_env_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3139_, v___y_3141_, v___y_3143_);
return v___x_3145_;
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_3139_ = stack[0].m_obj;
lean_object* v___y_3140_ = stack[1].m_obj;
lean_object* v___y_3141_ = stack[2].m_obj;
lean_object* v___y_3142_ = stack[3].m_obj;
lean_object* v___y_3143_ = stack[4].m_obj;
lean_object* v_res_3146_;
v_res_3146_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(v_env_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
stack->m_obj
 = v_res_3146_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___boxed(lean_object* v_env_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(v_env_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
return v_res_3153_;
}
}
lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(lean_object* v_00_u03b1_3154_, lean_object* v_env_3155_, lean_object* v_x_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v___x_3162_; 
v___x_3162_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_3155_, v_x_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
return v___x_3162_;
}
}
LEAN_EXPORT void l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_3155_ = stack[1].m_obj;
lean_object* v_x_3156_ = stack[2].m_obj;
lean_object* v___y_3157_ = stack[3].m_obj;
lean_object* v___y_3158_ = stack[4].m_obj;
lean_object* v___y_3159_ = stack[5].m_obj;
lean_object* v___y_3160_ = stack[6].m_obj;
lean_object* v_res_3163_;
v_res_3163_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(lean_box(0), v_env_3155_, v_x_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
stack->m_obj
 = v_res_3163_;
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___boxed(lean_object* v_00_u03b1_3164_, lean_object* v_env_3165_, lean_object* v_x_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(v_00_u03b1_3164_, v_env_3165_, v_x_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
return v_res_3172_;
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
