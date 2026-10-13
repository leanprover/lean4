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
lean_object* v___x_1892_; uint8_t v___y_1894_; uint8_t v___x_1911_; 
v___x_1892_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1911_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_1889_);
if (v___x_1911_ == 0)
{
v___y_1894_ = v___x_1911_;
goto v___jp_1893_;
}
else
{
uint8_t v___x_1912_; 
v___x_1912_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_1890_);
v___y_1894_ = v___x_1912_;
goto v___jp_1893_;
}
v___jp_1893_:
{
if (v___y_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1895_ = lean_unsigned_to_nat(1u);
v___x_1896_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_1890_);
v___x_1897_ = lean_nat_dec_lt(v___x_1895_, v___x_1896_);
lean_dec(v___x_1896_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v_declName_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1898_ = lean_unsigned_to_nat(0u);
v___x_1899_ = lean_array_get_borrowed(v___x_1892_, v_preDefs_1891_, v___x_1898_);
v_declName_1900_ = lean_ctor_get(v___x_1899_, 3);
v___x_1901_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__1));
lean_inc(v_declName_1900_);
v___x_1902_ = l_Lean_Name_append(v_declName_1900_, v___x_1901_);
return v___x_1902_;
}
else
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v_declName_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1903_ = lean_unsigned_to_nat(0u);
v___x_1904_ = lean_array_get_borrowed(v___x_1892_, v_preDefs_1891_, v___x_1903_);
v_declName_1905_ = lean_ctor_get(v___x_1904_, 3);
v___x_1906_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__3));
lean_inc(v_declName_1905_);
v___x_1907_ = l_Lean_Name_append(v_declName_1905_, v___x_1906_);
return v___x_1907_;
}
}
else
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v_declName_1910_; 
v___x_1908_ = lean_unsigned_to_nat(0u);
v___x_1909_ = lean_array_get_borrowed(v___x_1892_, v_preDefs_1891_, v___x_1908_);
v_declName_1910_ = lean_ctor_get(v___x_1909_, 3);
lean_inc(v_declName_1910_);
return v_declName_1910_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName___boxed(lean_object* v_fixedParamPerms_1913_, lean_object* v_argsPacker_1914_, lean_object* v_preDefs_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_1913_, v_argsPacker_1914_, v_preDefs_1915_);
lean_dec_ref(v_preDefs_1915_);
lean_dec_ref(v_argsPacker_1914_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(lean_object* v_k_1917_, lean_object* v_b_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v___x_1924_; 
lean_inc(v___y_1922_);
lean_inc_ref(v___y_1921_);
lean_inc(v___y_1920_);
lean_inc_ref(v___y_1919_);
v___x_1924_ = lean_apply_6(v_k_1917_, v_b_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, lean_box(0));
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed(lean_object* v_k_1925_, lean_object* v_b_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(v_k_1925_, v_b_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(lean_object* v_perm_1933_, lean_object* v_type_1934_, lean_object* v_k_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v___f_1941_; lean_object* v___x_1942_; 
v___f_1941_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1941_, 0, v_k_1935_);
v___x_1942_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_1933_, v_type_1934_, v___f_1941_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
v_a_1951_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1942_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1942_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___boxed(lean_object* v_perm_1959_, lean_object* v_type_1960_, lean_object* v_k_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_1959_, v_type_1960_, v_k_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(lean_object* v_00_u03b1_1968_, lean_object* v_perm_1969_, lean_object* v_type_1970_, lean_object* v_k_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_1969_, v_type_1970_, v_k_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___boxed(lean_object* v_00_u03b1_1978_, lean_object* v_perm_1979_, lean_object* v_type_1980_, lean_object* v_k_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(v_00_u03b1_1978_, v_perm_1979_, v_type_1980_, v_k_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(lean_object* v___x_1988_, lean_object* v_ys_1989_, size_t v_sz_1990_, size_t v_i_1991_, lean_object* v_bs_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
uint8_t v___x_1998_; 
v___x_1998_ = lean_usize_dec_lt(v_i_1991_, v_sz_1990_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; 
lean_dec_ref(v_ys_1989_);
v___x_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1999_, 0, v_bs_1992_);
return v___x_1999_;
}
else
{
lean_object* v_v_2000_; lean_object* v_value_2001_; lean_object* v___x_2002_; lean_object* v_bs_x27_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v_v_2000_ = lean_array_uget_borrowed(v_bs_1992_, v_i_1991_);
v_value_2001_ = lean_ctor_get(v_v_2000_, 7);
lean_inc_ref(v_value_2001_);
v___x_2002_ = lean_unsigned_to_nat(0u);
v_bs_x27_2003_ = lean_array_uset(v_bs_1992_, v_i_1991_, v___x_2002_);
v___x_2004_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2005_ = lean_usize_to_nat(v_i_1991_);
v___x_2006_ = lean_array_get_borrowed(v___x_2004_, v___x_1988_, v___x_2005_);
lean_dec(v___x_2005_);
lean_inc_ref(v_ys_1989_);
lean_inc(v___x_2006_);
v___x_2007_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_2006_, v_value_2001_, v_ys_1989_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; size_t v___x_2009_; size_t v___x_2010_; lean_object* v___x_2011_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref_known(v___x_2007_, 1);
v___x_2009_ = ((size_t)1ULL);
v___x_2010_ = lean_usize_add(v_i_1991_, v___x_2009_);
v___x_2011_ = lean_array_uset(v_bs_x27_2003_, v_i_1991_, v_a_2008_);
v_i_1991_ = v___x_2010_;
v_bs_1992_ = v___x_2011_;
goto _start;
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec_ref(v_bs_x27_2003_);
lean_dec_ref(v_ys_1989_);
v_a_2013_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_2007_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2007_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg___boxed(lean_object* v___x_2021_, lean_object* v_ys_2022_, lean_object* v_sz_2023_, lean_object* v_i_2024_, lean_object* v_bs_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
size_t v_sz_boxed_2031_; size_t v_i_boxed_2032_; lean_object* v_res_2033_; 
v_sz_boxed_2031_ = lean_unbox_usize(v_sz_2023_);
lean_dec(v_sz_2023_);
v_i_boxed_2032_ = lean_unbox_usize(v_i_2024_);
lean_dec(v_i_2024_);
v_res_2033_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2021_, v_ys_2022_, v_sz_boxed_2031_, v_i_boxed_2032_, v_bs_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec_ref(v___x_2021_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(lean_object* v___x_2034_, lean_object* v_ys_2035_, size_t v_sz_2036_, size_t v_i_2037_, lean_object* v_bs_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
uint8_t v___x_2044_; 
v___x_2044_ = lean_usize_dec_lt(v_i_2037_, v_sz_2036_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2045_; 
lean_dec_ref(v_ys_2035_);
v___x_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2045_, 0, v_bs_2038_);
return v___x_2045_;
}
else
{
lean_object* v_v_2046_; lean_object* v_type_2047_; lean_object* v___x_2048_; lean_object* v_bs_x27_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v_v_2046_ = lean_array_uget_borrowed(v_bs_2038_, v_i_2037_);
v_type_2047_ = lean_ctor_get(v_v_2046_, 6);
lean_inc_ref(v_type_2047_);
v___x_2048_ = lean_unsigned_to_nat(0u);
v_bs_x27_2049_ = lean_array_uset(v_bs_2038_, v_i_2037_, v___x_2048_);
v___x_2050_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2051_ = lean_usize_to_nat(v_i_2037_);
v___x_2052_ = lean_array_get_borrowed(v___x_2050_, v___x_2034_, v___x_2051_);
lean_dec(v___x_2051_);
lean_inc_ref(v_ys_2035_);
lean_inc(v___x_2052_);
v___x_2053_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_2052_, v_type_2047_, v_ys_2035_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; size_t v___x_2055_; size_t v___x_2056_; lean_object* v___x_2057_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref_known(v___x_2053_, 1);
v___x_2055_ = ((size_t)1ULL);
v___x_2056_ = lean_usize_add(v_i_2037_, v___x_2055_);
v___x_2057_ = lean_array_uset(v_bs_x27_2049_, v_i_2037_, v_a_2054_);
v_i_2037_ = v___x_2056_;
v_bs_2038_ = v___x_2057_;
goto _start;
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec_ref(v_bs_x27_2049_);
lean_dec_ref(v_ys_2035_);
v_a_2059_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2053_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2053_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg___boxed(lean_object* v___x_2067_, lean_object* v_ys_2068_, lean_object* v_sz_2069_, lean_object* v_i_2070_, lean_object* v_bs_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
size_t v_sz_boxed_2077_; size_t v_i_boxed_2078_; lean_object* v_res_2079_; 
v_sz_boxed_2077_ = lean_unbox_usize(v_sz_2069_);
lean_dec(v_sz_2069_);
v_i_boxed_2078_ = lean_unbox_usize(v_i_2070_);
lean_dec(v_i_2070_);
v_res_2079_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2067_, v_ys_2068_, v_sz_boxed_2077_, v_i_boxed_2078_, v_bs_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec_ref(v___x_2067_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(lean_object* v_a_2080_, lean_object* v_a_2081_){
_start:
{
if (lean_obj_tag(v_a_2080_) == 0)
{
lean_object* v___x_2082_; 
v___x_2082_ = l_List_reverse___redArg(v_a_2081_);
return v___x_2082_;
}
else
{
lean_object* v_head_2083_; lean_object* v_tail_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2093_; 
v_head_2083_ = lean_ctor_get(v_a_2080_, 0);
v_tail_2084_ = lean_ctor_get(v_a_2080_, 1);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_a_2080_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2086_ = v_a_2080_;
v_isShared_2087_ = v_isSharedCheck_2093_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_tail_2084_);
lean_inc(v_head_2083_);
lean_dec(v_a_2080_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2093_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; lean_object* v___x_2090_; 
v___x_2088_ = l_Lean_mkLevelParam(v_head_2083_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 1, v_a_2081_);
lean_ctor_set(v___x_2086_, 0, v___x_2088_);
v___x_2090_ = v___x_2086_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_a_2081_);
v___x_2090_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
v_a_2080_ = v_tail_2084_;
v_a_2081_ = v___x_2090_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(size_t v_sz_2094_, size_t v_i_2095_, lean_object* v_bs_2096_){
_start:
{
uint8_t v___x_2097_; 
v___x_2097_ = lean_usize_dec_lt(v_i_2095_, v_sz_2094_);
if (v___x_2097_ == 0)
{
return v_bs_2096_;
}
else
{
lean_object* v_v_2098_; lean_object* v_declName_2099_; lean_object* v___x_2100_; lean_object* v_bs_x27_2101_; size_t v___x_2102_; size_t v___x_2103_; lean_object* v___x_2104_; 
v_v_2098_ = lean_array_uget_borrowed(v_bs_2096_, v_i_2095_);
v_declName_2099_ = lean_ctor_get(v_v_2098_, 3);
lean_inc(v_declName_2099_);
v___x_2100_ = lean_unsigned_to_nat(0u);
v_bs_x27_2101_ = lean_array_uset(v_bs_2096_, v_i_2095_, v___x_2100_);
v___x_2102_ = ((size_t)1ULL);
v___x_2103_ = lean_usize_add(v_i_2095_, v___x_2102_);
v___x_2104_ = lean_array_uset(v_bs_x27_2101_, v_i_2095_, v_declName_2099_);
v_i_2095_ = v___x_2103_;
v_bs_2096_ = v___x_2104_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3___boxed(lean_object* v_sz_2106_, lean_object* v_i_2107_, lean_object* v_bs_2108_){
_start:
{
size_t v_sz_boxed_2109_; size_t v_i_boxed_2110_; lean_object* v_res_2111_; 
v_sz_boxed_2109_ = lean_unbox_usize(v_sz_2106_);
lean_dec(v_sz_2106_);
v_i_boxed_2110_ = lean_unbox_usize(v_i_2107_);
lean_dec(v_i_2107_);
v_res_2111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_boxed_2109_, v_i_boxed_2110_, v_bs_2108_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0(lean_object* v_preDefs_2112_, lean_object* v_perms_2113_, lean_object* v_argsPacker_2114_, uint8_t v___x_2115_, lean_object* v_ref_2116_, uint8_t v_kind_2117_, lean_object* v_levelParams_2118_, lean_object* v_modifiers_2119_, lean_object* v_newFn_2120_, lean_object* v_binders_2121_, lean_object* v_numSectionVars_2122_, lean_object* v_value_2123_, lean_object* v_termination_2124_, lean_object* v_fixedParamPerms_2125_, lean_object* v_ys_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
size_t v_sz_2132_; size_t v___x_2133_; lean_object* v___x_2134_; 
v_sz_2132_ = lean_array_size(v_preDefs_2112_);
v___x_2133_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_2112_);
lean_inc_ref(v_ys_2126_);
v___x_2134_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v_perms_2113_, v_ys_2126_, v_sz_2132_, v___x_2133_, v_preDefs_2112_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2136_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
lean_inc_ref(v_preDefs_2112_);
lean_inc_ref(v_ys_2126_);
v___x_2136_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v_perms_2113_, v_ys_2126_, v_sz_2132_, v___x_2133_, v_preDefs_2112_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2138_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v___x_2138_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_2114_, v_a_2135_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v_a_2135_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; uint8_t v___x_2140_; uint8_t v___x_2141_; lean_object* v___x_2142_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
v___x_2140_ = 1;
v___x_2141_ = 1;
v___x_2142_ = l_Lean_Meta_mkForallFVars(v_ys_2126_, v_a_2139_, v___x_2115_, v___x_2140_, v___x_2140_, v___x_2141_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc_n(v_a_2143_, 2);
lean_dec_ref_known(v___x_2142_, 1);
lean_inc_ref(v_termination_2124_);
lean_inc(v_numSectionVars_2122_);
lean_inc(v_binders_2121_);
lean_inc(v_newFn_2120_);
lean_inc_ref(v_modifiers_2119_);
lean_inc(v_levelParams_2118_);
lean_inc(v_ref_2116_);
v___x_2144_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2144_, 0, v_ref_2116_);
lean_ctor_set(v___x_2144_, 1, v_levelParams_2118_);
lean_ctor_set(v___x_2144_, 2, v_modifiers_2119_);
lean_ctor_set(v___x_2144_, 3, v_newFn_2120_);
lean_ctor_set(v___x_2144_, 4, v_binders_2121_);
lean_ctor_set(v___x_2144_, 5, v_numSectionVars_2122_);
lean_ctor_set(v___x_2144_, 6, v_a_2143_);
lean_ctor_set(v___x_2144_, 7, v_value_2123_);
lean_ctor_set(v___x_2144_, 8, v_termination_2124_);
lean_ctor_set_uint8(v___x_2144_, sizeof(void*)*9, v_kind_2117_);
v___x_2145_ = l_Lean_Elab_addAsAxiom___redArg(v___x_2144_, v___y_2129_, v___y_2130_);
lean_dec_ref_known(v___x_2144_, 9);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
lean_dec_ref_known(v___x_2145_, 1);
v___x_2146_ = lean_box(0);
lean_inc(v_levelParams_2118_);
v___x_2147_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_2118_, v___x_2146_);
lean_inc(v_newFn_2120_);
v___x_2148_ = l_Lean_mkConst(v_newFn_2120_, v___x_2147_);
v___x_2149_ = l_Lean_mkAppN(v___x_2148_, v_ys_2126_);
v___x_2150_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_2114_, v_a_2137_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v_a_2137_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v___x_2150_, 1);
v___x_2152_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_2132_, v___x_2133_, v_preDefs_2112_);
v___x_2153_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_2125_, v_argsPacker_2114_, v___x_2152_, v___x_2149_, v_a_2151_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2155_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
lean_dec_ref_known(v___x_2153_, 1);
v___x_2155_ = l_Lean_Meta_mkLambdaFVars(v_ys_2126_, v_a_2154_, v___x_2115_, v___x_2140_, v___x_2115_, v___x_2140_, v___x_2141_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec_ref(v_ys_2126_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2164_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2158_ = v___x_2155_;
v_isShared_2159_ = v_isSharedCheck_2164_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2155_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2164_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2160_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2160_, 0, v_ref_2116_);
lean_ctor_set(v___x_2160_, 1, v_levelParams_2118_);
lean_ctor_set(v___x_2160_, 2, v_modifiers_2119_);
lean_ctor_set(v___x_2160_, 3, v_newFn_2120_);
lean_ctor_set(v___x_2160_, 4, v_binders_2121_);
lean_ctor_set(v___x_2160_, 5, v_numSectionVars_2122_);
lean_ctor_set(v___x_2160_, 6, v_a_2143_);
lean_ctor_set(v___x_2160_, 7, v_a_2156_);
lean_ctor_set(v___x_2160_, 8, v_termination_2124_);
lean_ctor_set_uint8(v___x_2160_, sizeof(void*)*9, v_kind_2117_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v___x_2160_);
v___x_2162_ = v___x_2158_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec(v_a_2143_);
lean_dec_ref(v_termination_2124_);
lean_dec(v_numSectionVars_2122_);
lean_dec(v_binders_2121_);
lean_dec(v_newFn_2120_);
lean_dec_ref(v_modifiers_2119_);
lean_dec(v_levelParams_2118_);
lean_dec(v_ref_2116_);
v_a_2165_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2155_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2155_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_a_2143_);
lean_dec_ref(v_ys_2126_);
lean_dec_ref(v_termination_2124_);
lean_dec(v_numSectionVars_2122_);
lean_dec(v_binders_2121_);
lean_dec(v_newFn_2120_);
lean_dec_ref(v_modifiers_2119_);
lean_dec(v_levelParams_2118_);
lean_dec(v_ref_2116_);
v_a_2173_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2153_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2153_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec_ref(v___x_2149_);
lean_dec(v_a_2143_);
lean_dec_ref(v_ys_2126_);
lean_dec_ref(v_fixedParamPerms_2125_);
lean_dec_ref(v_termination_2124_);
lean_dec(v_numSectionVars_2122_);
lean_dec(v_binders_2121_);
lean_dec(v_newFn_2120_);
lean_dec_ref(v_modifiers_2119_);
lean_dec(v_levelParams_2118_);
lean_dec(v_ref_2116_);
lean_dec_ref(v_argsPacker_2114_);
lean_dec_ref(v_preDefs_2112_);
v_a_2181_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2150_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2150_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v_a_2143_);
lean_dec(v_a_2137_);
lean_dec_ref(v_ys_2126_);
lean_dec_ref(v_fixedParamPerms_2125_);
lean_dec_ref(v_termination_2124_);
lean_dec(v_numSectionVars_2122_);
lean_dec(v_binders_2121_);
lean_dec(v_newFn_2120_);
lean_dec_ref(v_modifiers_2119_);
lean_dec(v_levelParams_2118_);
lean_dec(v_ref_2116_);
lean_dec_ref(v_argsPacker_2114_);
lean_dec_ref(v_preDefs_2112_);
v_a_2189_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2145_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2145_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec(v_a_2137_);
lean_dec_ref(v_ys_2126_);
lean_dec_ref(v_fixedParamPerms_2125_);
lean_dec_ref(v_termination_2124_);
lean_dec_ref(v_value_2123_);
lean_dec(v_numSectionVars_2122_);
lean_dec(v_binders_2121_);
lean_dec(v_newFn_2120_);
lean_dec_ref(v_modifiers_2119_);
lean_dec(v_levelParams_2118_);
lean_dec(v_ref_2116_);
lean_dec_ref(v_argsPacker_2114_);
lean_dec_ref(v_preDefs_2112_);
v_a_2197_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2142_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2142_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec(v_a_2137_);
lean_dec_ref(v_ys_2126_);
lean_dec_ref(v_fixedParamPerms_2125_);
lean_dec_ref(v_termination_2124_);
lean_dec_ref(v_value_2123_);
lean_dec(v_numSectionVars_2122_);
lean_dec(v_binders_2121_);
lean_dec(v_newFn_2120_);
lean_dec_ref(v_modifiers_2119_);
lean_dec(v_levelParams_2118_);
lean_dec(v_ref_2116_);
lean_dec_ref(v_argsPacker_2114_);
lean_dec_ref(v_preDefs_2112_);
v_a_2205_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2138_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2138_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec(v_a_2135_);
lean_dec_ref(v_ys_2126_);
lean_dec_ref(v_fixedParamPerms_2125_);
lean_dec_ref(v_termination_2124_);
lean_dec_ref(v_value_2123_);
lean_dec(v_numSectionVars_2122_);
lean_dec(v_binders_2121_);
lean_dec(v_newFn_2120_);
lean_dec_ref(v_modifiers_2119_);
lean_dec(v_levelParams_2118_);
lean_dec(v_ref_2116_);
lean_dec_ref(v_argsPacker_2114_);
lean_dec_ref(v_preDefs_2112_);
v_a_2213_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2136_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2136_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_dec_ref(v_ys_2126_);
lean_dec_ref(v_fixedParamPerms_2125_);
lean_dec_ref(v_termination_2124_);
lean_dec_ref(v_value_2123_);
lean_dec(v_numSectionVars_2122_);
lean_dec(v_binders_2121_);
lean_dec(v_newFn_2120_);
lean_dec_ref(v_modifiers_2119_);
lean_dec(v_levelParams_2118_);
lean_dec(v_ref_2116_);
lean_dec_ref(v_argsPacker_2114_);
lean_dec_ref(v_preDefs_2112_);
v_a_2221_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2134_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2134_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0___boxed(lean_object** _args){
lean_object* v_preDefs_2229_ = _args[0];
lean_object* v_perms_2230_ = _args[1];
lean_object* v_argsPacker_2231_ = _args[2];
lean_object* v___x_2232_ = _args[3];
lean_object* v_ref_2233_ = _args[4];
lean_object* v_kind_2234_ = _args[5];
lean_object* v_levelParams_2235_ = _args[6];
lean_object* v_modifiers_2236_ = _args[7];
lean_object* v_newFn_2237_ = _args[8];
lean_object* v_binders_2238_ = _args[9];
lean_object* v_numSectionVars_2239_ = _args[10];
lean_object* v_value_2240_ = _args[11];
lean_object* v_termination_2241_ = _args[12];
lean_object* v_fixedParamPerms_2242_ = _args[13];
lean_object* v_ys_2243_ = _args[14];
lean_object* v___y_2244_ = _args[15];
lean_object* v___y_2245_ = _args[16];
lean_object* v___y_2246_ = _args[17];
lean_object* v___y_2247_ = _args[18];
lean_object* v___y_2248_ = _args[19];
_start:
{
uint8_t v___x_2509__boxed_2249_; uint8_t v_kind_boxed_2250_; lean_object* v_res_2251_; 
v___x_2509__boxed_2249_ = lean_unbox(v___x_2232_);
v_kind_boxed_2250_ = lean_unbox(v_kind_2234_);
v_res_2251_ = l_Lean_Elab_WF_packMutual___lam__0(v_preDefs_2229_, v_perms_2230_, v_argsPacker_2231_, v___x_2509__boxed_2249_, v_ref_2233_, v_kind_boxed_2250_, v_levelParams_2235_, v_modifiers_2236_, v_newFn_2237_, v_binders_2238_, v_numSectionVars_2239_, v_value_2240_, v_termination_2241_, v_fixedParamPerms_2242_, v_ys_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec_ref(v_perms_2230_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual(lean_object* v_fixedParamPerms_2252_, lean_object* v_argsPacker_2253_, lean_object* v_preDefs_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v_ref_2263_; uint8_t v_kind_2264_; lean_object* v_levelParams_2265_; lean_object* v_modifiers_2266_; lean_object* v_declName_2267_; lean_object* v_binders_2268_; lean_object* v_numSectionVars_2269_; lean_object* v_type_2270_; lean_object* v_value_2271_; lean_object* v_termination_2272_; lean_object* v_newFn_2273_; uint8_t v___x_2274_; 
v___x_2260_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_2261_ = lean_unsigned_to_nat(0u);
v___x_2262_ = lean_array_get_borrowed(v___x_2260_, v_preDefs_2254_, v___x_2261_);
v_ref_2263_ = lean_ctor_get(v___x_2262_, 0);
v_kind_2264_ = lean_ctor_get_uint8(v___x_2262_, sizeof(void*)*9);
v_levelParams_2265_ = lean_ctor_get(v___x_2262_, 1);
v_modifiers_2266_ = lean_ctor_get(v___x_2262_, 2);
v_declName_2267_ = lean_ctor_get(v___x_2262_, 3);
v_binders_2268_ = lean_ctor_get(v___x_2262_, 4);
v_numSectionVars_2269_ = lean_ctor_get(v___x_2262_, 5);
v_type_2270_ = lean_ctor_get(v___x_2262_, 6);
v_value_2271_ = lean_ctor_get(v___x_2262_, 7);
v_termination_2272_ = lean_ctor_get(v___x_2262_, 8);
lean_inc_ref(v_fixedParamPerms_2252_);
v_newFn_2273_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_2252_, v_argsPacker_2253_, v_preDefs_2254_);
v___x_2274_ = lean_name_eq(v_newFn_2273_, v_declName_2267_);
if (v___x_2274_ == 0)
{
lean_object* v_perms_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___f_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
lean_inc_ref(v_termination_2272_);
lean_inc_ref(v_value_2271_);
lean_inc_ref(v_type_2270_);
lean_inc(v_numSectionVars_2269_);
lean_inc(v_binders_2268_);
lean_inc_ref(v_modifiers_2266_);
lean_inc(v_levelParams_2265_);
lean_inc(v_ref_2263_);
v_perms_2275_ = lean_ctor_get(v_fixedParamPerms_2252_, 1);
lean_inc_ref_n(v_perms_2275_, 2);
v___x_2276_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2277_ = lean_box(v___x_2274_);
v___x_2278_ = lean_box(v_kind_2264_);
v___f_2279_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packMutual___lam__0___boxed), 20, 14);
lean_closure_set(v___f_2279_, 0, v_preDefs_2254_);
lean_closure_set(v___f_2279_, 1, v_perms_2275_);
lean_closure_set(v___f_2279_, 2, v_argsPacker_2253_);
lean_closure_set(v___f_2279_, 3, v___x_2277_);
lean_closure_set(v___f_2279_, 4, v_ref_2263_);
lean_closure_set(v___f_2279_, 5, v___x_2278_);
lean_closure_set(v___f_2279_, 6, v_levelParams_2265_);
lean_closure_set(v___f_2279_, 7, v_modifiers_2266_);
lean_closure_set(v___f_2279_, 8, v_newFn_2273_);
lean_closure_set(v___f_2279_, 9, v_binders_2268_);
lean_closure_set(v___f_2279_, 10, v_numSectionVars_2269_);
lean_closure_set(v___f_2279_, 11, v_value_2271_);
lean_closure_set(v___f_2279_, 12, v_termination_2272_);
lean_closure_set(v___f_2279_, 13, v_fixedParamPerms_2252_);
v___x_2280_ = lean_array_get(v___x_2276_, v_perms_2275_, v___x_2261_);
lean_dec_ref(v_perms_2275_);
v___x_2281_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v___x_2280_, v_type_2270_, v___f_2279_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_);
return v___x_2281_;
}
else
{
lean_object* v___x_2282_; 
lean_inc(v___x_2262_);
lean_dec(v_newFn_2273_);
lean_dec_ref(v_preDefs_2254_);
lean_dec_ref(v_argsPacker_2253_);
lean_dec_ref(v_fixedParamPerms_2252_);
v___x_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2262_);
return v___x_2282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___boxed(lean_object* v_fixedParamPerms_2283_, lean_object* v_argsPacker_2284_, lean_object* v_preDefs_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_Elab_WF_packMutual(v_fixedParamPerms_2283_, v_argsPacker_2284_, v_preDefs_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
lean_dec(v_a_2287_);
lean_dec_ref(v_a_2286_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(lean_object* v___x_2292_, lean_object* v_ys_2293_, lean_object* v_as_2294_, size_t v_sz_2295_, size_t v_i_2296_, lean_object* v_bs_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2292_, v_ys_2293_, v_sz_2295_, v_i_2296_, v_bs_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___boxed(lean_object* v___x_2304_, lean_object* v_ys_2305_, lean_object* v_as_2306_, lean_object* v_sz_2307_, lean_object* v_i_2308_, lean_object* v_bs_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
size_t v_sz_boxed_2315_; size_t v_i_boxed_2316_; lean_object* v_res_2317_; 
v_sz_boxed_2315_ = lean_unbox_usize(v_sz_2307_);
lean_dec(v_sz_2307_);
v_i_boxed_2316_ = lean_unbox_usize(v_i_2308_);
lean_dec(v_i_2308_);
v_res_2317_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(v___x_2304_, v_ys_2305_, v_as_2306_, v_sz_boxed_2315_, v_i_boxed_2316_, v_bs_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec_ref(v_as_2306_);
lean_dec_ref(v___x_2304_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(lean_object* v___x_2318_, lean_object* v_ys_2319_, lean_object* v_as_2320_, size_t v_sz_2321_, size_t v_i_2322_, lean_object* v_bs_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2318_, v_ys_2319_, v_sz_2321_, v_i_2322_, v_bs_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___boxed(lean_object* v___x_2330_, lean_object* v_ys_2331_, lean_object* v_as_2332_, lean_object* v_sz_2333_, lean_object* v_i_2334_, lean_object* v_bs_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
size_t v_sz_boxed_2341_; size_t v_i_boxed_2342_; lean_object* v_res_2343_; 
v_sz_boxed_2341_ = lean_unbox_usize(v_sz_2333_);
lean_dec(v_sz_2333_);
v_i_boxed_2342_ = lean_unbox_usize(v_i_2334_);
lean_dec(v_i_2334_);
v_res_2343_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(v___x_2330_, v_ys_2331_, v_as_2332_, v_sz_boxed_2341_, v_i_boxed_2342_, v_bs_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec_ref(v_as_2332_);
lean_dec_ref(v___x_2330_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(lean_object* v_e_2344_, lean_object* v_k_2345_, uint8_t v_cleanupAnnotations_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v___f_2352_; uint8_t v___x_2353_; uint8_t v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___f_2352_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2352_, 0, v_k_2345_);
v___x_2353_ = 1;
v___x_2354_ = 0;
v___x_2355_ = lean_box(0);
v___x_2356_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2344_, v___x_2353_, v___x_2354_, v___x_2353_, v___x_2354_, v___x_2355_, v___f_2352_, v_cleanupAnnotations_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2356_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2356_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
v_a_2365_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2356_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2356_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg___boxed(lean_object* v_e_2373_, lean_object* v_k_2374_, lean_object* v_cleanupAnnotations_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2381_; lean_object* v_res_2382_; 
v_cleanupAnnotations_boxed_2381_ = lean_unbox(v_cleanupAnnotations_2375_);
v_res_2382_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2373_, v_k_2374_, v_cleanupAnnotations_boxed_2381_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(lean_object* v_00_u03b1_2383_, lean_object* v_e_2384_, lean_object* v_k_2385_, uint8_t v_cleanupAnnotations_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2384_, v_k_2385_, v_cleanupAnnotations_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___boxed(lean_object* v_00_u03b1_2393_, lean_object* v_e_2394_, lean_object* v_k_2395_, lean_object* v_cleanupAnnotations_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2402_; lean_object* v_res_2403_; 
v_cleanupAnnotations_boxed_2402_ = lean_unbox(v_cleanupAnnotations_2396_);
v_res_2403_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(v_00_u03b1_2393_, v_e_2394_, v_k_2395_, v_cleanupAnnotations_boxed_2402_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(lean_object* v_msg_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v___f_2410_; lean_object* v___x_1649__overap_2411_; lean_object* v___x_2412_; 
v___f_2410_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1649__overap_2411_ = lean_panic_fn_borrowed(v___f_2410_, v_msg_2404_);
lean_inc(v___y_2408_);
lean_inc_ref(v___y_2407_);
lean_inc(v___y_2406_);
lean_inc_ref(v___y_2405_);
v___x_2412_ = lean_apply_5(v___x_1649__overap_2411_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, lean_box(0));
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1___boxed(lean_object* v_msg_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v_msg_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0(lean_object* v_xs_2420_, lean_object* v_x_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = lean_array_get_size(v_xs_2420_);
v___x_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0___boxed(lean_object* v_xs_2429_, lean_object* v_x_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_Elab_WF_varyingVarNames___lam__0(v_xs_2429_, v_x_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec_ref(v_x_2430_);
lean_dec_ref(v_xs_2429_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(lean_object* v_as_2437_, size_t v_sz_2438_, size_t v_i_2439_, lean_object* v_b_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v_a_2446_; uint8_t v___x_2450_; 
v___x_2450_ = lean_usize_dec_lt(v_i_2439_, v_sz_2438_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2451_; 
v___x_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2451_, 0, v_b_2440_);
return v___x_2451_;
}
else
{
lean_object* v_snd_2452_; lean_object* v_fst_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2497_; 
v_snd_2452_ = lean_ctor_get(v_b_2440_, 1);
v_fst_2453_ = lean_ctor_get(v_b_2440_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_b_2440_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2455_ = v_b_2440_;
v_isShared_2456_ = v_isSharedCheck_2497_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_snd_2452_);
lean_inc(v_fst_2453_);
lean_dec(v_b_2440_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2497_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v_array_2457_; lean_object* v_start_2458_; lean_object* v_stop_2459_; uint8_t v___x_2460_; 
v_array_2457_ = lean_ctor_get(v_snd_2452_, 0);
v_start_2458_ = lean_ctor_get(v_snd_2452_, 1);
v_stop_2459_ = lean_ctor_get(v_snd_2452_, 2);
v___x_2460_ = lean_nat_dec_lt(v_start_2458_, v_stop_2459_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2462_; 
if (v_isShared_2456_ == 0)
{
v___x_2462_ = v___x_2455_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_fst_2453_);
lean_ctor_set(v_reuseFailAlloc_2464_, 1, v_snd_2452_);
v___x_2462_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
lean_object* v___x_2463_; 
v___x_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2462_);
return v___x_2463_;
}
}
else
{
lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2493_; 
lean_inc(v_stop_2459_);
lean_inc(v_start_2458_);
lean_inc_ref(v_array_2457_);
v_isSharedCheck_2493_ = !lean_is_exclusive(v_snd_2452_);
if (v_isSharedCheck_2493_ == 0)
{
lean_object* v_unused_2494_; lean_object* v_unused_2495_; lean_object* v_unused_2496_; 
v_unused_2494_ = lean_ctor_get(v_snd_2452_, 2);
lean_dec(v_unused_2494_);
v_unused_2495_ = lean_ctor_get(v_snd_2452_, 1);
lean_dec(v_unused_2495_);
v_unused_2496_ = lean_ctor_get(v_snd_2452_, 0);
lean_dec(v_unused_2496_);
v___x_2466_ = v_snd_2452_;
v_isShared_2467_ = v_isSharedCheck_2493_;
goto v_resetjp_2465_;
}
else
{
lean_dec(v_snd_2452_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2493_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
v___x_2468_ = lean_array_fget(v_array_2457_, v_start_2458_);
v___x_2469_ = lean_unsigned_to_nat(1u);
v___x_2470_ = lean_nat_add(v_start_2458_, v___x_2469_);
lean_dec(v_start_2458_);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 1, v___x_2470_);
v___x_2472_ = v___x_2466_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_array_2457_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v___x_2470_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v_stop_2459_);
v___x_2472_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v_a_2473_ = lean_array_uget_borrowed(v_as_2437_, v_i_2439_);
v___x_2474_ = l_Lean_Expr_fvarId_x21(v_a_2473_);
v___x_2475_ = l_Lean_FVarId_getUserName___redArg(v___x_2474_, v___y_2441_, v___y_2442_, v___y_2443_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2476_);
lean_dec_ref_known(v___x_2475_, 1);
v___x_2477_ = lean_array_push(v_fst_2453_, v_a_2476_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 1, v___x_2472_);
lean_ctor_set(v___x_2455_, 0, v___x_2477_);
v___x_2479_ = v___x_2455_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2477_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v___x_2472_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
v_a_2446_ = v___x_2479_;
goto v___jp_2445_;
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec_ref(v___x_2472_);
lean_del_object(v___x_2455_);
lean_dec(v_fst_2453_);
v_a_2481_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2475_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2475_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
else
{
lean_object* v___x_2490_; 
lean_dec_ref_known(v___x_2468_, 1);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 1, v___x_2472_);
v___x_2490_ = v___x_2455_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_fst_2453_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v___x_2472_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
v_a_2446_ = v___x_2490_;
goto v___jp_2445_;
}
}
}
}
}
}
}
v___jp_2445_:
{
size_t v___x_2447_; size_t v___x_2448_; 
v___x_2447_ = ((size_t)1ULL);
v___x_2448_ = lean_usize_add(v_i_2439_, v___x_2447_);
v_i_2439_ = v___x_2448_;
v_b_2440_ = v_a_2446_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg___boxed(lean_object* v_as_2498_, lean_object* v_sz_2499_, lean_object* v_i_2500_, lean_object* v_b_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
size_t v_sz_boxed_2506_; size_t v_i_boxed_2507_; lean_object* v_res_2508_; 
v_sz_boxed_2506_ = lean_unbox_usize(v_sz_2499_);
lean_dec(v_sz_2499_);
v_i_boxed_2507_ = lean_unbox_usize(v_i_2500_);
lean_dec(v_i_2500_);
v_res_2508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2498_, v_sz_boxed_2506_, v_i_boxed_2507_, v_b_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec_ref(v_as_2498_);
return v_res_2508_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2511_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1));
v___x_2512_ = lean_unsigned_to_nat(4u);
v___x_2513_ = lean_unsigned_to_nat(119u);
v___x_2514_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2515_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2516_ = l_mkPanicMessageWithDecl(v___x_2515_, v___x_2514_, v___x_2513_, v___x_2512_, v___x_2511_);
return v___x_2516_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2518_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3));
v___x_2519_ = lean_unsigned_to_nat(4u);
v___x_2520_ = lean_unsigned_to_nat(120u);
v___x_2521_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2522_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2523_ = l_mkPanicMessageWithDecl(v___x_2522_, v___x_2521_, v___x_2520_, v___x_2519_, v___x_2518_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1(lean_object* v_a_2526_, lean_object* v_fixedParamPerms_2527_, lean_object* v___x_2528_, lean_object* v_preDefIdx_2529_, lean_object* v_xs_2530_, lean_object* v_x_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2537_ = lean_array_get_size(v_xs_2530_);
v___x_2538_ = lean_nat_dec_eq(v___x_2537_, v_a_2526_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2);
v___x_2540_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2539_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
return v___x_2540_;
}
else
{
lean_object* v_perms_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
v_perms_2541_ = lean_ctor_get(v_fixedParamPerms_2527_, 1);
v___x_2542_ = lean_array_get_borrowed(v___x_2528_, v_perms_2541_, v_preDefIdx_2529_);
v___x_2543_ = lean_array_get_size(v___x_2542_);
v___x_2544_ = lean_nat_dec_eq(v___x_2543_, v_a_2526_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4);
v___x_2546_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2545_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
return v___x_2546_;
}
else
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; size_t v_sz_2551_; size_t v___x_2552_; lean_object* v___x_2553_; 
v___x_2547_ = lean_unsigned_to_nat(0u);
v___x_2548_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5));
lean_inc(v___x_2542_);
v___x_2549_ = l_Array_toSubarray___redArg(v___x_2542_, v___x_2547_, v___x_2543_);
v___x_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v_sz_2551_ = lean_array_size(v_xs_2530_);
v___x_2552_ = ((size_t)0ULL);
v___x_2553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_xs_2530_, v_sz_2551_, v___x_2552_, v___x_2550_, v___y_2532_, v___y_2534_, v___y_2535_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2562_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2556_ = v___x_2553_;
v_isShared_2557_ = v_isSharedCheck_2562_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2553_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2562_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v_fst_2558_; lean_object* v___x_2560_; 
v_fst_2558_ = lean_ctor_get(v_a_2554_, 0);
lean_inc(v_fst_2558_);
lean_dec(v_a_2554_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v_fst_2558_);
v___x_2560_ = v___x_2556_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_fst_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
v_a_2563_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2553_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2553_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___boxed(lean_object* v_a_2571_, lean_object* v_fixedParamPerms_2572_, lean_object* v___x_2573_, lean_object* v_preDefIdx_2574_, lean_object* v_xs_2575_, lean_object* v_x_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_Elab_WF_varyingVarNames___lam__1(v_a_2571_, v_fixedParamPerms_2572_, v___x_2573_, v_preDefIdx_2574_, v_xs_2575_, v_x_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec_ref(v_x_2576_);
lean_dec_ref(v_xs_2575_);
lean_dec(v_preDefIdx_2574_);
lean_dec_ref(v___x_2573_);
lean_dec_ref(v_fixedParamPerms_2572_);
lean_dec(v_a_2571_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object* v_fixedParamPerms_2584_, lean_object* v_preDefIdx_2585_, lean_object* v_preDef_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v_type_2592_; lean_object* v_value_2593_; lean_object* v___f_2594_; lean_object* v___x_2595_; uint8_t v___x_2596_; lean_object* v___x_2597_; 
v_type_2592_ = lean_ctor_get(v_preDef_2586_, 6);
lean_inc_ref(v_type_2592_);
v_value_2593_ = lean_ctor_get(v_preDef_2586_, 7);
lean_inc_ref(v_value_2593_);
lean_dec_ref(v_preDef_2586_);
v___f_2594_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___closed__0));
v___x_2595_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2596_ = 0;
v___x_2597_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_value_2593_, v___f_2594_, v___x_2596_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___f_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc_n(v_a_2598_, 2);
lean_dec_ref_known(v___x_2597_, 1);
v___f_2599_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_varyingVarNames___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2599_, 0, v_a_2598_);
lean_closure_set(v___f_2599_, 1, v_fixedParamPerms_2584_);
lean_closure_set(v___f_2599_, 2, v___x_2595_);
lean_closure_set(v___f_2599_, 3, v_preDefIdx_2585_);
v___x_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2600_, 0, v_a_2598_);
v___x_2601_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2592_, v___x_2600_, v___f_2599_, v___x_2596_, v___x_2596_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_);
return v___x_2601_;
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_dec_ref(v_type_2592_);
lean_dec(v_preDefIdx_2585_);
lean_dec_ref(v_fixedParamPerms_2584_);
v_a_2602_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2597_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2597_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___boxed(lean_object* v_fixedParamPerms_2610_, lean_object* v_preDefIdx_2611_, lean_object* v_preDef_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_Lean_Elab_WF_varyingVarNames(v_fixedParamPerms_2610_, v_preDefIdx_2611_, v_preDef_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_);
lean_dec(v_a_2616_);
lean_dec_ref(v_a_2615_);
lean_dec(v_a_2614_);
lean_dec_ref(v_a_2613_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(lean_object* v_as_2619_, size_t v_sz_2620_, size_t v_i_2621_, lean_object* v_b_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2619_, v_sz_2620_, v_i_2621_, v_b_2622_, v___y_2623_, v___y_2625_, v___y_2626_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___boxed(lean_object* v_as_2629_, lean_object* v_sz_2630_, lean_object* v_i_2631_, lean_object* v_b_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
size_t v_sz_boxed_2638_; size_t v_i_boxed_2639_; lean_object* v_res_2640_; 
v_sz_boxed_2638_ = lean_unbox_usize(v_sz_2630_);
lean_dec(v_sz_2630_);
v_i_boxed_2639_ = lean_unbox_usize(v_i_2631_);
lean_dec(v_i_2631_);
v_res_2640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(v_as_2629_, v_sz_boxed_2638_, v_i_boxed_2639_, v_b_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v_as_2629_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(lean_object* v_msg_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v___f_2647_; lean_object* v___x_1596__overap_2648_; lean_object* v___x_2649_; 
v___f_2647_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1596__overap_2648_ = lean_panic_fn_borrowed(v___f_2647_, v_msg_2641_);
lean_inc(v___y_2645_);
lean_inc_ref(v___y_2644_);
lean_inc(v___y_2643_);
lean_inc_ref(v___y_2642_);
v___x_2649_ = lean_apply_5(v___x_1596__overap_2648_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, lean_box(0));
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0___boxed(lean_object* v_msg_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v_msg_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
return v_res_2656_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2657_; double v___x_2658_; 
v___x_2657_ = lean_unsigned_to_nat(0u);
v___x_2658_ = lean_float_of_nat(v___x_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(lean_object* v_cls_2662_, lean_object* v_msg_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v_ref_2669_; lean_object* v___x_2670_; lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2716_; 
v_ref_2669_ = lean_ctor_get(v___y_2666_, 2);
v___x_2670_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msg_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2673_ = v___x_2670_;
v_isShared_2674_ = v_isSharedCheck_2716_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2670_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2716_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2675_; lean_object* v_traceState_2676_; lean_object* v_env_2677_; lean_object* v_nextMacroScope_2678_; lean_object* v_ngen_2679_; lean_object* v_auxDeclNGen_2680_; lean_object* v_cache_2681_; lean_object* v_recordedDeps_2682_; lean_object* v_messages_2683_; lean_object* v_infoState_2684_; lean_object* v_snapshotTasks_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2715_; 
v___x_2675_ = lean_st_ref_take(v___y_2667_);
v_traceState_2676_ = lean_ctor_get(v___x_2675_, 4);
v_env_2677_ = lean_ctor_get(v___x_2675_, 0);
v_nextMacroScope_2678_ = lean_ctor_get(v___x_2675_, 1);
v_ngen_2679_ = lean_ctor_get(v___x_2675_, 2);
v_auxDeclNGen_2680_ = lean_ctor_get(v___x_2675_, 3);
v_cache_2681_ = lean_ctor_get(v___x_2675_, 5);
v_recordedDeps_2682_ = lean_ctor_get(v___x_2675_, 6);
v_messages_2683_ = lean_ctor_get(v___x_2675_, 7);
v_infoState_2684_ = lean_ctor_get(v___x_2675_, 8);
v_snapshotTasks_2685_ = lean_ctor_get(v___x_2675_, 9);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2687_ = v___x_2675_;
v_isShared_2688_ = v_isSharedCheck_2715_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_snapshotTasks_2685_);
lean_inc(v_infoState_2684_);
lean_inc(v_messages_2683_);
lean_inc(v_recordedDeps_2682_);
lean_inc(v_cache_2681_);
lean_inc(v_traceState_2676_);
lean_inc(v_auxDeclNGen_2680_);
lean_inc(v_ngen_2679_);
lean_inc(v_nextMacroScope_2678_);
lean_inc(v_env_2677_);
lean_dec(v___x_2675_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2715_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
uint64_t v_tid_2689_; lean_object* v_traces_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2714_; 
v_tid_2689_ = lean_ctor_get_uint64(v_traceState_2676_, sizeof(void*)*1);
v_traces_2690_ = lean_ctor_get(v_traceState_2676_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_traceState_2676_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2692_ = v_traceState_2676_;
v_isShared_2693_ = v_isSharedCheck_2714_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_traces_2690_);
lean_dec(v_traceState_2676_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2714_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; double v___x_2696_; uint8_t v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2705_; 
v___x_2694_ = lean_box(0);
v___x_2695_ = lean_box(0);
v___x_2696_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0);
v___x_2697_ = 0;
v___x_2698_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1));
v___x_2699_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2699_, 0, v_cls_2662_);
lean_ctor_set(v___x_2699_, 1, v___x_2695_);
lean_ctor_set(v___x_2699_, 2, v___x_2698_);
lean_ctor_set_float(v___x_2699_, sizeof(void*)*3, v___x_2696_);
lean_ctor_set_float(v___x_2699_, sizeof(void*)*3 + 8, v___x_2696_);
lean_ctor_set_uint8(v___x_2699_, sizeof(void*)*3 + 16, v___x_2697_);
v___x_2700_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2));
v___x_2701_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2699_);
lean_ctor_set(v___x_2701_, 1, v_a_2671_);
lean_ctor_set(v___x_2701_, 2, v___x_2700_);
lean_inc(v_ref_2669_);
v___x_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2702_, 0, v_ref_2669_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
v___x_2703_ = l_Lean_PersistentArray_push___redArg(v_traces_2690_, v___x_2702_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v___x_2703_);
v___x_2705_ = v___x_2692_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2703_);
lean_ctor_set_uint64(v_reuseFailAlloc_2713_, sizeof(void*)*1, v_tid_2689_);
v___x_2705_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
lean_object* v___x_2707_; 
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 4, v___x_2705_);
v___x_2707_ = v___x_2687_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_env_2677_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v_nextMacroScope_2678_);
lean_ctor_set(v_reuseFailAlloc_2712_, 2, v_ngen_2679_);
lean_ctor_set(v_reuseFailAlloc_2712_, 3, v_auxDeclNGen_2680_);
lean_ctor_set(v_reuseFailAlloc_2712_, 4, v___x_2705_);
lean_ctor_set(v_reuseFailAlloc_2712_, 5, v_cache_2681_);
lean_ctor_set(v_reuseFailAlloc_2712_, 6, v_recordedDeps_2682_);
lean_ctor_set(v_reuseFailAlloc_2712_, 7, v_messages_2683_);
lean_ctor_set(v_reuseFailAlloc_2712_, 8, v_infoState_2684_);
lean_ctor_set(v_reuseFailAlloc_2712_, 9, v_snapshotTasks_2685_);
v___x_2707_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2708_; lean_object* v___x_2710_; 
v___x_2708_ = lean_st_ref_put(v___y_2667_, v___x_2707_);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 0, v___x_2694_);
v___x_2710_ = v___x_2673_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2694_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___boxed(lean_object* v_cls_2717_, lean_object* v_msg_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v_cls_2717_, v_msg_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
return v_res_2724_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2727_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1));
v___x_2728_ = lean_unsigned_to_nat(8u);
v___x_2729_ = lean_unsigned_to_nat(135u);
v___x_2730_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0));
v___x_2731_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2732_ = l_mkPanicMessageWithDecl(v___x_2731_, v___x_2730_, v___x_2729_, v___x_2728_, v___x_2727_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(lean_object* v___x_2733_, lean_object* v_unaryPreDefNonRec_2734_, lean_object* v___x_2735_, lean_object* v_us_2736_, lean_object* v_argsPacker_2737_, lean_object* v___x_2738_, lean_object* v_params_2739_, lean_object* v_x_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v___x_2746_; uint8_t v___x_2747_; 
v___x_2746_ = lean_array_get_size(v_params_2739_);
v___x_2747_ = lean_nat_dec_eq(v___x_2733_, v___x_2746_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
lean_dec(v___x_2738_);
lean_dec(v_us_2736_);
lean_dec_ref(v_unaryPreDefNonRec_2734_);
v___x_2748_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2);
v___x_2749_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v___x_2748_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
return v___x_2749_;
}
else
{
lean_object* v_declName_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v_declName_2750_ = lean_ctor_get(v_unaryPreDefNonRec_2734_, 3);
lean_inc(v_declName_2750_);
lean_dec_ref(v_unaryPreDefNonRec_2734_);
v___x_2751_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v___x_2735_, v_params_2739_);
v___x_2752_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_2735_, v_params_2739_);
v___x_2753_ = l_Lean_mkConst(v_declName_2750_, v_us_2736_);
v___x_2754_ = l_Lean_mkAppN(v___x_2753_, v___x_2751_);
lean_dec_ref(v___x_2751_);
v___x_2755_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_2737_, v___x_2754_, v___x_2738_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2757_; uint8_t v___x_2758_; uint8_t v___x_2759_; lean_object* v___x_2760_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_a_2756_);
lean_dec_ref_known(v___x_2755_, 1);
v___x_2757_ = l_Lean_Expr_beta(v_a_2756_, v___x_2752_);
v___x_2758_ = 0;
v___x_2759_ = 1;
v___x_2760_ = l_Lean_Meta_mkLambdaFVars(v_params_2739_, v___x_2757_, v___x_2758_, v___x_2747_, v___x_2758_, v___x_2747_, v___x_2759_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
return v___x_2760_;
}
else
{
lean_dec_ref(v___x_2752_);
return v___x_2755_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed(lean_object* v___x_2761_, lean_object* v_unaryPreDefNonRec_2762_, lean_object* v___x_2763_, lean_object* v_us_2764_, lean_object* v_argsPacker_2765_, lean_object* v___x_2766_, lean_object* v_params_2767_, lean_object* v_x_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(v___x_2761_, v_unaryPreDefNonRec_2762_, v___x_2763_, v_us_2764_, v_argsPacker_2765_, v___x_2766_, v_params_2767_, v_x_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec_ref(v_x_2768_);
lean_dec_ref(v_params_2767_);
lean_dec_ref(v_argsPacker_2765_);
lean_dec_ref(v___x_2763_);
lean_dec(v___x_2761_);
return v_res_2774_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2785_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2786_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5));
v___x_2787_ = l_Lean_Name_append(v___x_2786_, v___x_2785_);
return v___x_2787_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7));
v___x_2790_ = l_Lean_stringToMessageData(v___x_2789_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(lean_object* v_fixedParamPerms_2791_, lean_object* v_unaryPreDefNonRec_2792_, lean_object* v_us_2793_, lean_object* v_argsPacker_2794_, size_t v_sz_2795_, size_t v_i_2796_, lean_object* v_bs_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
uint8_t v___x_2803_; 
v___x_2803_ = lean_usize_dec_lt(v_i_2796_, v_sz_2795_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; 
lean_dec_ref(v_argsPacker_2794_);
lean_dec(v_us_2793_);
lean_dec_ref(v_unaryPreDefNonRec_2792_);
v___x_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2804_, 0, v_bs_2797_);
return v___x_2804_;
}
else
{
lean_object* v_v_2805_; lean_object* v_perms_2806_; lean_object* v_ref_2807_; uint8_t v_kind_2808_; lean_object* v_levelParams_2809_; lean_object* v_modifiers_2810_; lean_object* v_declName_2811_; lean_object* v_binders_2812_; lean_object* v_numSectionVars_2813_; lean_object* v_type_2814_; lean_object* v_termination_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2867_; 
v_v_2805_ = lean_array_uget(v_bs_2797_, v_i_2796_);
v_perms_2806_ = lean_ctor_get(v_fixedParamPerms_2791_, 1);
v_ref_2807_ = lean_ctor_get(v_v_2805_, 0);
v_kind_2808_ = lean_ctor_get_uint8(v_v_2805_, sizeof(void*)*9);
v_levelParams_2809_ = lean_ctor_get(v_v_2805_, 1);
v_modifiers_2810_ = lean_ctor_get(v_v_2805_, 2);
v_declName_2811_ = lean_ctor_get(v_v_2805_, 3);
v_binders_2812_ = lean_ctor_get(v_v_2805_, 4);
v_numSectionVars_2813_ = lean_ctor_get(v_v_2805_, 5);
v_type_2814_ = lean_ctor_get(v_v_2805_, 6);
v_termination_2815_ = lean_ctor_get(v_v_2805_, 8);
v_isSharedCheck_2867_ = !lean_is_exclusive(v_v_2805_);
if (v_isSharedCheck_2867_ == 0)
{
lean_object* v_unused_2868_; 
v_unused_2868_ = lean_ctor_get(v_v_2805_, 7);
lean_dec(v_unused_2868_);
v___x_2817_ = v_v_2805_;
v_isShared_2818_ = v_isSharedCheck_2867_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_termination_2815_);
lean_inc(v_type_2814_);
lean_inc(v_numSectionVars_2813_);
lean_inc(v_binders_2812_);
lean_inc(v_declName_2811_);
lean_inc(v_modifiers_2810_);
lean_inc(v_levelParams_2809_);
lean_inc(v_ref_2807_);
lean_dec(v_v_2805_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2867_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v_bs_x27_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___f_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; lean_object* v___x_2828_; 
v___x_2819_ = lean_unsigned_to_nat(0u);
v_bs_x27_2820_ = lean_array_uset(v_bs_2797_, v_i_2796_, v___x_2819_);
v___x_2821_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2822_ = lean_usize_to_nat(v_i_2796_);
v___x_2823_ = lean_array_get_borrowed(v___x_2821_, v_perms_2806_, v___x_2822_);
v___x_2824_ = lean_array_get_size(v___x_2823_);
lean_inc_ref(v_argsPacker_2794_);
lean_inc(v_us_2793_);
lean_inc(v___x_2823_);
lean_inc_ref(v_unaryPreDefNonRec_2792_);
v___f_2825_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2825_, 0, v___x_2824_);
lean_closure_set(v___f_2825_, 1, v_unaryPreDefNonRec_2792_);
lean_closure_set(v___f_2825_, 2, v___x_2823_);
lean_closure_set(v___f_2825_, 3, v_us_2793_);
lean_closure_set(v___f_2825_, 4, v_argsPacker_2794_);
lean_closure_set(v___f_2825_, 5, v___x_2822_);
v___x_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2824_);
v___x_2827_ = 0;
lean_inc_ref(v_type_2814_);
v___x_2828_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2814_, v___x_2826_, v___f_2825_, v___x_2827_, v___x_2827_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v_toCold_2838_; lean_object* v_options_2839_; uint8_t v_hasTrace_2840_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_a_2829_);
lean_dec_ref_known(v___x_2828_, 1);
v_toCold_2838_ = lean_ctor_get(v___y_2800_, 0);
v_options_2839_ = lean_ctor_get(v_toCold_2838_, 2);
v_hasTrace_2840_ = lean_ctor_get_uint8(v_options_2839_, sizeof(void*)*1);
if (v_hasTrace_2840_ == 0)
{
goto v___jp_2830_;
}
else
{
lean_object* v_inheritedTraceOptions_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v_inheritedTraceOptions_2841_ = lean_ctor_get(v_toCold_2838_, 11);
v___x_2842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2843_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6);
v___x_2844_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2841_, v_options_2839_, v___x_2843_);
if (v___x_2844_ == 0)
{
goto v___jp_2830_;
}
else
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
lean_inc(v_declName_2811_);
v___x_2845_ = l_Lean_MessageData_ofName(v_declName_2811_);
v___x_2846_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8);
v___x_2847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2845_);
lean_ctor_set(v___x_2847_, 1, v___x_2846_);
lean_inc(v_a_2829_);
v___x_2848_ = l_Lean_MessageData_ofExpr(v_a_2829_);
v___x_2849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2847_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v___x_2842_, v___x_2849_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_dec_ref_known(v___x_2850_, 1);
goto v___jp_2830_;
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_dec(v_a_2829_);
lean_dec_ref(v_bs_x27_2820_);
lean_del_object(v___x_2817_);
lean_dec_ref(v_termination_2815_);
lean_dec_ref(v_type_2814_);
lean_dec(v_numSectionVars_2813_);
lean_dec(v_binders_2812_);
lean_dec(v_declName_2811_);
lean_dec_ref(v_modifiers_2810_);
lean_dec(v_levelParams_2809_);
lean_dec(v_ref_2807_);
lean_dec_ref(v_argsPacker_2794_);
lean_dec(v_us_2793_);
lean_dec_ref(v_unaryPreDefNonRec_2792_);
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2850_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2850_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
}
v___jp_2830_:
{
lean_object* v___x_2832_; 
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 7, v_a_2829_);
v___x_2832_ = v___x_2817_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_ref_2807_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v_levelParams_2809_);
lean_ctor_set(v_reuseFailAlloc_2837_, 2, v_modifiers_2810_);
lean_ctor_set(v_reuseFailAlloc_2837_, 3, v_declName_2811_);
lean_ctor_set(v_reuseFailAlloc_2837_, 4, v_binders_2812_);
lean_ctor_set(v_reuseFailAlloc_2837_, 5, v_numSectionVars_2813_);
lean_ctor_set(v_reuseFailAlloc_2837_, 6, v_type_2814_);
lean_ctor_set(v_reuseFailAlloc_2837_, 7, v_a_2829_);
lean_ctor_set(v_reuseFailAlloc_2837_, 8, v_termination_2815_);
lean_ctor_set_uint8(v_reuseFailAlloc_2837_, sizeof(void*)*9, v_kind_2808_);
v___x_2832_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
size_t v___x_2833_; size_t v___x_2834_; lean_object* v___x_2835_; 
v___x_2833_ = ((size_t)1ULL);
v___x_2834_ = lean_usize_add(v_i_2796_, v___x_2833_);
v___x_2835_ = lean_array_uset(v_bs_x27_2820_, v_i_2796_, v___x_2832_);
v_i_2796_ = v___x_2834_;
v_bs_2797_ = v___x_2835_;
goto _start;
}
}
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
lean_dec_ref(v_bs_x27_2820_);
lean_del_object(v___x_2817_);
lean_dec_ref(v_termination_2815_);
lean_dec_ref(v_type_2814_);
lean_dec(v_numSectionVars_2813_);
lean_dec(v_binders_2812_);
lean_dec(v_declName_2811_);
lean_dec_ref(v_modifiers_2810_);
lean_dec(v_levelParams_2809_);
lean_dec(v_ref_2807_);
lean_dec_ref(v_argsPacker_2794_);
lean_dec(v_us_2793_);
lean_dec_ref(v_unaryPreDefNonRec_2792_);
v_a_2859_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v___x_2828_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2828_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2859_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_2869_, lean_object* v_unaryPreDefNonRec_2870_, lean_object* v_us_2871_, lean_object* v_argsPacker_2872_, lean_object* v_sz_2873_, lean_object* v_i_2874_, lean_object* v_bs_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
size_t v_sz_boxed_2881_; size_t v_i_boxed_2882_; lean_object* v_res_2883_; 
v_sz_boxed_2881_ = lean_unbox_usize(v_sz_2873_);
lean_dec(v_sz_2873_);
v_i_boxed_2882_ = lean_unbox_usize(v_i_2874_);
lean_dec(v_i_2874_);
v_res_2883_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2869_, v_unaryPreDefNonRec_2870_, v_us_2871_, v_argsPacker_2872_, v_sz_boxed_2881_, v_i_boxed_2882_, v_bs_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec_ref(v_fixedParamPerms_2869_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(lean_object* v_unaryPreDefNonRec_2884_, lean_object* v_preDefs_2885_, lean_object* v_fixedParamPerms_2886_, lean_object* v_us_2887_, lean_object* v_argsPacker_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Lean_Elab_addAsAxiom___redArg(v_unaryPreDefNonRec_2884_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2894_) == 0)
{
size_t v_sz_2895_; size_t v___x_2896_; lean_object* v___x_2897_; 
lean_dec_ref_known(v___x_2894_, 1);
v_sz_2895_ = lean_array_size(v_preDefs_2885_);
v___x_2896_ = ((size_t)0ULL);
v___x_2897_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2886_, v_unaryPreDefNonRec_2884_, v_us_2887_, v_argsPacker_2888_, v_sz_2895_, v___x_2896_, v_preDefs_2885_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
return v___x_2897_;
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec_ref(v_argsPacker_2888_);
lean_dec(v_us_2887_);
lean_dec_ref(v_preDefs_2885_);
lean_dec_ref(v_unaryPreDefNonRec_2884_);
v_a_2898_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2894_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2894_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed(lean_object* v_unaryPreDefNonRec_2906_, lean_object* v_preDefs_2907_, lean_object* v_fixedParamPerms_2908_, lean_object* v_us_2909_, lean_object* v_argsPacker_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(v_unaryPreDefNonRec_2906_, v_preDefs_2907_, v_fixedParamPerms_2908_, v_us_2909_, v_argsPacker_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec_ref(v_fixedParamPerms_2908_);
return v_res_2916_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2917_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0);
v___x_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
return v___x_2919_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
v___x_2921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
lean_ctor_set(v___x_2921_, 1, v___x_2920_);
return v___x_2921_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
v___x_2923_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
lean_ctor_set(v___x_2923_, 2, v___x_2922_);
lean_ctor_set(v___x_2923_, 3, v___x_2922_);
lean_ctor_set(v___x_2923_, 4, v___x_2922_);
lean_ctor_set(v___x_2923_, 5, v___x_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(lean_object* v_env_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v___x_2928_; lean_object* v_nextMacroScope_2929_; lean_object* v_ngen_2930_; lean_object* v_auxDeclNGen_2931_; lean_object* v_traceState_2932_; lean_object* v_recordedDeps_2933_; lean_object* v_messages_2934_; lean_object* v_infoState_2935_; lean_object* v_snapshotTasks_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2962_; 
v___x_2928_ = lean_st_ref_take(v___y_2926_);
v_nextMacroScope_2929_ = lean_ctor_get(v___x_2928_, 1);
v_ngen_2930_ = lean_ctor_get(v___x_2928_, 2);
v_auxDeclNGen_2931_ = lean_ctor_get(v___x_2928_, 3);
v_traceState_2932_ = lean_ctor_get(v___x_2928_, 4);
v_recordedDeps_2933_ = lean_ctor_get(v___x_2928_, 6);
v_messages_2934_ = lean_ctor_get(v___x_2928_, 7);
v_infoState_2935_ = lean_ctor_get(v___x_2928_, 8);
v_snapshotTasks_2936_ = lean_ctor_get(v___x_2928_, 9);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2962_ == 0)
{
lean_object* v_unused_2963_; lean_object* v_unused_2964_; 
v_unused_2963_ = lean_ctor_get(v___x_2928_, 5);
lean_dec(v_unused_2963_);
v_unused_2964_ = lean_ctor_get(v___x_2928_, 0);
lean_dec(v_unused_2964_);
v___x_2938_ = v___x_2928_;
v_isShared_2939_ = v_isSharedCheck_2962_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_snapshotTasks_2936_);
lean_inc(v_infoState_2935_);
lean_inc(v_messages_2934_);
lean_inc(v_recordedDeps_2933_);
lean_inc(v_traceState_2932_);
lean_inc(v_auxDeclNGen_2931_);
lean_inc(v_ngen_2930_);
lean_inc(v_nextMacroScope_2929_);
lean_dec(v___x_2928_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2962_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2940_; lean_object* v___x_2942_; 
v___x_2940_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 5, v___x_2940_);
lean_ctor_set(v___x_2938_, 0, v_env_2924_);
v___x_2942_ = v___x_2938_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_env_2924_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v_nextMacroScope_2929_);
lean_ctor_set(v_reuseFailAlloc_2961_, 2, v_ngen_2930_);
lean_ctor_set(v_reuseFailAlloc_2961_, 3, v_auxDeclNGen_2931_);
lean_ctor_set(v_reuseFailAlloc_2961_, 4, v_traceState_2932_);
lean_ctor_set(v_reuseFailAlloc_2961_, 5, v___x_2940_);
lean_ctor_set(v_reuseFailAlloc_2961_, 6, v_recordedDeps_2933_);
lean_ctor_set(v_reuseFailAlloc_2961_, 7, v_messages_2934_);
lean_ctor_set(v_reuseFailAlloc_2961_, 8, v_infoState_2935_);
lean_ctor_set(v_reuseFailAlloc_2961_, 9, v_snapshotTasks_2936_);
v___x_2942_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v_mctx_2945_; lean_object* v_zetaDeltaFVarIds_2946_; lean_object* v_postponed_2947_; lean_object* v_diag_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2959_; 
v___x_2943_ = lean_st_ref_put(v___y_2926_, v___x_2942_);
v___x_2944_ = lean_st_ref_take(v___y_2925_);
v_mctx_2945_ = lean_ctor_get(v___x_2944_, 0);
v_zetaDeltaFVarIds_2946_ = lean_ctor_get(v___x_2944_, 2);
v_postponed_2947_ = lean_ctor_get(v___x_2944_, 3);
v_diag_2948_ = lean_ctor_get(v___x_2944_, 4);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2959_ == 0)
{
lean_object* v_unused_2960_; 
v_unused_2960_ = lean_ctor_get(v___x_2944_, 1);
lean_dec(v_unused_2960_);
v___x_2950_ = v___x_2944_;
v_isShared_2951_ = v_isSharedCheck_2959_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_diag_2948_);
lean_inc(v_postponed_2947_);
lean_inc(v_zetaDeltaFVarIds_2946_);
lean_inc(v_mctx_2945_);
lean_dec(v___x_2944_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2959_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2955_; 
v___x_2952_ = lean_box(0);
v___x_2953_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 1, v___x_2953_);
v___x_2955_ = v___x_2950_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_mctx_2945_);
lean_ctor_set(v_reuseFailAlloc_2958_, 1, v___x_2953_);
lean_ctor_set(v_reuseFailAlloc_2958_, 2, v_zetaDeltaFVarIds_2946_);
lean_ctor_set(v_reuseFailAlloc_2958_, 3, v_postponed_2947_);
lean_ctor_set(v_reuseFailAlloc_2958_, 4, v_diag_2948_);
v___x_2955_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = lean_st_ref_put(v___y_2925_, v___x_2955_);
v___x_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2952_);
return v___x_2957_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___boxed(lean_object* v_env_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec(v___y_2966_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(lean_object* v_env_2970_, lean_object* v_x_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v___x_2977_; lean_object* v_env_2978_; lean_object* v_a_2980_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2977_ = lean_st_ref_get(v___y_2975_);
v_env_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc_ref(v_env_2978_);
lean_dec(v___x_2977_);
v___x_2990_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2970_, v___y_2973_, v___y_2975_);
lean_dec_ref(v___x_2990_);
lean_inc(v___y_2975_);
lean_inc_ref(v___y_2974_);
lean_inc(v___y_2973_);
lean_inc_ref(v___y_2972_);
v___x_2991_ = lean_apply_5(v_x_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, lean_box(0));
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref_known(v___x_2991_, 1);
v___x_2993_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2978_, v___y_2973_, v___y_2975_);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3000_ == 0)
{
lean_object* v_unused_3001_; 
v_unused_3001_ = lean_ctor_get(v___x_2993_, 0);
lean_dec(v_unused_3001_);
v___x_2995_ = v___x_2993_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_dec(v___x_2993_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 0, v_a_2992_);
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2992_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
else
{
lean_object* v_a_3002_; 
v_a_3002_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_2991_, 1);
v_a_2980_ = v_a_3002_;
goto v___jp_2979_;
}
v___jp_2979_:
{
lean_object* v___x_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
v___x_2981_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2978_, v___y_2973_, v___y_2975_);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2988_ == 0)
{
lean_object* v_unused_2989_; 
v_unused_2989_ = lean_ctor_get(v___x_2981_, 0);
lean_dec(v_unused_2989_);
v___x_2983_ = v___x_2981_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_dec(v___x_2981_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
lean_ctor_set_tag(v___x_2983_, 1);
lean_ctor_set(v___x_2983_, 0, v_a_2980_);
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2980_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___boxed(lean_object* v_env_3003_, lean_object* v_x_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_3003_, v_x_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object* v_fixedParamPerms_3011_, lean_object* v_argsPacker_3012_, lean_object* v_preDefs_3013_, lean_object* v_unaryPreDefNonRec_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_){
_start:
{
lean_object* v_levelParams_3020_; lean_object* v___x_3021_; lean_object* v_us_3022_; lean_object* v___f_3023_; lean_object* v___x_3024_; lean_object* v_env_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v_levelParams_3020_ = lean_ctor_get(v_unaryPreDefNonRec_3014_, 1);
v___x_3021_ = lean_box(0);
lean_inc(v_levelParams_3020_);
v_us_3022_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_3020_, v___x_3021_);
v___f_3023_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3023_, 0, v_unaryPreDefNonRec_3014_);
lean_closure_set(v___f_3023_, 1, v_preDefs_3013_);
lean_closure_set(v___f_3023_, 2, v_fixedParamPerms_3011_);
lean_closure_set(v___f_3023_, 3, v_us_3022_);
lean_closure_set(v___f_3023_, 4, v_argsPacker_3012_);
v___x_3024_ = lean_st_ref_get(v_a_3018_);
v_env_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc_ref(v_env_3025_);
lean_dec(v___x_3024_);
v___x_3026_ = l_Lean_Environment_unlockAsync(v_env_3025_);
v___x_3027_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v___x_3026_, v___f_3023_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___boxed(lean_object* v_fixedParamPerms_3028_, lean_object* v_argsPacker_3029_, lean_object* v_preDefs_3030_, lean_object* v_unaryPreDefNonRec_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fixedParamPerms_3028_, v_argsPacker_3029_, v_preDefs_3030_, v_unaryPreDefNonRec_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
lean_dec(v_a_3035_);
lean_dec_ref(v_a_3034_);
lean_dec(v_a_3033_);
lean_dec_ref(v_a_3032_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(lean_object* v_fixedParamPerms_3038_, lean_object* v_unaryPreDefNonRec_3039_, lean_object* v_us_3040_, lean_object* v_argsPacker_3041_, lean_object* v_as_3042_, size_t v_sz_3043_, size_t v_i_3044_, lean_object* v_bs_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_){
_start:
{
lean_object* v___x_3051_; 
v___x_3051_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_3038_, v_unaryPreDefNonRec_3039_, v_us_3040_, v_argsPacker_3041_, v_sz_3043_, v_i_3044_, v_bs_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___boxed(lean_object* v_fixedParamPerms_3052_, lean_object* v_unaryPreDefNonRec_3053_, lean_object* v_us_3054_, lean_object* v_argsPacker_3055_, lean_object* v_as_3056_, lean_object* v_sz_3057_, lean_object* v_i_3058_, lean_object* v_bs_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
size_t v_sz_boxed_3065_; size_t v_i_boxed_3066_; lean_object* v_res_3067_; 
v_sz_boxed_3065_ = lean_unbox_usize(v_sz_3057_);
lean_dec(v_sz_3057_);
v_i_boxed_3066_ = lean_unbox_usize(v_i_3058_);
lean_dec(v_i_3058_);
v_res_3067_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(v_fixedParamPerms_3052_, v_unaryPreDefNonRec_3053_, v_us_3054_, v_argsPacker_3055_, v_as_3056_, v_sz_boxed_3065_, v_i_boxed_3066_, v_bs_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec_ref(v_as_3056_);
lean_dec_ref(v_fixedParamPerms_3052_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(lean_object* v_env_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v___x_3074_; 
v___x_3074_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3068_, v___y_3070_, v___y_3072_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___boxed(lean_object* v_env_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(v_env_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(lean_object* v_00_u03b1_3082_, lean_object* v_env_3083_, lean_object* v_x_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v___x_3090_; 
v___x_3090_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_3083_, v_x_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___boxed(lean_object* v_00_u03b1_3091_, lean_object* v_env_3092_, lean_object* v_x_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(v_00_u03b1_3091_, v_env_3092_, v_x_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
return v_res_3099_;
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
