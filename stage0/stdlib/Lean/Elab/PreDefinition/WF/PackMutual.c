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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__4;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4(lean_object*);
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
uint8_t v___x_2264__boxed_179_; lean_object* v_res_180_; 
v___x_2264__boxed_179_ = lean_unbox(v___x_170_);
v_res_180_ = l_Lean_Elab_WF_withAppN___lam__0(v_args_168_, v_k_169_, v___x_2264__boxed_179_, v_missing_171_, v_xs_172_, v_x_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
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
lean_object* v___y_511_; lean_object* v_toCold_520_; lean_object* v_currRecDepth_521_; lean_object* v_ref_522_; uint16_t v_optionFlags_523_; uint8_t v_suppressElabErrors_524_; uint8_t v_checkDeprecated_525_; uint8_t v_isRecordingDeps_526_; lean_object* v_maxRecDepth_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v_toCold_520_ = lean_ctor_get(v___y_507_, 0);
v_currRecDepth_521_ = lean_ctor_get(v___y_507_, 1);
v_ref_522_ = lean_ctor_get(v___y_507_, 2);
v_optionFlags_523_ = lean_ctor_get_uint16(v___y_507_, sizeof(void*)*3);
v_suppressElabErrors_524_ = lean_ctor_get_uint8(v___y_507_, sizeof(void*)*3 + 2);
v_checkDeprecated_525_ = lean_ctor_get_uint8(v___y_507_, sizeof(void*)*3 + 3);
v_isRecordingDeps_526_ = lean_ctor_get_uint8(v___y_507_, sizeof(void*)*3 + 4);
v_maxRecDepth_532_ = lean_ctor_get(v_toCold_520_, 3);
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = lean_nat_dec_eq(v_maxRecDepth_532_, v___x_533_);
if (v___x_534_ == 0)
{
uint8_t v___x_535_; 
v___x_535_ = lean_nat_dec_eq(v_currRecDepth_521_, v_maxRecDepth_532_);
if (v___x_535_ == 0)
{
goto v___jp_527_;
}
else
{
lean_object* v___x_536_; 
lean_dec_ref(v_x_503_);
lean_inc(v_ref_522_);
v___x_536_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_522_);
v___y_511_ = v___x_536_;
goto v___jp_510_;
}
}
else
{
goto v___jp_527_;
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
v___jp_527_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_528_ = lean_unsigned_to_nat(1u);
v___x_529_ = lean_nat_add(v_currRecDepth_521_, v___x_528_);
lean_inc(v_ref_522_);
lean_inc_ref(v_toCold_520_);
v___x_530_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_530_, 0, v_toCold_520_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
lean_ctor_set(v___x_530_, 2, v_ref_522_);
lean_ctor_set_uint16(v___x_530_, sizeof(void*)*3, v_optionFlags_523_);
lean_ctor_set_uint8(v___x_530_, sizeof(void*)*3 + 2, v_suppressElabErrors_524_);
lean_ctor_set_uint8(v___x_530_, sizeof(void*)*3 + 3, v_checkDeprecated_525_);
lean_ctor_set_uint8(v___x_530_, sizeof(void*)*3 + 4, v_isRecordingDeps_526_);
lean_inc(v___y_508_);
lean_inc(v___y_506_);
lean_inc_ref(v___y_505_);
lean_inc(v___y_504_);
v___x_531_ = lean_apply_6(v_x_503_, v___y_504_, v___y_505_, v___y_506_, v___x_530_, v___y_508_, lean_box(0));
v___y_511_ = v___x_531_;
goto v___jp_510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg___boxed(lean_object* v_x_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__2(lean_object* v___x_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_545_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__2___boxed(lean_object* v___x_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__2(v___x_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(lean_object* v_k_559_, lean_object* v___y_560_, lean_object* v_b_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v___x_567_; 
lean_inc(v___y_565_);
lean_inc_ref(v___y_564_);
lean_inc(v___y_563_);
lean_inc_ref(v___y_562_);
lean_inc(v___y_560_);
v___x_567_ = lean_apply_7(v_k_559_, v_b_561_, v___y_560_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, lean_box(0));
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed(lean_object* v_k_568_, lean_object* v___y_569_, lean_object* v_b_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(v_k_568_, v___y_569_, v_b_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_569_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(lean_object* v_name_577_, lean_object* v_type_578_, lean_object* v_val_579_, lean_object* v_k_580_, uint8_t v_nondep_581_, uint8_t v_kind_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v___f_589_; lean_object* v___x_590_; 
lean_inc(v___y_583_);
v___f_589_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_589_, 0, v_k_580_);
lean_closure_set(v___f_589_, 1, v___y_583_);
v___x_590_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_577_, v_type_578_, v_val_579_, v___f_589_, v_nondep_581_, v_kind_582_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_590_) == 0)
{
return v___x_590_;
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg___boxed(lean_object* v_name_599_, lean_object* v_type_600_, lean_object* v_val_601_, lean_object* v_k_602_, lean_object* v_nondep_603_, lean_object* v_kind_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
uint8_t v_nondep_boxed_611_; uint8_t v_kind_boxed_612_; lean_object* v_res_613_; 
v_nondep_boxed_611_ = lean_unbox(v_nondep_603_);
v_kind_boxed_612_ = lean_unbox(v_kind_604_);
v_res_613_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_599_, v_type_600_, v_val_601_, v_k_602_, v_nondep_boxed_611_, v_kind_boxed_612_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(lean_object* v_name_614_, uint8_t v_bi_615_, lean_object* v_type_616_, lean_object* v_k_617_, uint8_t v_kind_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___f_625_; lean_object* v___x_626_; 
lean_inc(v___y_619_);
v___f_625_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_625_, 0, v_k_617_);
lean_closure_set(v___f_625_, 1, v___y_619_);
v___x_626_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_614_, v_bi_615_, v_type_616_, v___f_625_, v_kind_618_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
if (lean_obj_tag(v___x_626_) == 0)
{
return v___x_626_;
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___boxed(lean_object* v_name_635_, lean_object* v_bi_636_, lean_object* v_type_637_, lean_object* v_k_638_, lean_object* v_kind_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
uint8_t v_bi_boxed_646_; uint8_t v_kind_boxed_647_; lean_object* v_res_648_; 
v_bi_boxed_646_ = lean_unbox(v_bi_636_);
v_kind_boxed_647_ = lean_unbox(v_kind_639_);
v_res_648_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_635_, v_bi_boxed_646_, v_type_637_, v_k_638_, v_kind_boxed_647_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_object* v_00_u03b1_649_, lean_object* v_x_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_apply_1(v_x_650_, lean_box(0));
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0___boxed(lean_object* v_00_u03b1_658_, lean_object* v_x_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(v_00_u03b1_658_, v_x_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_spec__7___redArg(lean_object* v_a_666_, lean_object* v_x_667_){
_start:
{
if (lean_obj_tag(v_x_667_) == 0)
{
lean_object* v___x_668_; 
v___x_668_ = lean_box(0);
return v___x_668_;
}
else
{
lean_object* v_key_669_; lean_object* v_value_670_; lean_object* v_tail_671_; uint8_t v___x_672_; 
v_key_669_ = lean_ctor_get(v_x_667_, 0);
v_value_670_ = lean_ctor_get(v_x_667_, 1);
v_tail_671_ = lean_ctor_get(v_x_667_, 2);
v___x_672_ = l_Lean_ExprStructEq_beq(v_key_669_, v_a_666_);
if (v___x_672_ == 0)
{
v_x_667_ = v_tail_671_;
goto _start;
}
else
{
lean_object* v___x_674_; 
lean_inc(v_value_670_);
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v_value_670_);
return v___x_674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_a_675_, lean_object* v_x_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_spec__7___redArg(v_a_675_, v_x_676_);
lean_dec(v_x_676_);
lean_dec_ref(v_a_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___redArg(lean_object* v_m_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_buckets_680_; lean_object* v___x_681_; uint64_t v___x_682_; uint64_t v___x_683_; uint64_t v___x_684_; uint64_t v_fold_685_; uint64_t v___x_686_; uint64_t v___x_687_; uint64_t v___x_688_; size_t v___x_689_; size_t v___x_690_; size_t v___x_691_; size_t v___x_692_; size_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_buckets_680_ = lean_ctor_get(v_m_678_, 1);
v___x_681_ = lean_array_get_size(v_buckets_680_);
v___x_682_ = l_Lean_ExprStructEq_hash(v_a_679_);
v___x_683_ = 32ULL;
v___x_684_ = lean_uint64_shift_right(v___x_682_, v___x_683_);
v_fold_685_ = lean_uint64_xor(v___x_682_, v___x_684_);
v___x_686_ = 16ULL;
v___x_687_ = lean_uint64_shift_right(v_fold_685_, v___x_686_);
v___x_688_ = lean_uint64_xor(v_fold_685_, v___x_687_);
v___x_689_ = lean_uint64_to_usize(v___x_688_);
v___x_690_ = lean_usize_of_nat(v___x_681_);
v___x_691_ = ((size_t)1ULL);
v___x_692_ = lean_usize_sub(v___x_690_, v___x_691_);
v___x_693_ = lean_usize_land(v___x_689_, v___x_692_);
v___x_694_ = lean_array_uget_borrowed(v_buckets_680_, v___x_693_);
v___x_695_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_spec__7___redArg(v_a_679_, v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_m_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___redArg(v_m_696_, v_a_697_);
lean_dec_ref(v_a_697_);
lean_dec_ref(v_m_696_);
return v_res_698_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(lean_object* v_a_699_, lean_object* v_x_700_){
_start:
{
if (lean_obj_tag(v_x_700_) == 0)
{
uint8_t v___x_701_; 
v___x_701_ = 0;
return v___x_701_;
}
else
{
lean_object* v_key_702_; lean_object* v_tail_703_; uint8_t v___x_704_; 
v_key_702_ = lean_ctor_get(v_x_700_, 0);
v_tail_703_ = lean_ctor_get(v_x_700_, 2);
v___x_704_ = l_Lean_ExprStructEq_beq(v_key_702_, v_a_699_);
if (v___x_704_ == 0)
{
v_x_700_ = v_tail_703_;
goto _start;
}
else
{
return v___x_704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg___boxed(lean_object* v_a_706_, lean_object* v_x_707_){
_start:
{
uint8_t v_res_708_; lean_object* v_r_709_; 
v_res_708_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_706_, v_x_707_);
lean_dec(v_x_707_);
lean_dec_ref(v_a_706_);
v_r_709_ = lean_box(v_res_708_);
return v_r_709_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(lean_object* v_x_710_, lean_object* v_x_711_){
_start:
{
if (lean_obj_tag(v_x_711_) == 0)
{
return v_x_710_;
}
else
{
lean_object* v_key_712_; lean_object* v_value_713_; lean_object* v_tail_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_737_; 
v_key_712_ = lean_ctor_get(v_x_711_, 0);
v_value_713_ = lean_ctor_get(v_x_711_, 1);
v_tail_714_ = lean_ctor_get(v_x_711_, 2);
v_isSharedCheck_737_ = !lean_is_exclusive(v_x_711_);
if (v_isSharedCheck_737_ == 0)
{
v___x_716_ = v_x_711_;
v_isShared_717_ = v_isSharedCheck_737_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_tail_714_);
lean_inc(v_value_713_);
lean_inc(v_key_712_);
lean_dec(v_x_711_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_737_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; uint64_t v___x_719_; uint64_t v___x_720_; uint64_t v___x_721_; uint64_t v_fold_722_; uint64_t v___x_723_; uint64_t v___x_724_; uint64_t v___x_725_; size_t v___x_726_; size_t v___x_727_; size_t v___x_728_; size_t v___x_729_; size_t v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_718_ = lean_array_get_size(v_x_710_);
v___x_719_ = l_Lean_ExprStructEq_hash(v_key_712_);
v___x_720_ = 32ULL;
v___x_721_ = lean_uint64_shift_right(v___x_719_, v___x_720_);
v_fold_722_ = lean_uint64_xor(v___x_719_, v___x_721_);
v___x_723_ = 16ULL;
v___x_724_ = lean_uint64_shift_right(v_fold_722_, v___x_723_);
v___x_725_ = lean_uint64_xor(v_fold_722_, v___x_724_);
v___x_726_ = lean_uint64_to_usize(v___x_725_);
v___x_727_ = lean_usize_of_nat(v___x_718_);
v___x_728_ = ((size_t)1ULL);
v___x_729_ = lean_usize_sub(v___x_727_, v___x_728_);
v___x_730_ = lean_usize_land(v___x_726_, v___x_729_);
v___x_731_ = lean_array_uget_borrowed(v_x_710_, v___x_730_);
lean_inc(v___x_731_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 2, v___x_731_);
v___x_733_ = v___x_716_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_key_712_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_value_713_);
lean_ctor_set(v_reuseFailAlloc_736_, 2, v___x_731_);
v___x_733_ = v_reuseFailAlloc_736_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; 
v___x_734_ = lean_array_uset(v_x_710_, v___x_730_, v___x_733_);
v_x_710_ = v___x_734_;
v_x_711_ = v_tail_714_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(lean_object* v_i_738_, lean_object* v_source_739_, lean_object* v_target_740_){
_start:
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = lean_array_get_size(v_source_739_);
v___x_742_ = lean_nat_dec_lt(v_i_738_, v___x_741_);
if (v___x_742_ == 0)
{
lean_dec_ref(v_source_739_);
lean_dec(v_i_738_);
return v_target_740_;
}
else
{
lean_object* v_es_743_; lean_object* v___x_744_; lean_object* v_source_745_; lean_object* v_target_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_es_743_ = lean_array_fget(v_source_739_, v_i_738_);
v___x_744_ = lean_box(0);
v_source_745_ = lean_array_fset(v_source_739_, v_i_738_, v___x_744_);
v_target_746_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(v_target_740_, v_es_743_);
v___x_747_ = lean_unsigned_to_nat(1u);
v___x_748_ = lean_nat_add(v_i_738_, v___x_747_);
lean_dec(v_i_738_);
v_i_738_ = v___x_748_;
v_source_739_ = v_source_745_;
v_target_740_ = v_target_746_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(lean_object* v_data_750_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v_nbuckets_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_751_ = lean_array_get_size(v_data_750_);
v___x_752_ = lean_unsigned_to_nat(2u);
v_nbuckets_753_ = lean_nat_mul(v___x_751_, v___x_752_);
v___x_754_ = lean_unsigned_to_nat(0u);
v___x_755_ = lean_box(0);
v___x_756_ = lean_mk_array(v_nbuckets_753_, v___x_755_);
v___x_757_ = lean_array_propagate_mark(v_data_750_, v___x_756_);
v___x_758_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v___x_754_, v_data_750_, v___x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(lean_object* v_a_759_, lean_object* v_b_760_, lean_object* v_x_761_){
_start:
{
if (lean_obj_tag(v_x_761_) == 0)
{
lean_dec(v_b_760_);
lean_dec_ref(v_a_759_);
return v_x_761_;
}
else
{
lean_object* v_key_762_; lean_object* v_value_763_; lean_object* v_tail_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_776_; 
v_key_762_ = lean_ctor_get(v_x_761_, 0);
v_value_763_ = lean_ctor_get(v_x_761_, 1);
v_tail_764_ = lean_ctor_get(v_x_761_, 2);
v_isSharedCheck_776_ = !lean_is_exclusive(v_x_761_);
if (v_isSharedCheck_776_ == 0)
{
v___x_766_ = v_x_761_;
v_isShared_767_ = v_isSharedCheck_776_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_tail_764_);
lean_inc(v_value_763_);
lean_inc(v_key_762_);
lean_dec(v_x_761_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_776_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
uint8_t v___x_768_; 
v___x_768_ = l_Lean_ExprStructEq_beq(v_key_762_, v_a_759_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_759_, v_b_760_, v_tail_764_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 2, v___x_769_);
v___x_771_ = v___x_766_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_key_762_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_value_763_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
else
{
lean_object* v___x_774_; 
lean_dec(v_value_763_);
lean_dec(v_key_762_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v_b_760_);
lean_ctor_set(v___x_766_, 0, v_a_759_);
v___x_774_ = v___x_766_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_759_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_b_760_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v_tail_764_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(lean_object* v_m_777_, lean_object* v_a_778_, lean_object* v_b_779_){
_start:
{
lean_object* v_size_780_; lean_object* v_buckets_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_824_; 
v_size_780_ = lean_ctor_get(v_m_777_, 0);
v_buckets_781_ = lean_ctor_get(v_m_777_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v_m_777_);
if (v_isSharedCheck_824_ == 0)
{
v___x_783_ = v_m_777_;
v_isShared_784_ = v_isSharedCheck_824_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_buckets_781_);
lean_inc(v_size_780_);
lean_dec(v_m_777_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_824_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; uint64_t v___x_786_; uint64_t v___x_787_; uint64_t v___x_788_; uint64_t v_fold_789_; uint64_t v___x_790_; uint64_t v___x_791_; uint64_t v___x_792_; size_t v___x_793_; size_t v___x_794_; size_t v___x_795_; size_t v___x_796_; size_t v___x_797_; lean_object* v_bkt_798_; uint8_t v___x_799_; 
v___x_785_ = lean_array_get_size(v_buckets_781_);
v___x_786_ = l_Lean_ExprStructEq_hash(v_a_778_);
v___x_787_ = 32ULL;
v___x_788_ = lean_uint64_shift_right(v___x_786_, v___x_787_);
v_fold_789_ = lean_uint64_xor(v___x_786_, v___x_788_);
v___x_790_ = 16ULL;
v___x_791_ = lean_uint64_shift_right(v_fold_789_, v___x_790_);
v___x_792_ = lean_uint64_xor(v_fold_789_, v___x_791_);
v___x_793_ = lean_uint64_to_usize(v___x_792_);
v___x_794_ = lean_usize_of_nat(v___x_785_);
v___x_795_ = ((size_t)1ULL);
v___x_796_ = lean_usize_sub(v___x_794_, v___x_795_);
v___x_797_ = lean_usize_land(v___x_793_, v___x_796_);
v_bkt_798_ = lean_array_uget_borrowed(v_buckets_781_, v___x_797_);
v___x_799_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_778_, v_bkt_798_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; lean_object* v_size_x27_801_; lean_object* v___x_802_; lean_object* v_buckets_x27_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_800_ = lean_unsigned_to_nat(1u);
v_size_x27_801_ = lean_nat_add(v_size_780_, v___x_800_);
lean_dec(v_size_780_);
lean_inc(v_bkt_798_);
v___x_802_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_802_, 0, v_a_778_);
lean_ctor_set(v___x_802_, 1, v_b_779_);
lean_ctor_set(v___x_802_, 2, v_bkt_798_);
v_buckets_x27_803_ = lean_array_uset(v_buckets_781_, v___x_797_, v___x_802_);
v___x_804_ = lean_unsigned_to_nat(4u);
v___x_805_ = lean_nat_mul(v_size_x27_801_, v___x_804_);
v___x_806_ = lean_unsigned_to_nat(3u);
v___x_807_ = lean_nat_div(v___x_805_, v___x_806_);
lean_dec(v___x_805_);
v___x_808_ = lean_array_get_size(v_buckets_x27_803_);
v___x_809_ = lean_nat_dec_le(v___x_807_, v___x_808_);
lean_dec(v___x_807_);
if (v___x_809_ == 0)
{
lean_object* v_val_810_; lean_object* v___x_812_; 
v_val_810_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_buckets_x27_803_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v_val_810_);
lean_ctor_set(v___x_783_, 0, v_size_x27_801_);
v___x_812_ = v___x_783_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_size_x27_801_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_val_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
else
{
lean_object* v___x_815_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v_buckets_x27_803_);
lean_ctor_set(v___x_783_, 0, v_size_x27_801_);
v___x_815_ = v___x_783_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_size_x27_801_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_buckets_x27_803_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
else
{
lean_object* v___x_817_; lean_object* v_buckets_x27_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
lean_inc(v_bkt_798_);
v___x_817_ = lean_box(0);
v_buckets_x27_818_ = lean_array_uset(v_buckets_781_, v___x_797_, v___x_817_);
v___x_819_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_778_, v_b_779_, v_bkt_798_);
v___x_820_ = lean_array_uset(v_buckets_x27_818_, v___x_797_, v___x_819_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v___x_820_);
v___x_822_ = v___x_783_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_size_780_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(lean_object* v_a_825_, lean_object* v_e_826_, lean_object* v_a_827_){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_829_ = lean_st_ref_take(v_a_825_);
v___x_830_ = lean_box(0);
v___x_831_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v___x_829_, v_e_826_, v_a_827_);
v___x_832_ = lean_st_ref_put(v_a_825_, v___x_831_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed(lean_object* v_a_833_, lean_object* v_e_834_, lean_object* v_a_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(v_a_833_, v_e_834_, v_a_835_);
lean_dec(v_a_833_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed(lean_object* v_fvars_838_, lean_object* v_pre_839_, lean_object* v_post_840_, lean_object* v_usedLetOnly_841_, lean_object* v_skipConstInApp_842_, lean_object* v_skipInstances_843_, lean_object* v_postApp_844_, lean_object* v_body_845_, lean_object* v_x_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
uint8_t v_usedLetOnly_boxed_853_; uint8_t v_skipConstInApp_boxed_854_; uint8_t v_skipInstances_boxed_855_; lean_object* v_res_856_; 
v_usedLetOnly_boxed_853_ = lean_unbox(v_usedLetOnly_841_);
v_skipConstInApp_boxed_854_ = lean_unbox(v_skipConstInApp_842_);
v_skipInstances_boxed_855_ = lean_unbox(v_skipInstances_843_);
v_res_856_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(v_fvars_838_, v_pre_839_, v_post_840_, v_usedLetOnly_boxed_853_, v_skipConstInApp_boxed_854_, v_skipInstances_boxed_855_, v_postApp_844_, v_body_845_, v_x_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(lean_object* v_fvars_860_, lean_object* v_pre_861_, lean_object* v_post_862_, uint8_t v_usedLetOnly_863_, uint8_t v_skipConstInApp_864_, uint8_t v_skipInstances_865_, lean_object* v_postApp_866_, lean_object* v_body_867_, lean_object* v_x_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_array_push(v_fvars_860_, v_x_868_);
v___x_876_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_861_, v_post_862_, v_usedLetOnly_863_, v_skipConstInApp_864_, v_skipInstances_865_, v_postApp_866_, v___x_875_, v_body_867_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed(lean_object* v_fvars_877_, lean_object* v_pre_878_, lean_object* v_post_879_, lean_object* v_usedLetOnly_880_, lean_object* v_skipConstInApp_881_, lean_object* v_skipInstances_882_, lean_object* v_postApp_883_, lean_object* v_body_884_, lean_object* v_x_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
uint8_t v_usedLetOnly_boxed_892_; uint8_t v_skipConstInApp_boxed_893_; uint8_t v_skipInstances_boxed_894_; lean_object* v_res_895_; 
v_usedLetOnly_boxed_892_ = lean_unbox(v_usedLetOnly_880_);
v_skipConstInApp_boxed_893_ = lean_unbox(v_skipConstInApp_881_);
v_skipInstances_boxed_894_ = lean_unbox(v_skipInstances_882_);
v_res_895_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(v_fvars_877_, v_pre_878_, v_post_879_, v_usedLetOnly_boxed_892_, v_skipConstInApp_boxed_893_, v_skipInstances_boxed_894_, v_postApp_883_, v_body_884_, v_x_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(lean_object* v_pre_896_, lean_object* v_post_897_, uint8_t v_usedLetOnly_898_, uint8_t v_skipConstInApp_899_, uint8_t v_skipInstances_900_, lean_object* v_postApp_901_, lean_object* v_e_902_, lean_object* v_a_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; 
lean_inc_ref(v_post_897_);
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
lean_inc(v___y_905_);
lean_inc_ref(v___y_904_);
lean_inc_ref(v_e_902_);
v___x_909_ = lean_apply_6(v_post_897_, v_e_902_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, lean_box(0));
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_928_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_928_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_928_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_928_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
switch(lean_obj_tag(v_a_910_))
{
case 0:
{
lean_object* v_e_914_; lean_object* v___x_916_; 
lean_dec_ref(v_e_902_);
lean_dec_ref(v_postApp_901_);
lean_dec_ref(v_post_897_);
lean_dec_ref(v_pre_896_);
v_e_914_ = lean_ctor_get(v_a_910_, 0);
lean_inc_ref(v_e_914_);
lean_dec_ref_known(v_a_910_, 1);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v_e_914_);
v___x_916_ = v___x_912_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_e_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
case 1:
{
lean_object* v_e_918_; lean_object* v___x_919_; 
lean_del_object(v___x_912_);
lean_dec_ref(v_e_902_);
v_e_918_ = lean_ctor_get(v_a_910_, 0);
lean_inc_ref(v_e_918_);
lean_dec_ref_known(v_a_910_, 1);
v___x_919_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_896_, v_post_897_, v_usedLetOnly_898_, v_skipConstInApp_899_, v_skipInstances_900_, v_postApp_901_, v_e_918_, v_a_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
return v___x_919_;
}
default: 
{
lean_object* v_e_x3f_920_; 
lean_dec_ref(v_postApp_901_);
lean_dec_ref(v_post_897_);
lean_dec_ref(v_pre_896_);
v_e_x3f_920_ = lean_ctor_get(v_a_910_, 0);
lean_inc(v_e_x3f_920_);
lean_dec_ref_known(v_a_910_, 1);
if (lean_obj_tag(v_e_x3f_920_) == 0)
{
lean_object* v___x_922_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v_e_902_);
v___x_922_ = v___x_912_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_e_902_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
else
{
lean_object* v_val_924_; lean_object* v___x_926_; 
lean_dec_ref(v_e_902_);
v_val_924_ = lean_ctor_get(v_e_x3f_920_, 0);
lean_inc(v_val_924_);
lean_dec_ref_known(v_e_x3f_920_, 1);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v_val_924_);
v___x_926_ = v___x_912_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_val_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_dec_ref(v_e_902_);
lean_dec_ref(v_postApp_901_);
lean_dec_ref(v_post_897_);
lean_dec_ref(v_pre_896_);
v_a_929_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_909_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_909_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(lean_object* v_pre_937_, lean_object* v_post_938_, uint8_t v_usedLetOnly_939_, uint8_t v_skipConstInApp_940_, uint8_t v_skipInstances_941_, lean_object* v_postApp_942_, lean_object* v_fvars_943_, lean_object* v_e_944_, lean_object* v_a_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
if (lean_obj_tag(v_e_944_) == 6)
{
lean_object* v_binderName_951_; lean_object* v_binderType_952_; lean_object* v_body_953_; uint8_t v_binderInfo_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___f_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_binderName_951_ = lean_ctor_get(v_e_944_, 0);
lean_inc(v_binderName_951_);
v_binderType_952_ = lean_ctor_get(v_e_944_, 1);
lean_inc_ref(v_binderType_952_);
v_body_953_ = lean_ctor_get(v_e_944_, 2);
lean_inc_ref(v_body_953_);
v_binderInfo_954_ = lean_ctor_get_uint8(v_e_944_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_944_, 3);
v___x_955_ = lean_box(v_usedLetOnly_939_);
v___x_956_ = lean_box(v_skipConstInApp_940_);
v___x_957_ = lean_box(v_skipInstances_941_);
lean_inc_ref(v_postApp_942_);
lean_inc_ref(v_post_938_);
lean_inc_ref(v_pre_937_);
lean_inc_ref(v_fvars_943_);
v___f_958_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed), 15, 8);
lean_closure_set(v___f_958_, 0, v_fvars_943_);
lean_closure_set(v___f_958_, 1, v_pre_937_);
lean_closure_set(v___f_958_, 2, v_post_938_);
lean_closure_set(v___f_958_, 3, v___x_955_);
lean_closure_set(v___f_958_, 4, v___x_956_);
lean_closure_set(v___f_958_, 5, v___x_957_);
lean_closure_set(v___f_958_, 6, v_postApp_942_);
lean_closure_set(v___f_958_, 7, v_body_953_);
v___x_959_ = lean_expr_instantiate_rev(v_binderType_952_, v_fvars_943_);
lean_dec_ref(v_fvars_943_);
lean_dec_ref(v_binderType_952_);
v___x_960_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_937_, v_post_938_, v_usedLetOnly_939_, v_skipConstInApp_940_, v_skipInstances_941_, v_postApp_942_, v___x_959_, v_a_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; uint8_t v___x_962_; lean_object* v___x_963_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
v___x_962_ = 0;
v___x_963_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_951_, v_binderInfo_954_, v_a_961_, v___f_958_, v___x_962_, v_a_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
return v___x_963_;
}
else
{
lean_dec_ref(v___f_958_);
lean_dec(v_binderName_951_);
return v___x_960_;
}
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_expr_instantiate_rev(v_e_944_, v_fvars_943_);
lean_dec_ref(v_e_944_);
lean_inc_ref(v_postApp_942_);
lean_inc_ref(v_post_938_);
lean_inc_ref(v_pre_937_);
v___x_965_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_937_, v_post_938_, v_usedLetOnly_939_, v_skipConstInApp_940_, v_skipInstances_941_, v_postApp_942_, v___x_964_, v_a_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; uint8_t v___x_967_; uint8_t v___x_968_; uint8_t v___x_969_; lean_object* v___x_970_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v___x_967_ = 0;
v___x_968_ = 1;
v___x_969_ = 1;
v___x_970_ = l_Lean_Meta_mkLambdaFVars(v_fvars_943_, v_a_966_, v___x_967_, v_usedLetOnly_939_, v___x_967_, v___x_968_, v___x_969_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec_ref(v_fvars_943_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_972_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
lean_dec_ref_known(v___x_970_, 1);
v___x_972_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_937_, v_post_938_, v_usedLetOnly_939_, v_skipConstInApp_940_, v_skipInstances_941_, v_postApp_942_, v_a_971_, v_a_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
return v___x_972_;
}
else
{
lean_dec_ref(v_postApp_942_);
lean_dec_ref(v_post_938_);
lean_dec_ref(v_pre_937_);
return v___x_970_;
}
}
else
{
lean_dec_ref(v_fvars_943_);
lean_dec_ref(v_postApp_942_);
lean_dec_ref(v_post_938_);
lean_dec_ref(v_pre_937_);
return v___x_965_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(lean_object* v_fvars_973_, lean_object* v_pre_974_, lean_object* v_post_975_, uint8_t v_usedLetOnly_976_, uint8_t v_skipConstInApp_977_, uint8_t v_skipInstances_978_, lean_object* v_postApp_979_, lean_object* v_body_980_, lean_object* v_x_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = lean_array_push(v_fvars_973_, v_x_981_);
v___x_989_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_974_, v_post_975_, v_usedLetOnly_976_, v_skipConstInApp_977_, v_skipInstances_978_, v_postApp_979_, v___x_988_, v_body_980_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_990_, lean_object* v_pre_991_, lean_object* v_post_992_, lean_object* v_usedLetOnly_993_, lean_object* v_skipConstInApp_994_, lean_object* v_skipInstances_995_, lean_object* v_postApp_996_, lean_object* v_body_997_, lean_object* v_x_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
uint8_t v_usedLetOnly_boxed_1005_; uint8_t v_skipConstInApp_boxed_1006_; uint8_t v_skipInstances_boxed_1007_; lean_object* v_res_1008_; 
v_usedLetOnly_boxed_1005_ = lean_unbox(v_usedLetOnly_993_);
v_skipConstInApp_boxed_1006_ = lean_unbox(v_skipConstInApp_994_);
v_skipInstances_boxed_1007_ = lean_unbox(v_skipInstances_995_);
v_res_1008_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(v_fvars_990_, v_pre_991_, v_post_992_, v_usedLetOnly_boxed_1005_, v_skipConstInApp_boxed_1006_, v_skipInstances_boxed_1007_, v_postApp_996_, v_body_997_, v_x_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(lean_object* v_pre_1009_, lean_object* v_post_1010_, uint8_t v_usedLetOnly_1011_, uint8_t v_skipConstInApp_1012_, uint8_t v_skipInstances_1013_, lean_object* v_postApp_1014_, lean_object* v_fvars_1015_, lean_object* v_e_1016_, lean_object* v_a_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
if (lean_obj_tag(v_e_1016_) == 8)
{
lean_object* v_declName_1023_; lean_object* v_type_1024_; lean_object* v_value_1025_; lean_object* v_body_1026_; uint8_t v_nondep_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___f_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v_declName_1023_ = lean_ctor_get(v_e_1016_, 0);
lean_inc(v_declName_1023_);
v_type_1024_ = lean_ctor_get(v_e_1016_, 1);
lean_inc_ref(v_type_1024_);
v_value_1025_ = lean_ctor_get(v_e_1016_, 2);
lean_inc_ref(v_value_1025_);
v_body_1026_ = lean_ctor_get(v_e_1016_, 3);
lean_inc_ref(v_body_1026_);
v_nondep_1027_ = lean_ctor_get_uint8(v_e_1016_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1016_, 4);
v___x_1028_ = lean_box(v_usedLetOnly_1011_);
v___x_1029_ = lean_box(v_skipConstInApp_1012_);
v___x_1030_ = lean_box(v_skipInstances_1013_);
lean_inc_ref_n(v_postApp_1014_, 2);
lean_inc_ref_n(v_post_1010_, 2);
lean_inc_ref_n(v_pre_1009_, 2);
lean_inc_ref(v_fvars_1015_);
v___f_1031_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed), 15, 8);
lean_closure_set(v___f_1031_, 0, v_fvars_1015_);
lean_closure_set(v___f_1031_, 1, v_pre_1009_);
lean_closure_set(v___f_1031_, 2, v_post_1010_);
lean_closure_set(v___f_1031_, 3, v___x_1028_);
lean_closure_set(v___f_1031_, 4, v___x_1029_);
lean_closure_set(v___f_1031_, 5, v___x_1030_);
lean_closure_set(v___f_1031_, 6, v_postApp_1014_);
lean_closure_set(v___f_1031_, 7, v_body_1026_);
v___x_1032_ = lean_expr_instantiate_rev(v_type_1024_, v_fvars_1015_);
lean_dec_ref(v_type_1024_);
v___x_1033_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1009_, v_post_1010_, v_usedLetOnly_1011_, v_skipConstInApp_1012_, v_skipInstances_1013_, v_postApp_1014_, v___x_1032_, v_a_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1034_);
lean_dec_ref_known(v___x_1033_, 1);
v___x_1035_ = lean_expr_instantiate_rev(v_value_1025_, v_fvars_1015_);
lean_dec_ref(v_fvars_1015_);
lean_dec_ref(v_value_1025_);
v___x_1036_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1009_, v_post_1010_, v_usedLetOnly_1011_, v_skipConstInApp_1012_, v_skipInstances_1013_, v_postApp_1014_, v___x_1035_, v_a_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; uint8_t v___x_1038_; lean_object* v___x_1039_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref_known(v___x_1036_, 1);
v___x_1038_ = 0;
v___x_1039_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_declName_1023_, v_a_1034_, v_a_1037_, v___f_1031_, v_nondep_1027_, v___x_1038_, v_a_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
return v___x_1039_;
}
else
{
lean_dec(v_a_1034_);
lean_dec_ref(v___f_1031_);
lean_dec(v_declName_1023_);
return v___x_1036_;
}
}
else
{
lean_dec_ref(v___f_1031_);
lean_dec_ref(v_value_1025_);
lean_dec(v_declName_1023_);
lean_dec_ref(v_fvars_1015_);
lean_dec_ref(v_postApp_1014_);
lean_dec_ref(v_post_1010_);
lean_dec_ref(v_pre_1009_);
return v___x_1033_;
}
}
else
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_expr_instantiate_rev(v_e_1016_, v_fvars_1015_);
lean_dec_ref(v_e_1016_);
lean_inc_ref(v_postApp_1014_);
lean_inc_ref(v_post_1010_);
lean_inc_ref(v_pre_1009_);
v___x_1041_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1009_, v_post_1010_, v_usedLetOnly_1011_, v_skipConstInApp_1012_, v_skipInstances_1013_, v_postApp_1014_, v___x_1040_, v_a_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; uint8_t v___x_1043_; uint8_t v___x_1044_; lean_object* v___x_1045_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref_known(v___x_1041_, 1);
v___x_1043_ = 0;
v___x_1044_ = 1;
v___x_1045_ = l_Lean_Meta_mkLetFVars(v_fvars_1015_, v_a_1042_, v_usedLetOnly_1011_, v___x_1043_, v___x_1044_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec_ref(v_fvars_1015_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1047_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v___x_1047_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_1009_, v_post_1010_, v_usedLetOnly_1011_, v_skipConstInApp_1012_, v_skipInstances_1013_, v_postApp_1014_, v_a_1046_, v_a_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
return v___x_1047_;
}
else
{
lean_dec_ref(v_postApp_1014_);
lean_dec_ref(v_post_1010_);
lean_dec_ref(v_pre_1009_);
return v___x_1045_;
}
}
else
{
lean_dec_ref(v_fvars_1015_);
lean_dec_ref(v_postApp_1014_);
lean_dec_ref(v_post_1010_);
lean_dec_ref(v_pre_1009_);
return v___x_1041_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(lean_object* v_pre_1048_, lean_object* v_post_1049_, uint8_t v_usedLetOnly_1050_, uint8_t v_skipConstInApp_1051_, uint8_t v_skipInstances_1052_, lean_object* v_postApp_1053_, size_t v_sz_1054_, size_t v_i_1055_, lean_object* v_bs_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
uint8_t v___x_1063_; 
v___x_1063_ = lean_usize_dec_lt(v_i_1055_, v_sz_1054_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; 
lean_dec_ref(v_postApp_1053_);
lean_dec_ref(v_post_1049_);
lean_dec_ref(v_pre_1048_);
v___x_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1064_, 0, v_bs_1056_);
return v___x_1064_;
}
else
{
lean_object* v_v_1065_; lean_object* v___x_1066_; lean_object* v_bs_x27_1067_; lean_object* v___x_1068_; 
v_v_1065_ = lean_array_uget(v_bs_1056_, v_i_1055_);
v___x_1066_ = lean_unsigned_to_nat(0u);
v_bs_x27_1067_ = lean_array_uset(v_bs_1056_, v_i_1055_, v___x_1066_);
lean_inc_ref(v_postApp_1053_);
lean_inc_ref(v_post_1049_);
lean_inc_ref(v_pre_1048_);
v___x_1068_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1048_, v_post_1049_, v_usedLetOnly_1050_, v_skipConstInApp_1051_, v_skipInstances_1052_, v_postApp_1053_, v_v_1065_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; size_t v___x_1070_; size_t v___x_1071_; lean_object* v___x_1072_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1070_ = ((size_t)1ULL);
v___x_1071_ = lean_usize_add(v_i_1055_, v___x_1070_);
v___x_1072_ = lean_array_uset(v_bs_x27_1067_, v_i_1055_, v_a_1069_);
v_i_1055_ = v___x_1071_;
v_bs_1056_ = v___x_1072_;
goto _start;
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_dec_ref(v_bs_x27_1067_);
lean_dec_ref(v_postApp_1053_);
lean_dec_ref(v_post_1049_);
lean_dec_ref(v_pre_1048_);
v_a_1074_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1068_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1068_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__0(lean_object* v_pre_1082_, lean_object* v_post_1083_, uint8_t v_usedLetOnly_1084_, uint8_t v_skipConstInApp_1085_, uint8_t v_skipInstances_1086_, lean_object* v_postApp_1087_, lean_object* v___x_1088_, lean_object* v___y_1089_, lean_object* v_b_1090_, lean_object* v_a_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1082_, v_post_1083_, v_usedLetOnly_1084_, v_skipConstInApp_1085_, v_skipInstances_1086_, v_postApp_1087_, v___x_1088_, v___y_1089_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1107_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1107_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1107_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1102_ = lean_array_fset(v_b_1090_, v_a_1091_, v_a_1098_);
v___x_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1103_);
v___x_1105_ = v___x_1100_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec_ref(v_b_1090_);
v_a_1108_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1097_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1097_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__0___boxed(lean_object* v_pre_1116_, lean_object* v_post_1117_, lean_object* v_usedLetOnly_1118_, lean_object* v_skipConstInApp_1119_, lean_object* v_skipInstances_1120_, lean_object* v_postApp_1121_, lean_object* v___x_1122_, lean_object* v___y_1123_, lean_object* v_b_1124_, lean_object* v_a_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
uint8_t v_usedLetOnly_boxed_1131_; uint8_t v_skipConstInApp_boxed_1132_; uint8_t v_skipInstances_boxed_1133_; lean_object* v_res_1134_; 
v_usedLetOnly_boxed_1131_ = lean_unbox(v_usedLetOnly_1118_);
v_skipConstInApp_boxed_1132_ = lean_unbox(v_skipConstInApp_1119_);
v_skipInstances_boxed_1133_ = lean_unbox(v_skipInstances_1120_);
v_res_1134_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__0(v_pre_1116_, v_post_1117_, v_usedLetOnly_boxed_1131_, v_skipConstInApp_boxed_1132_, v_skipInstances_boxed_1133_, v_postApp_1121_, v___x_1122_, v___y_1123_, v_b_1124_, v_a_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v_a_1125_);
lean_dec(v___y_1123_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(lean_object* v_upperBound_1135_, lean_object* v___x_1136_, lean_object* v_pre_1137_, lean_object* v_post_1138_, uint8_t v_usedLetOnly_1139_, uint8_t v_skipConstInApp_1140_, uint8_t v_skipInstances_1141_, lean_object* v_postApp_1142_, lean_object* v_a_1143_, lean_object* v_b_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v___y_1152_; uint8_t v___x_1175_; 
v___x_1175_ = lean_nat_dec_lt(v_a_1143_, v_upperBound_1135_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; 
lean_dec(v_a_1143_);
lean_dec_ref(v_postApp_1142_);
lean_dec_ref(v_post_1138_);
lean_dec_ref(v_pre_1137_);
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v_b_1144_);
return v___x_1176_;
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1177_ = lean_array_fget_borrowed(v_b_1144_, v_a_1143_);
v___x_1178_ = lean_array_get_size(v___x_1136_);
v___x_1179_ = lean_nat_dec_lt(v_a_1143_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___f_1183_; 
lean_inc(v___x_1177_);
v___x_1180_ = lean_box(v_usedLetOnly_1139_);
v___x_1181_ = lean_box(v_skipConstInApp_1140_);
v___x_1182_ = lean_box(v_skipInstances_1141_);
lean_inc(v_a_1143_);
lean_inc(v___y_1145_);
lean_inc_ref(v_postApp_1142_);
lean_inc_ref(v_post_1138_);
lean_inc_ref(v_pre_1137_);
v___f_1183_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__0___boxed), 15, 10);
lean_closure_set(v___f_1183_, 0, v_pre_1137_);
lean_closure_set(v___f_1183_, 1, v_post_1138_);
lean_closure_set(v___f_1183_, 2, v___x_1180_);
lean_closure_set(v___f_1183_, 3, v___x_1181_);
lean_closure_set(v___f_1183_, 4, v___x_1182_);
lean_closure_set(v___f_1183_, 5, v_postApp_1142_);
lean_closure_set(v___f_1183_, 6, v___x_1177_);
lean_closure_set(v___f_1183_, 7, v___y_1145_);
lean_closure_set(v___f_1183_, 8, v_b_1144_);
lean_closure_set(v___f_1183_, 9, v_a_1143_);
v___y_1152_ = v___f_1183_;
goto v___jp_1151_;
}
else
{
lean_object* v___x_1184_; uint8_t v_isInstance_1185_; 
v___x_1184_ = lean_array_fget_borrowed(v___x_1136_, v_a_1143_);
v_isInstance_1185_ = lean_ctor_get_uint8(v___x_1184_, sizeof(void*)*1 + 4);
if (v_isInstance_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___f_1189_; 
lean_inc(v___x_1177_);
v___x_1186_ = lean_box(v_usedLetOnly_1139_);
v___x_1187_ = lean_box(v_skipConstInApp_1140_);
v___x_1188_ = lean_box(v_skipInstances_1141_);
lean_inc(v_a_1143_);
lean_inc(v___y_1145_);
lean_inc_ref(v_postApp_1142_);
lean_inc_ref(v_post_1138_);
lean_inc_ref(v_pre_1137_);
v___f_1189_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__0___boxed), 15, 10);
lean_closure_set(v___f_1189_, 0, v_pre_1137_);
lean_closure_set(v___f_1189_, 1, v_post_1138_);
lean_closure_set(v___f_1189_, 2, v___x_1186_);
lean_closure_set(v___f_1189_, 3, v___x_1187_);
lean_closure_set(v___f_1189_, 4, v___x_1188_);
lean_closure_set(v___f_1189_, 5, v_postApp_1142_);
lean_closure_set(v___f_1189_, 6, v___x_1177_);
lean_closure_set(v___f_1189_, 7, v___y_1145_);
lean_closure_set(v___f_1189_, 8, v_b_1144_);
lean_closure_set(v___f_1189_, 9, v_a_1143_);
v___y_1152_ = v___f_1189_;
goto v___jp_1151_;
}
else
{
lean_object* v___x_1190_; lean_object* v___f_1191_; 
v___x_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1190_, 0, v_b_1144_);
v___f_1191_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1191_, 0, v___x_1190_);
v___y_1152_ = v___f_1191_;
goto v___jp_1151_;
}
}
}
v___jp_1151_:
{
lean_object* v___x_1153_; 
lean_inc(v___y_1149_);
lean_inc_ref(v___y_1148_);
lean_inc(v___y_1147_);
lean_inc_ref(v___y_1146_);
v___x_1153_ = lean_apply_5(v___y_1152_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, lean_box(0));
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1166_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1156_ = v___x_1153_;
v_isShared_1157_ = v_isSharedCheck_1166_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1153_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1166_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
if (lean_obj_tag(v_a_1154_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; 
lean_dec(v_a_1143_);
lean_dec_ref(v_postApp_1142_);
lean_dec_ref(v_post_1138_);
lean_dec_ref(v_pre_1137_);
v_a_1158_ = lean_ctor_get(v_a_1154_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v_a_1154_, 1);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 0, v_a_1158_);
v___x_1160_ = v___x_1156_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_del_object(v___x_1156_);
v_a_1162_ = lean_ctor_get(v_a_1154_, 0);
lean_inc(v_a_1162_);
lean_dec_ref_known(v_a_1154_, 1);
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_nat_add(v_a_1143_, v___x_1163_);
lean_dec(v_a_1143_);
v_a_1143_ = v___x_1164_;
v_b_1144_ = v_a_1162_;
goto _start;
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec(v_a_1143_);
lean_dec_ref(v_postApp_1142_);
lean_dec_ref(v_post_1138_);
lean_dec_ref(v_pre_1137_);
v_a_1167_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1153_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1153_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(uint8_t v_skipInstances_1192_, lean_object* v_pre_1193_, lean_object* v_post_1194_, uint8_t v_usedLetOnly_1195_, uint8_t v_skipConstInApp_1196_, lean_object* v_postApp_1197_, lean_object* v___y_1198_, lean_object* v_x_1199_, lean_object* v_x_1200_, lean_object* v_x_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_f_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; 
if (lean_obj_tag(v_x_1199_) == 5)
{
lean_object* v_fn_1261_; lean_object* v_arg_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v_fn_1261_ = lean_ctor_get(v_x_1199_, 0);
lean_inc_ref(v_fn_1261_);
v_arg_1262_ = lean_ctor_get(v_x_1199_, 1);
lean_inc_ref(v_arg_1262_);
lean_dec_ref_known(v_x_1199_, 2);
v___x_1263_ = lean_array_set(v_x_1200_, v_x_1201_, v_arg_1262_);
v___x_1264_ = lean_unsigned_to_nat(1u);
v___x_1265_ = lean_nat_sub(v_x_1201_, v___x_1264_);
lean_dec(v_x_1201_);
v_x_1199_ = v_fn_1261_;
v_x_1200_ = v___x_1263_;
v_x_1201_ = v___x_1265_;
goto _start;
}
else
{
lean_dec(v_x_1201_);
if (v_skipConstInApp_1196_ == 0)
{
goto v___jp_1258_;
}
else
{
uint8_t v___x_1267_; 
v___x_1267_ = l_Lean_Expr_isConst(v_x_1199_);
if (v___x_1267_ == 0)
{
goto v___jp_1258_;
}
else
{
v_f_1209_ = v_x_1199_;
v___y_1210_ = v___y_1202_;
v___y_1211_ = v___y_1203_;
v___y_1212_ = v___y_1204_;
v___y_1213_ = v___y_1205_;
v___y_1214_ = v___y_1206_;
goto v___jp_1208_;
}
}
}
v___jp_1208_:
{
if (v_skipInstances_1192_ == 0)
{
size_t v_sz_1215_; size_t v___x_1216_; lean_object* v___x_1217_; 
v_sz_1215_ = lean_array_size(v_x_1200_);
v___x_1216_ = ((size_t)0ULL);
lean_inc_ref(v_postApp_1197_);
lean_inc_ref(v_post_1194_);
lean_inc_ref(v_pre_1193_);
v___x_1217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1193_, v_post_1194_, v_usedLetOnly_1195_, v_skipConstInApp_1196_, v_skipInstances_1192_, v_postApp_1197_, v_sz_1215_, v___x_1216_, v_x_1200_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1217_, 1);
v___x_1219_ = l_Lean_mkAppN(v_f_1209_, v_a_1218_);
lean_dec(v_a_1218_);
lean_inc_ref(v_postApp_1197_);
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
lean_inc(v___y_1212_);
lean_inc_ref(v___y_1211_);
v___x_1220_ = lean_apply_7(v_postApp_1197_, v___y_1198_, v___x_1219_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, lean_box(0));
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1222_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v___x_1220_, 1);
v___x_1222_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_1193_, v_post_1194_, v_usedLetOnly_1195_, v_skipConstInApp_1196_, v_skipInstances_1192_, v_postApp_1197_, v_a_1221_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
return v___x_1222_;
}
else
{
lean_dec_ref(v_postApp_1197_);
lean_dec_ref(v_post_1194_);
lean_dec_ref(v_pre_1193_);
return v___x_1220_;
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec_ref(v_f_1209_);
lean_dec_ref(v___y_1198_);
lean_dec_ref(v_postApp_1197_);
lean_dec_ref(v_post_1194_);
lean_dec_ref(v_pre_1193_);
v_a_1223_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1217_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1217_);
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
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = lean_array_get_size(v_x_1200_);
lean_inc_ref(v_f_1209_);
v___x_1232_ = l_Lean_Meta_getFunInfoNArgs(v_f_1209_, v___x_1231_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v_paramInfo_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1232_, 1);
v_paramInfo_1234_ = lean_ctor_get(v_a_1233_, 0);
lean_inc_ref(v_paramInfo_1234_);
lean_dec(v_a_1233_);
v___x_1235_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_postApp_1197_);
lean_inc_ref(v_post_1194_);
lean_inc_ref(v_pre_1193_);
v___x_1236_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v___x_1231_, v_paramInfo_1234_, v_pre_1193_, v_post_1194_, v_usedLetOnly_1195_, v_skipConstInApp_1196_, v_skipInstances_1192_, v_postApp_1197_, v___x_1235_, v_x_1200_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec_ref(v_paramInfo_1234_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___x_1236_, 1);
v___x_1238_ = l_Lean_mkAppN(v_f_1209_, v_a_1237_);
lean_dec(v_a_1237_);
lean_inc_ref(v_postApp_1197_);
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
lean_inc(v___y_1212_);
lean_inc_ref(v___y_1211_);
v___x_1239_ = lean_apply_7(v_postApp_1197_, v___y_1198_, v___x_1238_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, lean_box(0));
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1241_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref_known(v___x_1239_, 1);
v___x_1241_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_1193_, v_post_1194_, v_usedLetOnly_1195_, v_skipConstInApp_1196_, v_skipInstances_1192_, v_postApp_1197_, v_a_1240_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
return v___x_1241_;
}
else
{
lean_dec_ref(v_postApp_1197_);
lean_dec_ref(v_post_1194_);
lean_dec_ref(v_pre_1193_);
return v___x_1239_;
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec_ref(v_f_1209_);
lean_dec_ref(v___y_1198_);
lean_dec_ref(v_postApp_1197_);
lean_dec_ref(v_post_1194_);
lean_dec_ref(v_pre_1193_);
v_a_1242_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1236_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1236_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec_ref(v_f_1209_);
lean_dec_ref(v_x_1200_);
lean_dec_ref(v___y_1198_);
lean_dec_ref(v_postApp_1197_);
lean_dec_ref(v_post_1194_);
lean_dec_ref(v_pre_1193_);
v_a_1250_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1232_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1232_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
v___jp_1258_:
{
lean_object* v___x_1259_; 
lean_inc_ref(v_postApp_1197_);
lean_inc_ref(v_post_1194_);
lean_inc_ref(v_pre_1193_);
v___x_1259_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1193_, v_post_1194_, v_usedLetOnly_1195_, v_skipConstInApp_1196_, v_skipInstances_1192_, v_postApp_1197_, v_x_1199_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___x_1259_, 1);
v_f_1209_ = v_a_1260_;
v___y_1210_ = v___y_1202_;
v___y_1211_ = v___y_1203_;
v___y_1212_ = v___y_1204_;
v___y_1213_ = v___y_1205_;
v___y_1214_ = v___y_1206_;
goto v___jp_1208_;
}
else
{
lean_dec_ref(v_x_1200_);
lean_dec_ref(v___y_1198_);
lean_dec_ref(v_postApp_1197_);
lean_dec_ref(v_post_1194_);
lean_dec_ref(v_pre_1193_);
return v___x_1259_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(lean_object* v___x_1268_, lean_object* v_pre_1269_, lean_object* v_e_1270_, lean_object* v_post_1271_, uint8_t v_usedLetOnly_1272_, uint8_t v_skipConstInApp_1273_, uint8_t v_skipInstances_1274_, lean_object* v_postApp_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_Core_checkSystem(v___x_1268_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v___x_1283_; 
lean_dec_ref_known(v___x_1282_, 1);
lean_inc_ref(v_pre_1269_);
lean_inc(v___y_1280_);
lean_inc_ref(v___y_1279_);
lean_inc(v___y_1278_);
lean_inc_ref(v___y_1277_);
lean_inc_ref(v_e_1270_);
v___x_1283_ = lean_apply_6(v_pre_1269_, v_e_1270_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, lean_box(0));
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1332_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1332_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1332_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___y_1289_; 
switch(lean_obj_tag(v_a_1284_))
{
case 0:
{
lean_object* v_e_1324_; lean_object* v___x_1326_; 
lean_dec_ref(v_postApp_1275_);
lean_dec_ref(v_post_1271_);
lean_dec_ref(v_e_1270_);
lean_dec_ref(v_pre_1269_);
v_e_1324_ = lean_ctor_get(v_a_1284_, 0);
lean_inc_ref(v_e_1324_);
lean_dec_ref_known(v_a_1284_, 1);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v_e_1324_);
v___x_1326_ = v___x_1286_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_e_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
case 1:
{
lean_object* v_e_1328_; lean_object* v___x_1329_; 
lean_del_object(v___x_1286_);
lean_dec_ref(v_e_1270_);
v_e_1328_ = lean_ctor_get(v_a_1284_, 0);
lean_inc_ref(v_e_1328_);
lean_dec_ref_known(v_a_1284_, 1);
v___x_1329_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1269_, v_post_1271_, v_usedLetOnly_1272_, v_skipConstInApp_1273_, v_skipInstances_1274_, v_postApp_1275_, v_e_1328_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1329_;
}
default: 
{
lean_object* v_e_x3f_1330_; 
lean_del_object(v___x_1286_);
v_e_x3f_1330_ = lean_ctor_get(v_a_1284_, 0);
lean_inc(v_e_x3f_1330_);
lean_dec_ref_known(v_a_1284_, 1);
if (lean_obj_tag(v_e_x3f_1330_) == 0)
{
v___y_1289_ = v_e_1270_;
goto v___jp_1288_;
}
else
{
lean_object* v_val_1331_; 
lean_dec_ref(v_e_1270_);
v_val_1331_ = lean_ctor_get(v_e_x3f_1330_, 0);
lean_inc(v_val_1331_);
lean_dec_ref_known(v_e_x3f_1330_, 1);
v___y_1289_ = v_val_1331_;
goto v___jp_1288_;
}
}
}
v___jp_1288_:
{
switch(lean_obj_tag(v___y_1289_))
{
case 7:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1291_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1269_, v_post_1271_, v_usedLetOnly_1272_, v_skipConstInApp_1273_, v_skipInstances_1274_, v_postApp_1275_, v___x_1290_, v___y_1289_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1291_;
}
case 6:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1293_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1269_, v_post_1271_, v_usedLetOnly_1272_, v_skipConstInApp_1273_, v_skipInstances_1274_, v_postApp_1275_, v___x_1292_, v___y_1289_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1293_;
}
case 8:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1295_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1269_, v_post_1271_, v_usedLetOnly_1272_, v_skipConstInApp_1273_, v_skipInstances_1274_, v_postApp_1275_, v___x_1294_, v___y_1289_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1295_;
}
case 5:
{
lean_object* v_dummy_1296_; lean_object* v_nargs_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v_dummy_1296_ = lean_obj_once(&l_Lean_Elab_WF_withAppN___closed__0, &l_Lean_Elab_WF_withAppN___closed__0_once, _init_l_Lean_Elab_WF_withAppN___closed__0);
v_nargs_1297_ = l_Lean_Expr_getAppNumArgs(v___y_1289_);
lean_inc(v_nargs_1297_);
v___x_1298_ = lean_mk_array(v_nargs_1297_, v_dummy_1296_);
v___x_1299_ = lean_unsigned_to_nat(1u);
v___x_1300_ = lean_nat_sub(v_nargs_1297_, v___x_1299_);
lean_dec(v_nargs_1297_);
lean_inc_ref(v___y_1289_);
v___x_1301_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_1274_, v_pre_1269_, v_post_1271_, v_usedLetOnly_1272_, v_skipConstInApp_1273_, v_postApp_1275_, v___y_1289_, v___y_1289_, v___x_1298_, v___x_1300_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1301_;
}
case 10:
{
lean_object* v_data_1302_; lean_object* v_expr_1303_; lean_object* v___x_1304_; 
v_data_1302_ = lean_ctor_get(v___y_1289_, 0);
v_expr_1303_ = lean_ctor_get(v___y_1289_, 1);
lean_inc_ref(v_expr_1303_);
lean_inc_ref(v_postApp_1275_);
lean_inc_ref(v_post_1271_);
lean_inc_ref(v_pre_1269_);
v___x_1304_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1269_, v_post_1271_, v_usedLetOnly_1272_, v_skipConstInApp_1273_, v_skipInstances_1274_, v_postApp_1275_, v_expr_1303_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; size_t v___x_1306_; size_t v___x_1307_; uint8_t v___x_1308_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1304_, 1);
v___x_1306_ = lean_ptr_addr(v_expr_1303_);
v___x_1307_ = lean_ptr_addr(v_a_1305_);
v___x_1308_ = lean_usize_dec_eq(v___x_1306_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_inc(v_data_1302_);
lean_dec_ref_known(v___y_1289_, 2);
v___x_1309_ = l_Lean_Expr_mdata___override(v_data_1302_, v_a_1305_);
v___x_1310_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_1269_, v_post_1271_, v_usedLetOnly_1272_, v_skipConstInApp_1273_, v_skipInstances_1274_, v_postApp_1275_, v___x_1309_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1310_;
}
else
{
lean_object* v___x_1311_; 
lean_dec(v_a_1305_);
v___x_1311_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_1269_, v_post_1271_, v_usedLetOnly_1272_, v_skipConstInApp_1273_, v_skipInstances_1274_, v_postApp_1275_, v___y_1289_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1311_;
}
}
else
{
lean_dec_ref_known(v___y_1289_, 2);
lean_dec_ref(v_postApp_1275_);
lean_dec_ref(v_post_1271_);
lean_dec_ref(v_pre_1269_);
return v___x_1304_;
}
}
case 11:
{
lean_object* v_typeName_1312_; lean_object* v_idx_1313_; lean_object* v_struct_1314_; lean_object* v___x_1315_; 
v_typeName_1312_ = lean_ctor_get(v___y_1289_, 0);
v_idx_1313_ = lean_ctor_get(v___y_1289_, 1);
v_struct_1314_ = lean_ctor_get(v___y_1289_, 2);
lean_inc_ref(v_struct_1314_);
lean_inc_ref(v_postApp_1275_);
lean_inc_ref(v_post_1271_);
lean_inc_ref(v_pre_1269_);
v___x_1315_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1269_, v_post_1271_, v_usedLetOnly_1272_, v_skipConstInApp_1273_, v_skipInstances_1274_, v_postApp_1275_, v_struct_1314_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; size_t v___x_1317_; size_t v___x_1318_; uint8_t v___x_1319_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1315_, 1);
v___x_1317_ = lean_ptr_addr(v_struct_1314_);
v___x_1318_ = lean_ptr_addr(v_a_1316_);
v___x_1319_ = lean_usize_dec_eq(v___x_1317_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_inc(v_idx_1313_);
lean_inc(v_typeName_1312_);
lean_dec_ref_known(v___y_1289_, 3);
v___x_1320_ = l_Lean_Expr_proj___override(v_typeName_1312_, v_idx_1313_, v_a_1316_);
v___x_1321_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_1269_, v_post_1271_, v_usedLetOnly_1272_, v_skipConstInApp_1273_, v_skipInstances_1274_, v_postApp_1275_, v___x_1320_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1321_;
}
else
{
lean_object* v___x_1322_; 
lean_dec(v_a_1316_);
v___x_1322_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_1269_, v_post_1271_, v_usedLetOnly_1272_, v_skipConstInApp_1273_, v_skipInstances_1274_, v_postApp_1275_, v___y_1289_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1322_;
}
}
else
{
lean_dec_ref_known(v___y_1289_, 3);
lean_dec_ref(v_postApp_1275_);
lean_dec_ref(v_post_1271_);
lean_dec_ref(v_pre_1269_);
return v___x_1315_;
}
}
default: 
{
lean_object* v___x_1323_; 
v___x_1323_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_1269_, v_post_1271_, v_usedLetOnly_1272_, v_skipConstInApp_1273_, v_skipInstances_1274_, v_postApp_1275_, v___y_1289_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1323_;
}
}
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec_ref(v_postApp_1275_);
lean_dec_ref(v_post_1271_);
lean_dec_ref(v_e_1270_);
lean_dec_ref(v_pre_1269_);
v_a_1333_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1283_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1283_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref(v_postApp_1275_);
lean_dec_ref(v_post_1271_);
lean_dec_ref(v_e_1270_);
lean_dec_ref(v_pre_1269_);
v_a_1341_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1282_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1282_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed(lean_object* v___x_1349_, lean_object* v_pre_1350_, lean_object* v_e_1351_, lean_object* v_post_1352_, lean_object* v_usedLetOnly_1353_, lean_object* v_skipConstInApp_1354_, lean_object* v_skipInstances_1355_, lean_object* v_postApp_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
uint8_t v_usedLetOnly_boxed_1363_; uint8_t v_skipConstInApp_boxed_1364_; uint8_t v_skipInstances_boxed_1365_; lean_object* v_res_1366_; 
v_usedLetOnly_boxed_1363_ = lean_unbox(v_usedLetOnly_1353_);
v_skipConstInApp_boxed_1364_ = lean_unbox(v_skipConstInApp_1354_);
v_skipInstances_boxed_1365_ = lean_unbox(v_skipInstances_1355_);
v_res_1366_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(v___x_1349_, v_pre_1350_, v_e_1351_, v_post_1352_, v_usedLetOnly_boxed_1363_, v_skipConstInApp_boxed_1364_, v_skipInstances_boxed_1365_, v_postApp_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(lean_object* v_pre_1367_, lean_object* v_post_1368_, uint8_t v_usedLetOnly_1369_, uint8_t v_skipConstInApp_1370_, uint8_t v_skipInstances_1371_, lean_object* v_postApp_1372_, lean_object* v_e_1373_, lean_object* v_a_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
lean_inc(v_a_1374_);
v___x_1380_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1380_, 0, lean_box(0));
lean_closure_set(v___x_1380_, 1, lean_box(0));
lean_closure_set(v___x_1380_, 2, v_a_1374_);
v___x_1381_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___x_1380_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1416_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1384_ = v___x_1381_;
v_isShared_1385_ = v_isSharedCheck_1416_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1416_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___redArg(v_a_1382_, v_e_1373_);
lean_dec(v_a_1382_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___f_1391_; lean_object* v___x_1392_; 
lean_del_object(v___x_1384_);
v___x_1387_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0));
v___x_1388_ = lean_box(v_usedLetOnly_1369_);
v___x_1389_ = lean_box(v_skipConstInApp_1370_);
v___x_1390_ = lean_box(v_skipInstances_1371_);
lean_inc_ref(v_e_1373_);
v___f_1391_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed), 14, 8);
lean_closure_set(v___f_1391_, 0, v___x_1387_);
lean_closure_set(v___f_1391_, 1, v_pre_1367_);
lean_closure_set(v___f_1391_, 2, v_e_1373_);
lean_closure_set(v___f_1391_, 3, v_post_1368_);
lean_closure_set(v___f_1391_, 4, v___x_1388_);
lean_closure_set(v___f_1391_, 5, v___x_1389_);
lean_closure_set(v___f_1391_, 6, v___x_1390_);
lean_closure_set(v___f_1391_, 7, v_postApp_1372_);
v___x_1392_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v___f_1391_, v_a_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___f_1394_; lean_object* v___x_1395_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc_n(v_a_1393_, 2);
lean_dec_ref_known(v___x_1392_, 1);
lean_inc(v_a_1374_);
v___f_1394_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1394_, 0, v_a_1374_);
lean_closure_set(v___f_1394_, 1, v_e_1373_);
lean_closure_set(v___f_1394_, 2, v_a_1393_);
v___x_1395_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___f_1394_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; 
v_unused_1403_ = lean_ctor_get(v___x_1395_, 0);
lean_dec(v_unused_1403_);
v___x_1397_ = v___x_1395_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_dec(v___x_1395_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v_a_1393_);
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1393_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_dec(v_a_1393_);
v_a_1404_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1395_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1395_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
else
{
lean_dec_ref(v_e_1373_);
return v___x_1392_;
}
}
else
{
lean_object* v_val_1412_; lean_object* v___x_1414_; 
lean_dec_ref(v_e_1373_);
lean_dec_ref(v_postApp_1372_);
lean_dec_ref(v_post_1368_);
lean_dec_ref(v_pre_1367_);
v_val_1412_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_val_1412_);
lean_dec_ref_known(v___x_1386_, 1);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v_val_1412_);
v___x_1414_ = v___x_1384_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_val_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec_ref(v_e_1373_);
lean_dec_ref(v_postApp_1372_);
lean_dec_ref(v_post_1368_);
lean_dec_ref(v_pre_1367_);
v_a_1417_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1381_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1381_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(lean_object* v_pre_1425_, lean_object* v_post_1426_, uint8_t v_usedLetOnly_1427_, uint8_t v_skipConstInApp_1428_, uint8_t v_skipInstances_1429_, lean_object* v_postApp_1430_, lean_object* v_fvars_1431_, lean_object* v_e_1432_, lean_object* v_a_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
if (lean_obj_tag(v_e_1432_) == 7)
{
lean_object* v_binderName_1439_; lean_object* v_binderType_1440_; lean_object* v_body_1441_; uint8_t v_binderInfo_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___f_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v_binderName_1439_ = lean_ctor_get(v_e_1432_, 0);
lean_inc(v_binderName_1439_);
v_binderType_1440_ = lean_ctor_get(v_e_1432_, 1);
lean_inc_ref(v_binderType_1440_);
v_body_1441_ = lean_ctor_get(v_e_1432_, 2);
lean_inc_ref(v_body_1441_);
v_binderInfo_1442_ = lean_ctor_get_uint8(v_e_1432_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1432_, 3);
v___x_1443_ = lean_box(v_usedLetOnly_1427_);
v___x_1444_ = lean_box(v_skipConstInApp_1428_);
v___x_1445_ = lean_box(v_skipInstances_1429_);
lean_inc_ref(v_postApp_1430_);
lean_inc_ref(v_post_1426_);
lean_inc_ref(v_pre_1425_);
lean_inc_ref(v_fvars_1431_);
v___f_1446_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed), 15, 8);
lean_closure_set(v___f_1446_, 0, v_fvars_1431_);
lean_closure_set(v___f_1446_, 1, v_pre_1425_);
lean_closure_set(v___f_1446_, 2, v_post_1426_);
lean_closure_set(v___f_1446_, 3, v___x_1443_);
lean_closure_set(v___f_1446_, 4, v___x_1444_);
lean_closure_set(v___f_1446_, 5, v___x_1445_);
lean_closure_set(v___f_1446_, 6, v_postApp_1430_);
lean_closure_set(v___f_1446_, 7, v_body_1441_);
v___x_1447_ = lean_expr_instantiate_rev(v_binderType_1440_, v_fvars_1431_);
lean_dec_ref(v_fvars_1431_);
lean_dec_ref(v_binderType_1440_);
v___x_1448_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1425_, v_post_1426_, v_usedLetOnly_1427_, v_skipConstInApp_1428_, v_skipInstances_1429_, v_postApp_1430_, v___x_1447_, v_a_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; uint8_t v___x_1450_; lean_object* v___x_1451_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1448_, 1);
v___x_1450_ = 0;
v___x_1451_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_1439_, v_binderInfo_1442_, v_a_1449_, v___f_1446_, v___x_1450_, v_a_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
return v___x_1451_;
}
else
{
lean_dec_ref(v___f_1446_);
lean_dec(v_binderName_1439_);
return v___x_1448_;
}
}
else
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_expr_instantiate_rev(v_e_1432_, v_fvars_1431_);
lean_dec_ref(v_e_1432_);
lean_inc_ref(v_postApp_1430_);
lean_inc_ref(v_post_1426_);
lean_inc_ref(v_pre_1425_);
v___x_1453_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1425_, v_post_1426_, v_usedLetOnly_1427_, v_skipConstInApp_1428_, v_skipInstances_1429_, v_postApp_1430_, v___x_1452_, v_a_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; uint8_t v___x_1455_; uint8_t v___x_1456_; uint8_t v___x_1457_; lean_object* v___x_1458_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref_known(v___x_1453_, 1);
v___x_1455_ = 0;
v___x_1456_ = 1;
v___x_1457_ = 1;
v___x_1458_ = l_Lean_Meta_mkForallFVars(v_fvars_1431_, v_a_1454_, v___x_1455_, v_usedLetOnly_1427_, v___x_1456_, v___x_1457_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
lean_dec_ref(v_fvars_1431_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1460_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___x_1458_, 1);
v___x_1460_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_1425_, v_post_1426_, v_usedLetOnly_1427_, v_skipConstInApp_1428_, v_skipInstances_1429_, v_postApp_1430_, v_a_1459_, v_a_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
return v___x_1460_;
}
else
{
lean_dec_ref(v_postApp_1430_);
lean_dec_ref(v_post_1426_);
lean_dec_ref(v_pre_1425_);
return v___x_1458_;
}
}
else
{
lean_dec_ref(v_fvars_1431_);
lean_dec_ref(v_postApp_1430_);
lean_dec_ref(v_post_1426_);
lean_dec_ref(v_pre_1425_);
return v___x_1453_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(lean_object* v_fvars_1461_, lean_object* v_pre_1462_, lean_object* v_post_1463_, uint8_t v_usedLetOnly_1464_, uint8_t v_skipConstInApp_1465_, uint8_t v_skipInstances_1466_, lean_object* v_postApp_1467_, lean_object* v_body_1468_, lean_object* v_x_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = lean_array_push(v_fvars_1461_, v_x_1469_);
v___x_1477_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1462_, v_post_1463_, v_usedLetOnly_1464_, v_skipConstInApp_1465_, v_skipInstances_1466_, v_postApp_1467_, v___x_1476_, v_body_1468_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___boxed(lean_object* v_pre_1478_, lean_object* v_post_1479_, lean_object* v_usedLetOnly_1480_, lean_object* v_skipConstInApp_1481_, lean_object* v_skipInstances_1482_, lean_object* v_postApp_1483_, lean_object* v_e_1484_, lean_object* v_a_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
uint8_t v_usedLetOnly_boxed_1491_; uint8_t v_skipConstInApp_boxed_1492_; uint8_t v_skipInstances_boxed_1493_; lean_object* v_res_1494_; 
v_usedLetOnly_boxed_1491_ = lean_unbox(v_usedLetOnly_1480_);
v_skipConstInApp_boxed_1492_ = lean_unbox(v_skipConstInApp_1481_);
v_skipInstances_boxed_1493_ = lean_unbox(v_skipInstances_1482_);
v_res_1494_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_pre_1478_, v_post_1479_, v_usedLetOnly_boxed_1491_, v_skipConstInApp_boxed_1492_, v_skipInstances_boxed_1493_, v_postApp_1483_, v_e_1484_, v_a_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v_a_1485_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7___boxed(lean_object* v_pre_1495_, lean_object* v_post_1496_, lean_object* v_usedLetOnly_1497_, lean_object* v_skipConstInApp_1498_, lean_object* v_skipInstances_1499_, lean_object* v_postApp_1500_, lean_object* v_sz_1501_, lean_object* v_i_1502_, lean_object* v_bs_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
uint8_t v_usedLetOnly_boxed_1510_; uint8_t v_skipConstInApp_boxed_1511_; uint8_t v_skipInstances_boxed_1512_; size_t v_sz_boxed_1513_; size_t v_i_boxed_1514_; lean_object* v_res_1515_; 
v_usedLetOnly_boxed_1510_ = lean_unbox(v_usedLetOnly_1497_);
v_skipConstInApp_boxed_1511_ = lean_unbox(v_skipConstInApp_1498_);
v_skipInstances_boxed_1512_ = lean_unbox(v_skipInstances_1499_);
v_sz_boxed_1513_ = lean_unbox_usize(v_sz_1501_);
lean_dec(v_sz_1501_);
v_i_boxed_1514_ = lean_unbox_usize(v_i_1502_);
lean_dec(v_i_1502_);
v_res_1515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1495_, v_post_1496_, v_usedLetOnly_boxed_1510_, v_skipConstInApp_boxed_1511_, v_skipInstances_boxed_1512_, v_postApp_1500_, v_sz_boxed_1513_, v_i_boxed_1514_, v_bs_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___boxed(lean_object* v_pre_1516_, lean_object* v_post_1517_, lean_object* v_usedLetOnly_1518_, lean_object* v_skipConstInApp_1519_, lean_object* v_skipInstances_1520_, lean_object* v_postApp_1521_, lean_object* v_e_1522_, lean_object* v_a_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
uint8_t v_usedLetOnly_boxed_1529_; uint8_t v_skipConstInApp_boxed_1530_; uint8_t v_skipInstances_boxed_1531_; lean_object* v_res_1532_; 
v_usedLetOnly_boxed_1529_ = lean_unbox(v_usedLetOnly_1518_);
v_skipConstInApp_boxed_1530_ = lean_unbox(v_skipConstInApp_1519_);
v_skipInstances_boxed_1531_ = lean_unbox(v_skipInstances_1520_);
v_res_1532_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1516_, v_post_1517_, v_usedLetOnly_boxed_1529_, v_skipConstInApp_boxed_1530_, v_skipInstances_boxed_1531_, v_postApp_1521_, v_e_1522_, v_a_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v_a_1523_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___boxed(lean_object* v_pre_1533_, lean_object* v_post_1534_, lean_object* v_usedLetOnly_1535_, lean_object* v_skipConstInApp_1536_, lean_object* v_skipInstances_1537_, lean_object* v_postApp_1538_, lean_object* v_fvars_1539_, lean_object* v_e_1540_, lean_object* v_a_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
uint8_t v_usedLetOnly_boxed_1547_; uint8_t v_skipConstInApp_boxed_1548_; uint8_t v_skipInstances_boxed_1549_; lean_object* v_res_1550_; 
v_usedLetOnly_boxed_1547_ = lean_unbox(v_usedLetOnly_1535_);
v_skipConstInApp_boxed_1548_ = lean_unbox(v_skipConstInApp_1536_);
v_skipInstances_boxed_1549_ = lean_unbox(v_skipInstances_1537_);
v_res_1550_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1533_, v_post_1534_, v_usedLetOnly_boxed_1547_, v_skipConstInApp_boxed_1548_, v_skipInstances_boxed_1549_, v_postApp_1538_, v_fvars_1539_, v_e_1540_, v_a_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v_a_1541_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___boxed(lean_object* v_pre_1551_, lean_object* v_post_1552_, lean_object* v_usedLetOnly_1553_, lean_object* v_skipConstInApp_1554_, lean_object* v_skipInstances_1555_, lean_object* v_postApp_1556_, lean_object* v_fvars_1557_, lean_object* v_e_1558_, lean_object* v_a_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
uint8_t v_usedLetOnly_boxed_1565_; uint8_t v_skipConstInApp_boxed_1566_; uint8_t v_skipInstances_boxed_1567_; lean_object* v_res_1568_; 
v_usedLetOnly_boxed_1565_ = lean_unbox(v_usedLetOnly_1553_);
v_skipConstInApp_boxed_1566_ = lean_unbox(v_skipConstInApp_1554_);
v_skipInstances_boxed_1567_ = lean_unbox(v_skipInstances_1555_);
v_res_1568_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1551_, v_post_1552_, v_usedLetOnly_boxed_1565_, v_skipConstInApp_boxed_1566_, v_skipInstances_boxed_1567_, v_postApp_1556_, v_fvars_1557_, v_e_1558_, v_a_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v_a_1559_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___boxed(lean_object* v_pre_1569_, lean_object* v_post_1570_, lean_object* v_usedLetOnly_1571_, lean_object* v_skipConstInApp_1572_, lean_object* v_skipInstances_1573_, lean_object* v_postApp_1574_, lean_object* v_fvars_1575_, lean_object* v_e_1576_, lean_object* v_a_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
uint8_t v_usedLetOnly_boxed_1583_; uint8_t v_skipConstInApp_boxed_1584_; uint8_t v_skipInstances_boxed_1585_; lean_object* v_res_1586_; 
v_usedLetOnly_boxed_1583_ = lean_unbox(v_usedLetOnly_1571_);
v_skipConstInApp_boxed_1584_ = lean_unbox(v_skipConstInApp_1572_);
v_skipInstances_boxed_1585_ = lean_unbox(v_skipInstances_1573_);
v_res_1586_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1569_, v_post_1570_, v_usedLetOnly_boxed_1583_, v_skipConstInApp_boxed_1584_, v_skipInstances_boxed_1585_, v_postApp_1574_, v_fvars_1575_, v_e_1576_, v_a_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v_a_1577_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___boxed(lean_object* v_upperBound_1587_, lean_object* v___x_1588_, lean_object* v_pre_1589_, lean_object* v_post_1590_, lean_object* v_usedLetOnly_1591_, lean_object* v_skipConstInApp_1592_, lean_object* v_skipInstances_1593_, lean_object* v_postApp_1594_, lean_object* v_a_1595_, lean_object* v_b_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
uint8_t v_usedLetOnly_boxed_1603_; uint8_t v_skipConstInApp_boxed_1604_; uint8_t v_skipInstances_boxed_1605_; lean_object* v_res_1606_; 
v_usedLetOnly_boxed_1603_ = lean_unbox(v_usedLetOnly_1591_);
v_skipConstInApp_boxed_1604_ = lean_unbox(v_skipConstInApp_1592_);
v_skipInstances_boxed_1605_ = lean_unbox(v_skipInstances_1593_);
v_res_1606_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_upperBound_1587_, v___x_1588_, v_pre_1589_, v_post_1590_, v_usedLetOnly_boxed_1603_, v_skipConstInApp_boxed_1604_, v_skipInstances_boxed_1605_, v_postApp_1594_, v_a_1595_, v_b_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___x_1588_);
lean_dec(v_upperBound_1587_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13___boxed(lean_object* v_skipInstances_1607_, lean_object* v_pre_1608_, lean_object* v_post_1609_, lean_object* v_usedLetOnly_1610_, lean_object* v_skipConstInApp_1611_, lean_object* v_postApp_1612_, lean_object* v___y_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_, lean_object* v_x_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
uint8_t v_skipInstances_boxed_1623_; uint8_t v_usedLetOnly_boxed_1624_; uint8_t v_skipConstInApp_boxed_1625_; lean_object* v_res_1626_; 
v_skipInstances_boxed_1623_ = lean_unbox(v_skipInstances_1607_);
v_usedLetOnly_boxed_1624_ = lean_unbox(v_usedLetOnly_1610_);
v_skipConstInApp_boxed_1625_ = lean_unbox(v_skipConstInApp_1611_);
v_res_1626_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_boxed_1623_, v_pre_1608_, v_post_1609_, v_usedLetOnly_boxed_1624_, v_skipConstInApp_boxed_1625_, v_postApp_1612_, v___y_1613_, v_x_1614_, v_x_1615_, v_x_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__1(lean_object* v_x_1627_, lean_object* v_e_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1634_, 0, v_e_1628_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__1___boxed(lean_object* v_x_1635_, lean_object* v_e_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__1(v_x_1635_, v_e_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec_ref(v_x_1635_);
return v_res_1642_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1644_ = lean_box(0);
v___x_1645_ = lean_unsigned_to_nat(16u);
v___x_1646_ = lean_mk_array(v___x_1645_, v___x_1644_);
return v___x_1646_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1647_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1);
v___x_1648_ = lean_unsigned_to_nat(0u);
v___x_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
lean_ctor_set(v___x_1649_, 1, v___x_1647_);
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2);
v___x_1651_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1651_, 0, lean_box(0));
lean_closure_set(v___x_1651_, 1, lean_box(0));
lean_closure_set(v___x_1651_, 2, v___x_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(lean_object* v_input_1652_, lean_object* v_pre_1653_, lean_object* v_post_1654_, uint8_t v_usedLetOnly_1655_, uint8_t v_skipConstInApp_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___f_1662_; uint8_t v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v_a_1666_; lean_object* v___x_1667_; 
v___f_1662_ = ((lean_object*)(l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0));
v___x_1663_ = 0;
v___x_1664_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__3, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__3_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__3);
v___x_1665_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1664_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref(v___x_1665_);
v___x_1667_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1653_, v_post_1654_, v_usedLetOnly_1655_, v_skipConstInApp_1656_, v___x_1663_, v___f_1662_, v_input_1652_, v_a_1666_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1667_, 1);
v___x_1669_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1669_, 0, lean_box(0));
lean_closure_set(v___x_1669_, 1, lean_box(0));
lean_closure_set(v___x_1669_, 2, v_a_1666_);
v___x_1670_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1669_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1677_ == 0)
{
lean_object* v_unused_1678_; 
v_unused_1678_ = lean_ctor_get(v___x_1670_, 0);
lean_dec(v_unused_1678_);
v___x_1672_ = v___x_1670_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_dec(v___x_1670_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v_a_1668_);
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1668_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
else
{
lean_dec(v_a_1666_);
return v___x_1667_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___boxed(lean_object* v_input_1679_, lean_object* v_pre_1680_, lean_object* v_post_1681_, lean_object* v_usedLetOnly_1682_, lean_object* v_skipConstInApp_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
uint8_t v_usedLetOnly_boxed_1689_; uint8_t v_skipConstInApp_boxed_1690_; lean_object* v_res_1691_; 
v_usedLetOnly_boxed_1689_ = lean_unbox(v_usedLetOnly_1682_);
v_skipConstInApp_boxed_1690_ = lean_unbox(v_skipConstInApp_1683_);
v_res_1691_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_input_1679_, v_pre_1680_, v_post_1681_, v_usedLetOnly_boxed_1689_, v_skipConstInApp_boxed_1690_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
return v_res_1691_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__1(void){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Array_instInhabited___redArg();
return v___x_1693_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__3(void){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__2));
v___x_1696_ = l_Lean_stringToMessageData(v___x_1695_);
return v___x_1696_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__5(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__4));
v___x_1699_ = l_Lean_stringToMessageData(v___x_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls(lean_object* v_fixedParamPerms_1700_, lean_object* v_argsPacker_1701_, lean_object* v_funNames_1702_, lean_object* v_newF_1703_, lean_object* v_e_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v___f_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___f_1710_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__0));
v___x_1711_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
lean_inc(v_a_1708_);
lean_inc_ref(v_a_1707_);
lean_inc(v_a_1706_);
lean_inc_ref(v_a_1705_);
lean_inc_ref(v_newF_1703_);
v___x_1712_ = lean_infer_type(v_newF_1703_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; uint8_t v___x_1724_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___x_1712_, 1);
v___x_1724_ = l_Lean_Expr_isForall(v_a_1713_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec_ref(v_e_1704_);
lean_dec_ref(v_funNames_1702_);
lean_dec_ref(v_argsPacker_1701_);
lean_dec_ref(v_fixedParamPerms_1700_);
v___x_1725_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__3, &l_Lean_Elab_WF_packCalls___closed__3_once, _init_l_Lean_Elab_WF_packCalls___closed__3);
v___x_1726_ = l_Lean_MessageData_ofExpr(v_newF_1703_);
v___x_1727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1725_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
v___x_1728_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__5, &l_Lean_Elab_WF_packCalls___closed__5_once, _init_l_Lean_Elab_WF_packCalls___closed__5);
v___x_1729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1727_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
v___x_1730_ = l_Lean_MessageData_ofExpr(v_a_1713_);
v___x_1731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1729_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v___x_1731_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_);
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1732_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1732_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
else
{
v___y_1715_ = v_a_1705_;
v___y_1716_ = v_a_1706_;
v___y_1717_ = v_a_1707_;
v___y_1718_ = v_a_1708_;
goto v___jp_1714_;
}
v___jp_1714_:
{
lean_object* v___x_1719_; lean_object* v___f_1720_; uint8_t v___x_1721_; uint8_t v___x_1722_; lean_object* v___x_1723_; 
v___x_1719_ = l_Lean_Expr_bindingDomain_x21(v_a_1713_);
lean_dec(v_a_1713_);
v___f_1720_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packCalls___lam__2___boxed), 12, 6);
lean_closure_set(v___f_1720_, 0, v_funNames_1702_);
lean_closure_set(v___f_1720_, 1, v_fixedParamPerms_1700_);
lean_closure_set(v___f_1720_, 2, v___x_1711_);
lean_closure_set(v___f_1720_, 3, v_argsPacker_1701_);
lean_closure_set(v___f_1720_, 4, v___x_1719_);
lean_closure_set(v___f_1720_, 5, v_newF_1703_);
v___x_1721_ = 0;
v___x_1722_ = 1;
v___x_1723_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_e_1704_, v___f_1710_, v___f_1720_, v___x_1721_, v___x_1722_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
return v___x_1723_;
}
}
else
{
lean_dec_ref(v_e_1704_);
lean_dec_ref(v_newF_1703_);
lean_dec_ref(v_funNames_1702_);
lean_dec_ref(v_argsPacker_1701_);
lean_dec_ref(v_fixedParamPerms_1700_);
return v___x_1712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___boxed(lean_object* v_fixedParamPerms_1741_, lean_object* v_argsPacker_1742_, lean_object* v_funNames_1743_, lean_object* v_newF_1744_, lean_object* v_e_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_1741_, v_argsPacker_1742_, v_funNames_1743_, v_newF_1744_, v_e_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
lean_dec(v_a_1749_);
lean_dec_ref(v_a_1748_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1752_, lean_object* v_m_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___redArg(v_m_1753_, v_a_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1756_, lean_object* v_m_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_00_u03b2_1756_, v_m_1757_, v_a_1758_);
lean_dec_ref(v_a_1758_);
lean_dec_ref(v_m_1757_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(lean_object* v_upperBound_1760_, lean_object* v___x_1761_, lean_object* v_pre_1762_, lean_object* v_post_1763_, uint8_t v_usedLetOnly_1764_, uint8_t v_skipConstInApp_1765_, uint8_t v_skipInstances_1766_, lean_object* v_postApp_1767_, lean_object* v___x_1768_, lean_object* v_inst_1769_, lean_object* v_R_1770_, lean_object* v_a_1771_, lean_object* v_b_1772_, lean_object* v_c_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_upperBound_1760_, v___x_1761_, v_pre_1762_, v_post_1763_, v_usedLetOnly_1764_, v_skipConstInApp_1765_, v_skipInstances_1766_, v_postApp_1767_, v_a_1771_, v_b_1772_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___boxed(lean_object** _args){
lean_object* v_upperBound_1781_ = _args[0];
lean_object* v___x_1782_ = _args[1];
lean_object* v_pre_1783_ = _args[2];
lean_object* v_post_1784_ = _args[3];
lean_object* v_usedLetOnly_1785_ = _args[4];
lean_object* v_skipConstInApp_1786_ = _args[5];
lean_object* v_skipInstances_1787_ = _args[6];
lean_object* v_postApp_1788_ = _args[7];
lean_object* v___x_1789_ = _args[8];
lean_object* v_inst_1790_ = _args[9];
lean_object* v_R_1791_ = _args[10];
lean_object* v_a_1792_ = _args[11];
lean_object* v_b_1793_ = _args[12];
lean_object* v_c_1794_ = _args[13];
lean_object* v___y_1795_ = _args[14];
lean_object* v___y_1796_ = _args[15];
lean_object* v___y_1797_ = _args[16];
lean_object* v___y_1798_ = _args[17];
lean_object* v___y_1799_ = _args[18];
lean_object* v___y_1800_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_1801_; uint8_t v_skipConstInApp_boxed_1802_; uint8_t v_skipInstances_boxed_1803_; lean_object* v_res_1804_; 
v_usedLetOnly_boxed_1801_ = lean_unbox(v_usedLetOnly_1785_);
v_skipConstInApp_boxed_1802_ = lean_unbox(v_skipConstInApp_1786_);
v_skipInstances_boxed_1803_ = lean_unbox(v_skipInstances_1787_);
v_res_1804_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(v_upperBound_1781_, v___x_1782_, v_pre_1783_, v_post_1784_, v_usedLetOnly_boxed_1801_, v_skipConstInApp_boxed_1802_, v_skipInstances_boxed_1803_, v_postApp_1788_, v___x_1789_, v_inst_1790_, v_R_1791_, v_a_1792_, v_b_1793_, v_c_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec(v___x_1789_);
lean_dec_ref(v___x_1782_);
lean_dec(v_upperBound_1781_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_1805_, lean_object* v_name_1806_, uint8_t v_bi_1807_, lean_object* v_type_1808_, lean_object* v_k_1809_, uint8_t v_kind_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_1806_, v_bi_1807_, v_type_1808_, v_k_1809_, v_kind_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_1818_, lean_object* v_name_1819_, lean_object* v_bi_1820_, lean_object* v_type_1821_, lean_object* v_k_1822_, lean_object* v_kind_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
uint8_t v_bi_boxed_1830_; uint8_t v_kind_boxed_1831_; lean_object* v_res_1832_; 
v_bi_boxed_1830_ = lean_unbox(v_bi_1820_);
v_kind_boxed_1831_ = lean_unbox(v_kind_1823_);
v_res_1832_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(v_00_u03b1_1818_, v_name_1819_, v_bi_boxed_1830_, v_type_1821_, v_k_1822_, v_kind_boxed_1831_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(lean_object* v_00_u03b1_1833_, lean_object* v_name_1834_, lean_object* v_type_1835_, lean_object* v_val_1836_, lean_object* v_k_1837_, uint8_t v_nondep_1838_, uint8_t v_kind_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_1834_, v_type_1835_, v_val_1836_, v_k_1837_, v_nondep_1838_, v_kind_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___boxed(lean_object* v_00_u03b1_1847_, lean_object* v_name_1848_, lean_object* v_type_1849_, lean_object* v_val_1850_, lean_object* v_k_1851_, lean_object* v_nondep_1852_, lean_object* v_kind_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
uint8_t v_nondep_boxed_1860_; uint8_t v_kind_boxed_1861_; lean_object* v_res_1862_; 
v_nondep_boxed_1860_ = lean_unbox(v_nondep_1852_);
v_kind_boxed_1861_ = lean_unbox(v_kind_1853_);
v_res_1862_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(v_00_u03b1_1847_, v_name_1848_, v_type_1849_, v_val_1850_, v_k_1851_, v_nondep_boxed_1860_, v_kind_boxed_1861_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(lean_object* v_00_u03b1_1863_, lean_object* v_ref_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_1864_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___boxed(lean_object* v_00_u03b1_1871_, lean_object* v_ref_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(v_00_u03b1_1871_, v_ref_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(lean_object* v_00_u03b1_1879_, lean_object* v_x_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___boxed(lean_object* v_00_u03b1_1888_, lean_object* v_x_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(v_00_u03b1_1888_, v_x_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15(lean_object* v_00_u03b2_1897_, lean_object* v_m_1898_, lean_object* v_a_1899_, lean_object* v_b_1900_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v_m_1898_, v_a_1899_, v_b_1900_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_1902_, lean_object* v_a_1903_, lean_object* v_x_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_spec__7___redArg(v_a_1903_, v_x_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b2_1906_, lean_object* v_a_1907_, lean_object* v_x_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6_spec__7(v_00_u03b2_1906_, v_a_1907_, v_x_1908_);
lean_dec(v_x_1908_);
lean_dec_ref(v_a_1907_);
return v_res_1909_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(lean_object* v_00_u03b2_1910_, lean_object* v_a_1911_, lean_object* v_x_1912_){
_start:
{
uint8_t v___x_1913_; 
v___x_1913_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_1911_, v_x_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___boxed(lean_object* v_00_u03b2_1914_, lean_object* v_a_1915_, lean_object* v_x_1916_){
_start:
{
uint8_t v_res_1917_; lean_object* v_r_1918_; 
v_res_1917_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(v_00_u03b2_1914_, v_a_1915_, v_x_1916_);
lean_dec(v_x_1916_);
lean_dec_ref(v_a_1915_);
v_r_1918_ = lean_box(v_res_1917_);
return v_r_1918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21(lean_object* v_00_u03b2_1919_, lean_object* v_data_1920_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_data_1920_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22(lean_object* v_00_u03b2_1922_, lean_object* v_a_1923_, lean_object* v_b_1924_, lean_object* v_x_1925_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_1923_, v_b_1924_, v_x_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22(lean_object* v_00_u03b2_1927_, lean_object* v_i_1928_, lean_object* v_source_1929_, lean_object* v_target_1930_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v_i_1928_, v_source_1929_, v_target_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23(lean_object* v_00_u03b2_1932_, lean_object* v_x_1933_, lean_object* v_x_1934_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(v_x_1933_, v_x_1934_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName(lean_object* v_fixedParamPerms_1942_, lean_object* v_argsPacker_1943_, lean_object* v_preDefs_1944_){
_start:
{
lean_object* v___x_1945_; uint8_t v___x_1960_; 
v___x_1945_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1960_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_1942_);
if (v___x_1960_ == 0)
{
goto v___jp_1946_;
}
else
{
uint8_t v___x_1961_; 
v___x_1961_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_1943_);
if (v___x_1961_ == 0)
{
goto v___jp_1946_;
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v_declName_1964_; 
v___x_1962_ = lean_unsigned_to_nat(0u);
v___x_1963_ = lean_array_get_borrowed(v___x_1945_, v_preDefs_1944_, v___x_1962_);
v_declName_1964_ = lean_ctor_get(v___x_1963_, 3);
lean_inc(v_declName_1964_);
return v_declName_1964_;
}
}
v___jp_1946_:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; 
v___x_1947_ = lean_unsigned_to_nat(1u);
v___x_1948_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_1943_);
v___x_1949_ = lean_nat_dec_lt(v___x_1947_, v___x_1948_);
lean_dec(v___x_1948_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v_declName_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1950_ = lean_unsigned_to_nat(0u);
v___x_1951_ = lean_array_get_borrowed(v___x_1945_, v_preDefs_1944_, v___x_1950_);
v_declName_1952_ = lean_ctor_get(v___x_1951_, 3);
v___x_1953_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__1));
lean_inc(v_declName_1952_);
v___x_1954_ = l_Lean_Name_append(v_declName_1952_, v___x_1953_);
return v___x_1954_;
}
else
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v_declName_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1955_ = lean_unsigned_to_nat(0u);
v___x_1956_ = lean_array_get_borrowed(v___x_1945_, v_preDefs_1944_, v___x_1955_);
v_declName_1957_ = lean_ctor_get(v___x_1956_, 3);
v___x_1958_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__3));
lean_inc(v_declName_1957_);
v___x_1959_ = l_Lean_Name_append(v_declName_1957_, v___x_1958_);
return v___x_1959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName___boxed(lean_object* v_fixedParamPerms_1965_, lean_object* v_argsPacker_1966_, lean_object* v_preDefs_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_1965_, v_argsPacker_1966_, v_preDefs_1967_);
lean_dec_ref(v_preDefs_1967_);
lean_dec_ref(v_argsPacker_1966_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(lean_object* v_k_1969_, lean_object* v_b_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v___x_1976_; 
lean_inc(v___y_1974_);
lean_inc_ref(v___y_1973_);
lean_inc(v___y_1972_);
lean_inc_ref(v___y_1971_);
v___x_1976_ = lean_apply_6(v_k_1969_, v_b_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, lean_box(0));
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed(lean_object* v_k_1977_, lean_object* v_b_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(v_k_1977_, v_b_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(lean_object* v_perm_1985_, lean_object* v_type_1986_, lean_object* v_k_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v___f_1993_; lean_object* v___x_1994_; 
v___f_1993_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1993_, 0, v_k_1987_);
v___x_1994_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_1985_, v_type_1986_, v___f_1993_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
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
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
v_a_2003_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1994_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_1994_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___boxed(lean_object* v_perm_2011_, lean_object* v_type_2012_, lean_object* v_k_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_2011_, v_type_2012_, v_k_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(lean_object* v_00_u03b1_2020_, lean_object* v_perm_2021_, lean_object* v_type_2022_, lean_object* v_k_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_2021_, v_type_2022_, v_k_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___boxed(lean_object* v_00_u03b1_2030_, lean_object* v_perm_2031_, lean_object* v_type_2032_, lean_object* v_k_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(v_00_u03b1_2030_, v_perm_2031_, v_type_2032_, v_k_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(lean_object* v___x_2040_, lean_object* v_ys_2041_, size_t v_sz_2042_, size_t v_i_2043_, lean_object* v_bs_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
uint8_t v___x_2050_; 
v___x_2050_ = lean_usize_dec_lt(v_i_2043_, v_sz_2042_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; 
lean_dec_ref(v_ys_2041_);
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v_bs_2044_);
return v___x_2051_;
}
else
{
lean_object* v_v_2052_; lean_object* v_value_2053_; lean_object* v___x_2054_; lean_object* v_bs_x27_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v_v_2052_ = lean_array_uget_borrowed(v_bs_2044_, v_i_2043_);
v_value_2053_ = lean_ctor_get(v_v_2052_, 7);
lean_inc_ref(v_value_2053_);
v___x_2054_ = lean_unsigned_to_nat(0u);
v_bs_x27_2055_ = lean_array_uset(v_bs_2044_, v_i_2043_, v___x_2054_);
v___x_2056_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2057_ = lean_usize_to_nat(v_i_2043_);
v___x_2058_ = lean_array_get_borrowed(v___x_2056_, v___x_2040_, v___x_2057_);
lean_dec(v___x_2057_);
lean_inc_ref(v_ys_2041_);
lean_inc(v___x_2058_);
v___x_2059_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_2058_, v_value_2053_, v_ys_2041_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; size_t v___x_2061_; size_t v___x_2062_; lean_object* v___x_2063_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
lean_inc(v_a_2060_);
lean_dec_ref_known(v___x_2059_, 1);
v___x_2061_ = ((size_t)1ULL);
v___x_2062_ = lean_usize_add(v_i_2043_, v___x_2061_);
v___x_2063_ = lean_array_uset(v_bs_x27_2055_, v_i_2043_, v_a_2060_);
v_i_2043_ = v___x_2062_;
v_bs_2044_ = v___x_2063_;
goto _start;
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec_ref(v_bs_x27_2055_);
lean_dec_ref(v_ys_2041_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg___boxed(lean_object* v___x_2073_, lean_object* v_ys_2074_, lean_object* v_sz_2075_, lean_object* v_i_2076_, lean_object* v_bs_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
size_t v_sz_boxed_2083_; size_t v_i_boxed_2084_; lean_object* v_res_2085_; 
v_sz_boxed_2083_ = lean_unbox_usize(v_sz_2075_);
lean_dec(v_sz_2075_);
v_i_boxed_2084_ = lean_unbox_usize(v_i_2076_);
lean_dec(v_i_2076_);
v_res_2085_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2073_, v_ys_2074_, v_sz_boxed_2083_, v_i_boxed_2084_, v_bs_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec_ref(v___x_2073_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(lean_object* v___x_2086_, lean_object* v_ys_2087_, size_t v_sz_2088_, size_t v_i_2089_, lean_object* v_bs_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
uint8_t v___x_2096_; 
v___x_2096_ = lean_usize_dec_lt(v_i_2089_, v_sz_2088_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; 
lean_dec_ref(v_ys_2087_);
v___x_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2097_, 0, v_bs_2090_);
return v___x_2097_;
}
else
{
lean_object* v_v_2098_; lean_object* v_type_2099_; lean_object* v___x_2100_; lean_object* v_bs_x27_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v_v_2098_ = lean_array_uget_borrowed(v_bs_2090_, v_i_2089_);
v_type_2099_ = lean_ctor_get(v_v_2098_, 6);
lean_inc_ref(v_type_2099_);
v___x_2100_ = lean_unsigned_to_nat(0u);
v_bs_x27_2101_ = lean_array_uset(v_bs_2090_, v_i_2089_, v___x_2100_);
v___x_2102_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2103_ = lean_usize_to_nat(v_i_2089_);
v___x_2104_ = lean_array_get_borrowed(v___x_2102_, v___x_2086_, v___x_2103_);
lean_dec(v___x_2103_);
lean_inc_ref(v_ys_2087_);
lean_inc(v___x_2104_);
v___x_2105_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_2104_, v_type_2099_, v_ys_2087_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; size_t v___x_2107_; size_t v___x_2108_; lean_object* v___x_2109_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2105_, 1);
v___x_2107_ = ((size_t)1ULL);
v___x_2108_ = lean_usize_add(v_i_2089_, v___x_2107_);
v___x_2109_ = lean_array_uset(v_bs_x27_2101_, v_i_2089_, v_a_2106_);
v_i_2089_ = v___x_2108_;
v_bs_2090_ = v___x_2109_;
goto _start;
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec_ref(v_bs_x27_2101_);
lean_dec_ref(v_ys_2087_);
v_a_2111_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2105_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2105_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg___boxed(lean_object* v___x_2119_, lean_object* v_ys_2120_, lean_object* v_sz_2121_, lean_object* v_i_2122_, lean_object* v_bs_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
size_t v_sz_boxed_2129_; size_t v_i_boxed_2130_; lean_object* v_res_2131_; 
v_sz_boxed_2129_ = lean_unbox_usize(v_sz_2121_);
lean_dec(v_sz_2121_);
v_i_boxed_2130_ = lean_unbox_usize(v_i_2122_);
lean_dec(v_i_2122_);
v_res_2131_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2119_, v_ys_2120_, v_sz_boxed_2129_, v_i_boxed_2130_, v_bs_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec_ref(v___x_2119_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
if (lean_obj_tag(v_a_2132_) == 0)
{
lean_object* v___x_2134_; 
v___x_2134_ = l_List_reverse___redArg(v_a_2133_);
return v___x_2134_;
}
else
{
lean_object* v_head_2135_; lean_object* v_tail_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2145_; 
v_head_2135_ = lean_ctor_get(v_a_2132_, 0);
v_tail_2136_ = lean_ctor_get(v_a_2132_, 1);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_a_2132_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2138_ = v_a_2132_;
v_isShared_2139_ = v_isSharedCheck_2145_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_tail_2136_);
lean_inc(v_head_2135_);
lean_dec(v_a_2132_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2145_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2140_ = l_Lean_mkLevelParam(v_head_2135_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 1, v_a_2133_);
lean_ctor_set(v___x_2138_, 0, v___x_2140_);
v___x_2142_ = v___x_2138_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2140_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_a_2133_);
v___x_2142_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
v_a_2132_ = v_tail_2136_;
v_a_2133_ = v___x_2142_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(size_t v_sz_2146_, size_t v_i_2147_, lean_object* v_bs_2148_){
_start:
{
uint8_t v___x_2149_; 
v___x_2149_ = lean_usize_dec_lt(v_i_2147_, v_sz_2146_);
if (v___x_2149_ == 0)
{
return v_bs_2148_;
}
else
{
lean_object* v_v_2150_; lean_object* v_declName_2151_; lean_object* v___x_2152_; lean_object* v_bs_x27_2153_; size_t v___x_2154_; size_t v___x_2155_; lean_object* v___x_2156_; 
v_v_2150_ = lean_array_uget_borrowed(v_bs_2148_, v_i_2147_);
v_declName_2151_ = lean_ctor_get(v_v_2150_, 3);
lean_inc(v_declName_2151_);
v___x_2152_ = lean_unsigned_to_nat(0u);
v_bs_x27_2153_ = lean_array_uset(v_bs_2148_, v_i_2147_, v___x_2152_);
v___x_2154_ = ((size_t)1ULL);
v___x_2155_ = lean_usize_add(v_i_2147_, v___x_2154_);
v___x_2156_ = lean_array_uset(v_bs_x27_2153_, v_i_2147_, v_declName_2151_);
v_i_2147_ = v___x_2155_;
v_bs_2148_ = v___x_2156_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3___boxed(lean_object* v_sz_2158_, lean_object* v_i_2159_, lean_object* v_bs_2160_){
_start:
{
size_t v_sz_boxed_2161_; size_t v_i_boxed_2162_; lean_object* v_res_2163_; 
v_sz_boxed_2161_ = lean_unbox_usize(v_sz_2158_);
lean_dec(v_sz_2158_);
v_i_boxed_2162_ = lean_unbox_usize(v_i_2159_);
lean_dec(v_i_2159_);
v_res_2163_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_boxed_2161_, v_i_boxed_2162_, v_bs_2160_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0(lean_object* v_preDefs_2164_, lean_object* v_perms_2165_, lean_object* v_argsPacker_2166_, uint8_t v___x_2167_, lean_object* v_ref_2168_, uint8_t v_kind_2169_, lean_object* v_levelParams_2170_, lean_object* v_modifiers_2171_, lean_object* v_newFn_2172_, lean_object* v_binders_2173_, lean_object* v_numSectionVars_2174_, lean_object* v_value_2175_, lean_object* v_termination_2176_, lean_object* v_fixedParamPerms_2177_, lean_object* v_ys_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
size_t v_sz_2184_; size_t v___x_2185_; lean_object* v___x_2186_; 
v_sz_2184_ = lean_array_size(v_preDefs_2164_);
v___x_2185_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_2164_);
lean_inc_ref(v_ys_2178_);
v___x_2186_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v_perms_2165_, v_ys_2178_, v_sz_2184_, v___x_2185_, v_preDefs_2164_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___x_2188_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2186_, 1);
lean_inc_ref(v_preDefs_2164_);
lean_inc_ref(v_ys_2178_);
v___x_2188_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v_perms_2165_, v_ys_2178_, v_sz_2184_, v___x_2185_, v_preDefs_2164_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2190_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
lean_dec_ref_known(v___x_2188_, 1);
v___x_2190_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_2166_, v_a_2187_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v_a_2187_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; uint8_t v___x_2192_; uint8_t v___x_2193_; lean_object* v___x_2194_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___x_2190_, 1);
v___x_2192_ = 1;
v___x_2193_ = 1;
v___x_2194_ = l_Lean_Meta_mkForallFVars(v_ys_2178_, v_a_2191_, v___x_2167_, v___x_2192_, v___x_2192_, v___x_2193_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc_n(v_a_2195_, 2);
lean_dec_ref_known(v___x_2194_, 1);
lean_inc_ref(v_termination_2176_);
lean_inc(v_numSectionVars_2174_);
lean_inc(v_binders_2173_);
lean_inc(v_newFn_2172_);
lean_inc_ref(v_modifiers_2171_);
lean_inc(v_levelParams_2170_);
lean_inc(v_ref_2168_);
v___x_2196_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2196_, 0, v_ref_2168_);
lean_ctor_set(v___x_2196_, 1, v_levelParams_2170_);
lean_ctor_set(v___x_2196_, 2, v_modifiers_2171_);
lean_ctor_set(v___x_2196_, 3, v_newFn_2172_);
lean_ctor_set(v___x_2196_, 4, v_binders_2173_);
lean_ctor_set(v___x_2196_, 5, v_numSectionVars_2174_);
lean_ctor_set(v___x_2196_, 6, v_a_2195_);
lean_ctor_set(v___x_2196_, 7, v_value_2175_);
lean_ctor_set(v___x_2196_, 8, v_termination_2176_);
lean_ctor_set_uint8(v___x_2196_, sizeof(void*)*9, v_kind_2169_);
v___x_2197_ = l_Lean_Elab_addAsAxiom___redArg(v___x_2196_, v___y_2181_, v___y_2182_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec_ref_known(v___x_2197_, 1);
v___x_2198_ = lean_box(0);
lean_inc(v_levelParams_2170_);
v___x_2199_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_2170_, v___x_2198_);
lean_inc(v_newFn_2172_);
v___x_2200_ = l_Lean_mkConst(v_newFn_2172_, v___x_2199_);
v___x_2201_ = l_Lean_mkAppN(v___x_2200_, v_ys_2178_);
v___x_2202_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_2166_, v_a_2189_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v_a_2189_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2202_, 1);
v___x_2204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_2184_, v___x_2185_, v_preDefs_2164_);
v___x_2205_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_2177_, v_argsPacker_2166_, v___x_2204_, v___x_2201_, v_a_2203_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2207_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2206_);
lean_dec_ref_known(v___x_2205_, 1);
v___x_2207_ = l_Lean_Meta_mkLambdaFVars(v_ys_2178_, v_a_2206_, v___x_2167_, v___x_2192_, v___x_2167_, v___x_2192_, v___x_2193_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec_ref(v_ys_2178_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2216_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2210_ = v___x_2207_;
v_isShared_2211_ = v_isSharedCheck_2216_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2207_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2216_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2212_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2212_, 0, v_ref_2168_);
lean_ctor_set(v___x_2212_, 1, v_levelParams_2170_);
lean_ctor_set(v___x_2212_, 2, v_modifiers_2171_);
lean_ctor_set(v___x_2212_, 3, v_newFn_2172_);
lean_ctor_set(v___x_2212_, 4, v_binders_2173_);
lean_ctor_set(v___x_2212_, 5, v_numSectionVars_2174_);
lean_ctor_set(v___x_2212_, 6, v_a_2195_);
lean_ctor_set(v___x_2212_, 7, v_a_2208_);
lean_ctor_set(v___x_2212_, 8, v_termination_2176_);
lean_ctor_set_uint8(v___x_2212_, sizeof(void*)*9, v_kind_2169_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v___x_2212_);
v___x_2214_ = v___x_2210_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec(v_a_2195_);
lean_dec_ref(v_termination_2176_);
lean_dec(v_numSectionVars_2174_);
lean_dec(v_binders_2173_);
lean_dec(v_newFn_2172_);
lean_dec_ref(v_modifiers_2171_);
lean_dec(v_levelParams_2170_);
lean_dec(v_ref_2168_);
v_a_2217_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2207_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2207_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec(v_a_2195_);
lean_dec_ref(v_ys_2178_);
lean_dec_ref(v_termination_2176_);
lean_dec(v_numSectionVars_2174_);
lean_dec(v_binders_2173_);
lean_dec(v_newFn_2172_);
lean_dec_ref(v_modifiers_2171_);
lean_dec(v_levelParams_2170_);
lean_dec(v_ref_2168_);
v_a_2225_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2205_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2205_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec_ref(v___x_2201_);
lean_dec(v_a_2195_);
lean_dec_ref(v_ys_2178_);
lean_dec_ref(v_fixedParamPerms_2177_);
lean_dec_ref(v_termination_2176_);
lean_dec(v_numSectionVars_2174_);
lean_dec(v_binders_2173_);
lean_dec(v_newFn_2172_);
lean_dec_ref(v_modifiers_2171_);
lean_dec(v_levelParams_2170_);
lean_dec(v_ref_2168_);
lean_dec_ref(v_argsPacker_2166_);
lean_dec_ref(v_preDefs_2164_);
v_a_2233_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2202_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2202_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec(v_a_2195_);
lean_dec(v_a_2189_);
lean_dec_ref(v_ys_2178_);
lean_dec_ref(v_fixedParamPerms_2177_);
lean_dec_ref(v_termination_2176_);
lean_dec(v_numSectionVars_2174_);
lean_dec(v_binders_2173_);
lean_dec(v_newFn_2172_);
lean_dec_ref(v_modifiers_2171_);
lean_dec(v_levelParams_2170_);
lean_dec(v_ref_2168_);
lean_dec_ref(v_argsPacker_2166_);
lean_dec_ref(v_preDefs_2164_);
v_a_2241_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2197_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2197_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_dec(v_a_2189_);
lean_dec_ref(v_ys_2178_);
lean_dec_ref(v_fixedParamPerms_2177_);
lean_dec_ref(v_termination_2176_);
lean_dec_ref(v_value_2175_);
lean_dec(v_numSectionVars_2174_);
lean_dec(v_binders_2173_);
lean_dec(v_newFn_2172_);
lean_dec_ref(v_modifiers_2171_);
lean_dec(v_levelParams_2170_);
lean_dec(v_ref_2168_);
lean_dec_ref(v_argsPacker_2166_);
lean_dec_ref(v_preDefs_2164_);
v_a_2249_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2194_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2194_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec(v_a_2189_);
lean_dec_ref(v_ys_2178_);
lean_dec_ref(v_fixedParamPerms_2177_);
lean_dec_ref(v_termination_2176_);
lean_dec_ref(v_value_2175_);
lean_dec(v_numSectionVars_2174_);
lean_dec(v_binders_2173_);
lean_dec(v_newFn_2172_);
lean_dec_ref(v_modifiers_2171_);
lean_dec(v_levelParams_2170_);
lean_dec(v_ref_2168_);
lean_dec_ref(v_argsPacker_2166_);
lean_dec_ref(v_preDefs_2164_);
v_a_2257_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2190_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2190_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec(v_a_2187_);
lean_dec_ref(v_ys_2178_);
lean_dec_ref(v_fixedParamPerms_2177_);
lean_dec_ref(v_termination_2176_);
lean_dec_ref(v_value_2175_);
lean_dec(v_numSectionVars_2174_);
lean_dec(v_binders_2173_);
lean_dec(v_newFn_2172_);
lean_dec_ref(v_modifiers_2171_);
lean_dec(v_levelParams_2170_);
lean_dec(v_ref_2168_);
lean_dec_ref(v_argsPacker_2166_);
lean_dec_ref(v_preDefs_2164_);
v_a_2265_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2188_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2188_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec_ref(v_ys_2178_);
lean_dec_ref(v_fixedParamPerms_2177_);
lean_dec_ref(v_termination_2176_);
lean_dec_ref(v_value_2175_);
lean_dec(v_numSectionVars_2174_);
lean_dec(v_binders_2173_);
lean_dec(v_newFn_2172_);
lean_dec_ref(v_modifiers_2171_);
lean_dec(v_levelParams_2170_);
lean_dec(v_ref_2168_);
lean_dec_ref(v_argsPacker_2166_);
lean_dec_ref(v_preDefs_2164_);
v_a_2273_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2186_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2186_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0___boxed(lean_object** _args){
lean_object* v_preDefs_2281_ = _args[0];
lean_object* v_perms_2282_ = _args[1];
lean_object* v_argsPacker_2283_ = _args[2];
lean_object* v___x_2284_ = _args[3];
lean_object* v_ref_2285_ = _args[4];
lean_object* v_kind_2286_ = _args[5];
lean_object* v_levelParams_2287_ = _args[6];
lean_object* v_modifiers_2288_ = _args[7];
lean_object* v_newFn_2289_ = _args[8];
lean_object* v_binders_2290_ = _args[9];
lean_object* v_numSectionVars_2291_ = _args[10];
lean_object* v_value_2292_ = _args[11];
lean_object* v_termination_2293_ = _args[12];
lean_object* v_fixedParamPerms_2294_ = _args[13];
lean_object* v_ys_2295_ = _args[14];
lean_object* v___y_2296_ = _args[15];
lean_object* v___y_2297_ = _args[16];
lean_object* v___y_2298_ = _args[17];
lean_object* v___y_2299_ = _args[18];
lean_object* v___y_2300_ = _args[19];
_start:
{
uint8_t v___x_2509__boxed_2301_; uint8_t v_kind_boxed_2302_; lean_object* v_res_2303_; 
v___x_2509__boxed_2301_ = lean_unbox(v___x_2284_);
v_kind_boxed_2302_ = lean_unbox(v_kind_2286_);
v_res_2303_ = l_Lean_Elab_WF_packMutual___lam__0(v_preDefs_2281_, v_perms_2282_, v_argsPacker_2283_, v___x_2509__boxed_2301_, v_ref_2285_, v_kind_boxed_2302_, v_levelParams_2287_, v_modifiers_2288_, v_newFn_2289_, v_binders_2290_, v_numSectionVars_2291_, v_value_2292_, v_termination_2293_, v_fixedParamPerms_2294_, v_ys_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec_ref(v_perms_2282_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual(lean_object* v_fixedParamPerms_2304_, lean_object* v_argsPacker_2305_, lean_object* v_preDefs_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v_ref_2315_; uint8_t v_kind_2316_; lean_object* v_levelParams_2317_; lean_object* v_modifiers_2318_; lean_object* v_declName_2319_; lean_object* v_binders_2320_; lean_object* v_numSectionVars_2321_; lean_object* v_type_2322_; lean_object* v_value_2323_; lean_object* v_termination_2324_; lean_object* v_newFn_2325_; uint8_t v___x_2326_; 
v___x_2312_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_2313_ = lean_unsigned_to_nat(0u);
v___x_2314_ = lean_array_get_borrowed(v___x_2312_, v_preDefs_2306_, v___x_2313_);
v_ref_2315_ = lean_ctor_get(v___x_2314_, 0);
v_kind_2316_ = lean_ctor_get_uint8(v___x_2314_, sizeof(void*)*9);
v_levelParams_2317_ = lean_ctor_get(v___x_2314_, 1);
v_modifiers_2318_ = lean_ctor_get(v___x_2314_, 2);
v_declName_2319_ = lean_ctor_get(v___x_2314_, 3);
v_binders_2320_ = lean_ctor_get(v___x_2314_, 4);
v_numSectionVars_2321_ = lean_ctor_get(v___x_2314_, 5);
v_type_2322_ = lean_ctor_get(v___x_2314_, 6);
v_value_2323_ = lean_ctor_get(v___x_2314_, 7);
v_termination_2324_ = lean_ctor_get(v___x_2314_, 8);
lean_inc_ref(v_fixedParamPerms_2304_);
v_newFn_2325_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_2304_, v_argsPacker_2305_, v_preDefs_2306_);
v___x_2326_ = lean_name_eq(v_newFn_2325_, v_declName_2319_);
if (v___x_2326_ == 0)
{
lean_object* v_perms_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___f_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
lean_inc_ref(v_termination_2324_);
lean_inc_ref(v_value_2323_);
lean_inc_ref(v_type_2322_);
lean_inc(v_numSectionVars_2321_);
lean_inc(v_binders_2320_);
lean_inc_ref(v_modifiers_2318_);
lean_inc(v_levelParams_2317_);
lean_inc(v_ref_2315_);
v_perms_2327_ = lean_ctor_get(v_fixedParamPerms_2304_, 1);
lean_inc_ref_n(v_perms_2327_, 2);
v___x_2328_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2329_ = lean_box(v___x_2326_);
v___x_2330_ = lean_box(v_kind_2316_);
v___f_2331_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packMutual___lam__0___boxed), 20, 14);
lean_closure_set(v___f_2331_, 0, v_preDefs_2306_);
lean_closure_set(v___f_2331_, 1, v_perms_2327_);
lean_closure_set(v___f_2331_, 2, v_argsPacker_2305_);
lean_closure_set(v___f_2331_, 3, v___x_2329_);
lean_closure_set(v___f_2331_, 4, v_ref_2315_);
lean_closure_set(v___f_2331_, 5, v___x_2330_);
lean_closure_set(v___f_2331_, 6, v_levelParams_2317_);
lean_closure_set(v___f_2331_, 7, v_modifiers_2318_);
lean_closure_set(v___f_2331_, 8, v_newFn_2325_);
lean_closure_set(v___f_2331_, 9, v_binders_2320_);
lean_closure_set(v___f_2331_, 10, v_numSectionVars_2321_);
lean_closure_set(v___f_2331_, 11, v_value_2323_);
lean_closure_set(v___f_2331_, 12, v_termination_2324_);
lean_closure_set(v___f_2331_, 13, v_fixedParamPerms_2304_);
v___x_2332_ = lean_array_get(v___x_2328_, v_perms_2327_, v___x_2313_);
lean_dec_ref(v_perms_2327_);
v___x_2333_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v___x_2332_, v_type_2322_, v___f_2331_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_);
return v___x_2333_;
}
else
{
lean_object* v___x_2334_; 
lean_inc(v___x_2314_);
lean_dec(v_newFn_2325_);
lean_dec_ref(v_preDefs_2306_);
lean_dec_ref(v_argsPacker_2305_);
lean_dec_ref(v_fixedParamPerms_2304_);
v___x_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2314_);
return v___x_2334_;
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(lean_object* v___x_2344_, lean_object* v_ys_2345_, lean_object* v_as_2346_, size_t v_sz_2347_, size_t v_i_2348_, lean_object* v_bs_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2344_, v_ys_2345_, v_sz_2347_, v_i_2348_, v_bs_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___boxed(lean_object* v___x_2356_, lean_object* v_ys_2357_, lean_object* v_as_2358_, lean_object* v_sz_2359_, lean_object* v_i_2360_, lean_object* v_bs_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
size_t v_sz_boxed_2367_; size_t v_i_boxed_2368_; lean_object* v_res_2369_; 
v_sz_boxed_2367_ = lean_unbox_usize(v_sz_2359_);
lean_dec(v_sz_2359_);
v_i_boxed_2368_ = lean_unbox_usize(v_i_2360_);
lean_dec(v_i_2360_);
v_res_2369_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(v___x_2356_, v_ys_2357_, v_as_2358_, v_sz_boxed_2367_, v_i_boxed_2368_, v_bs_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec_ref(v_as_2358_);
lean_dec_ref(v___x_2356_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(lean_object* v___x_2370_, lean_object* v_ys_2371_, lean_object* v_as_2372_, size_t v_sz_2373_, size_t v_i_2374_, lean_object* v_bs_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2370_, v_ys_2371_, v_sz_2373_, v_i_2374_, v_bs_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___boxed(lean_object* v___x_2382_, lean_object* v_ys_2383_, lean_object* v_as_2384_, lean_object* v_sz_2385_, lean_object* v_i_2386_, lean_object* v_bs_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
size_t v_sz_boxed_2393_; size_t v_i_boxed_2394_; lean_object* v_res_2395_; 
v_sz_boxed_2393_ = lean_unbox_usize(v_sz_2385_);
lean_dec(v_sz_2385_);
v_i_boxed_2394_ = lean_unbox_usize(v_i_2386_);
lean_dec(v_i_2386_);
v_res_2395_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(v___x_2382_, v_ys_2383_, v_as_2384_, v_sz_boxed_2393_, v_i_boxed_2394_, v_bs_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec_ref(v_as_2384_);
lean_dec_ref(v___x_2382_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(lean_object* v_e_2396_, lean_object* v_k_2397_, uint8_t v_cleanupAnnotations_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v___f_2404_; uint8_t v___x_2405_; uint8_t v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___f_2404_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2404_, 0, v_k_2397_);
v___x_2405_ = 1;
v___x_2406_ = 0;
v___x_2407_ = lean_box(0);
v___x_2408_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2396_, v___x_2405_, v___x_2406_, v___x_2405_, v___x_2406_, v___x_2407_, v___f_2404_, v_cleanupAnnotations_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2408_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2408_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
v_a_2417_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2408_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2408_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg___boxed(lean_object* v_e_2425_, lean_object* v_k_2426_, lean_object* v_cleanupAnnotations_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2433_; lean_object* v_res_2434_; 
v_cleanupAnnotations_boxed_2433_ = lean_unbox(v_cleanupAnnotations_2427_);
v_res_2434_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2425_, v_k_2426_, v_cleanupAnnotations_boxed_2433_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(lean_object* v_00_u03b1_2435_, lean_object* v_e_2436_, lean_object* v_k_2437_, uint8_t v_cleanupAnnotations_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2436_, v_k_2437_, v_cleanupAnnotations_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___boxed(lean_object* v_00_u03b1_2445_, lean_object* v_e_2446_, lean_object* v_k_2447_, lean_object* v_cleanupAnnotations_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2454_; lean_object* v_res_2455_; 
v_cleanupAnnotations_boxed_2454_ = lean_unbox(v_cleanupAnnotations_2448_);
v_res_2455_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(v_00_u03b1_2445_, v_e_2446_, v_k_2447_, v_cleanupAnnotations_boxed_2454_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(lean_object* v_msg_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v___f_2462_; lean_object* v___x_1649__overap_2463_; lean_object* v___x_2464_; 
v___f_2462_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1649__overap_2463_ = lean_panic_fn_borrowed(v___f_2462_, v_msg_2456_);
lean_inc(v___y_2460_);
lean_inc_ref(v___y_2459_);
lean_inc(v___y_2458_);
lean_inc_ref(v___y_2457_);
v___x_2464_ = lean_apply_5(v___x_1649__overap_2463_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, lean_box(0));
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1___boxed(lean_object* v_msg_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v_msg_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0(lean_object* v_xs_2472_, lean_object* v_x_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = lean_array_get_size(v_xs_2472_);
v___x_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0___boxed(lean_object* v_xs_2481_, lean_object* v_x_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_Elab_WF_varyingVarNames___lam__0(v_xs_2481_, v_x_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec_ref(v_x_2482_);
lean_dec_ref(v_xs_2481_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(lean_object* v_as_2489_, size_t v_sz_2490_, size_t v_i_2491_, lean_object* v_b_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v_a_2498_; uint8_t v___x_2502_; 
v___x_2502_ = lean_usize_dec_lt(v_i_2491_, v_sz_2490_);
if (v___x_2502_ == 0)
{
lean_object* v___x_2503_; 
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v_b_2492_);
return v___x_2503_;
}
else
{
lean_object* v_snd_2504_; lean_object* v_fst_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2549_; 
v_snd_2504_ = lean_ctor_get(v_b_2492_, 1);
v_fst_2505_ = lean_ctor_get(v_b_2492_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_b_2492_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2507_ = v_b_2492_;
v_isShared_2508_ = v_isSharedCheck_2549_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_snd_2504_);
lean_inc(v_fst_2505_);
lean_dec(v_b_2492_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2549_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v_array_2509_; lean_object* v_start_2510_; lean_object* v_stop_2511_; uint8_t v___x_2512_; 
v_array_2509_ = lean_ctor_get(v_snd_2504_, 0);
v_start_2510_ = lean_ctor_get(v_snd_2504_, 1);
v_stop_2511_ = lean_ctor_get(v_snd_2504_, 2);
v___x_2512_ = lean_nat_dec_lt(v_start_2510_, v_stop_2511_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2514_; 
if (v_isShared_2508_ == 0)
{
v___x_2514_ = v___x_2507_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_fst_2505_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v_snd_2504_);
v___x_2514_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2515_; 
v___x_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
return v___x_2515_;
}
}
else
{
lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2545_; 
lean_inc(v_stop_2511_);
lean_inc(v_start_2510_);
lean_inc_ref(v_array_2509_);
v_isSharedCheck_2545_ = !lean_is_exclusive(v_snd_2504_);
if (v_isSharedCheck_2545_ == 0)
{
lean_object* v_unused_2546_; lean_object* v_unused_2547_; lean_object* v_unused_2548_; 
v_unused_2546_ = lean_ctor_get(v_snd_2504_, 2);
lean_dec(v_unused_2546_);
v_unused_2547_ = lean_ctor_get(v_snd_2504_, 1);
lean_dec(v_unused_2547_);
v_unused_2548_ = lean_ctor_get(v_snd_2504_, 0);
lean_dec(v_unused_2548_);
v___x_2518_ = v_snd_2504_;
v_isShared_2519_ = v_isSharedCheck_2545_;
goto v_resetjp_2517_;
}
else
{
lean_dec(v_snd_2504_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2545_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2520_ = lean_array_fget(v_array_2509_, v_start_2510_);
v___x_2521_ = lean_unsigned_to_nat(1u);
v___x_2522_ = lean_nat_add(v_start_2510_, v___x_2521_);
lean_dec(v_start_2510_);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 1, v___x_2522_);
v___x_2524_ = v___x_2518_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_array_2509_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2544_, 2, v_stop_2511_);
v___x_2524_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v_a_2525_ = lean_array_uget_borrowed(v_as_2489_, v_i_2491_);
v___x_2526_ = l_Lean_Expr_fvarId_x21(v_a_2525_);
v___x_2527_ = l_Lean_FVarId_getUserName___redArg(v___x_2526_, v___y_2493_, v___y_2494_, v___y_2495_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v___x_2529_; lean_object* v___x_2531_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2528_);
lean_dec_ref_known(v___x_2527_, 1);
v___x_2529_ = lean_array_push(v_fst_2505_, v_a_2528_);
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 1, v___x_2524_);
lean_ctor_set(v___x_2507_, 0, v___x_2529_);
v___x_2531_ = v___x_2507_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v___x_2524_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
v_a_2498_ = v___x_2531_;
goto v___jp_2497_;
}
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec_ref(v___x_2524_);
lean_del_object(v___x_2507_);
lean_dec(v_fst_2505_);
v_a_2533_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2527_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2527_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
else
{
lean_object* v___x_2542_; 
lean_dec_ref_known(v___x_2520_, 1);
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 1, v___x_2524_);
v___x_2542_ = v___x_2507_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_fst_2505_);
lean_ctor_set(v_reuseFailAlloc_2543_, 1, v___x_2524_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
v_a_2498_ = v___x_2542_;
goto v___jp_2497_;
}
}
}
}
}
}
}
v___jp_2497_:
{
size_t v___x_2499_; size_t v___x_2500_; 
v___x_2499_ = ((size_t)1ULL);
v___x_2500_ = lean_usize_add(v_i_2491_, v___x_2499_);
v_i_2491_ = v___x_2500_;
v_b_2492_ = v_a_2498_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg___boxed(lean_object* v_as_2550_, lean_object* v_sz_2551_, lean_object* v_i_2552_, lean_object* v_b_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
size_t v_sz_boxed_2558_; size_t v_i_boxed_2559_; lean_object* v_res_2560_; 
v_sz_boxed_2558_ = lean_unbox_usize(v_sz_2551_);
lean_dec(v_sz_2551_);
v_i_boxed_2559_ = lean_unbox_usize(v_i_2552_);
lean_dec(v_i_2552_);
v_res_2560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2550_, v_sz_boxed_2558_, v_i_boxed_2559_, v_b_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec_ref(v_as_2550_);
return v_res_2560_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2563_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1));
v___x_2564_ = lean_unsigned_to_nat(4u);
v___x_2565_ = lean_unsigned_to_nat(119u);
v___x_2566_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2567_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2568_ = l_mkPanicMessageWithDecl(v___x_2567_, v___x_2566_, v___x_2565_, v___x_2564_, v___x_2563_);
return v___x_2568_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2570_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3));
v___x_2571_ = lean_unsigned_to_nat(4u);
v___x_2572_ = lean_unsigned_to_nat(120u);
v___x_2573_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2574_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2575_ = l_mkPanicMessageWithDecl(v___x_2574_, v___x_2573_, v___x_2572_, v___x_2571_, v___x_2570_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1(lean_object* v_a_2578_, lean_object* v_fixedParamPerms_2579_, lean_object* v___x_2580_, lean_object* v_preDefIdx_2581_, lean_object* v_xs_2582_, lean_object* v_x_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v___x_2589_; uint8_t v___x_2590_; 
v___x_2589_ = lean_array_get_size(v_xs_2582_);
v___x_2590_ = lean_nat_dec_eq(v___x_2589_, v_a_2578_);
if (v___x_2590_ == 0)
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2);
v___x_2592_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2591_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
return v___x_2592_;
}
else
{
lean_object* v_perms_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; uint8_t v___x_2596_; 
v_perms_2593_ = lean_ctor_get(v_fixedParamPerms_2579_, 1);
v___x_2594_ = lean_array_get_borrowed(v___x_2580_, v_perms_2593_, v_preDefIdx_2581_);
v___x_2595_ = lean_array_get_size(v___x_2594_);
v___x_2596_ = lean_nat_dec_eq(v___x_2595_, v_a_2578_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2597_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4);
v___x_2598_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2597_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
return v___x_2598_;
}
else
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; size_t v_sz_2603_; size_t v___x_2604_; lean_object* v___x_2605_; 
v___x_2599_ = lean_unsigned_to_nat(0u);
v___x_2600_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5));
lean_inc(v___x_2594_);
v___x_2601_ = l_Array_toSubarray___redArg(v___x_2594_, v___x_2599_, v___x_2595_);
v___x_2602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2600_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v_sz_2603_ = lean_array_size(v_xs_2582_);
v___x_2604_ = ((size_t)0ULL);
v___x_2605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_xs_2582_, v_sz_2603_, v___x_2604_, v___x_2602_, v___y_2584_, v___y_2586_, v___y_2587_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2614_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2608_ = v___x_2605_;
v_isShared_2609_ = v_isSharedCheck_2614_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2605_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2614_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v_fst_2610_; lean_object* v___x_2612_; 
v_fst_2610_ = lean_ctor_get(v_a_2606_, 0);
lean_inc(v_fst_2610_);
lean_dec(v_a_2606_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v_fst_2610_);
v___x_2612_ = v___x_2608_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_fst_2610_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
v_a_2615_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2605_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2605_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___boxed(lean_object* v_a_2623_, lean_object* v_fixedParamPerms_2624_, lean_object* v___x_2625_, lean_object* v_preDefIdx_2626_, lean_object* v_xs_2627_, lean_object* v_x_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_Lean_Elab_WF_varyingVarNames___lam__1(v_a_2623_, v_fixedParamPerms_2624_, v___x_2625_, v_preDefIdx_2626_, v_xs_2627_, v_x_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec_ref(v_x_2628_);
lean_dec_ref(v_xs_2627_);
lean_dec(v_preDefIdx_2626_);
lean_dec_ref(v___x_2625_);
lean_dec_ref(v_fixedParamPerms_2624_);
lean_dec(v_a_2623_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object* v_fixedParamPerms_2636_, lean_object* v_preDefIdx_2637_, lean_object* v_preDef_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v_type_2644_; lean_object* v_value_2645_; lean_object* v___f_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; lean_object* v___x_2649_; 
v_type_2644_ = lean_ctor_get(v_preDef_2638_, 6);
lean_inc_ref(v_type_2644_);
v_value_2645_ = lean_ctor_get(v_preDef_2638_, 7);
lean_inc_ref(v_value_2645_);
lean_dec_ref(v_preDef_2638_);
v___f_2646_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___closed__0));
v___x_2647_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2648_ = 0;
v___x_2649_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_value_2645_, v___f_2646_, v___x_2648_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___f_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc_n(v_a_2650_, 2);
lean_dec_ref_known(v___x_2649_, 1);
v___f_2651_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_varyingVarNames___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2651_, 0, v_a_2650_);
lean_closure_set(v___f_2651_, 1, v_fixedParamPerms_2636_);
lean_closure_set(v___f_2651_, 2, v___x_2647_);
lean_closure_set(v___f_2651_, 3, v_preDefIdx_2637_);
v___x_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2652_, 0, v_a_2650_);
v___x_2653_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2644_, v___x_2652_, v___f_2651_, v___x_2648_, v___x_2648_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_);
return v___x_2653_;
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec_ref(v_type_2644_);
lean_dec(v_preDefIdx_2637_);
lean_dec_ref(v_fixedParamPerms_2636_);
v_a_2654_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2649_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2649_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___boxed(lean_object* v_fixedParamPerms_2662_, lean_object* v_preDefIdx_2663_, lean_object* v_preDef_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lean_Elab_WF_varyingVarNames(v_fixedParamPerms_2662_, v_preDefIdx_2663_, v_preDef_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(lean_object* v_as_2671_, size_t v_sz_2672_, size_t v_i_2673_, lean_object* v_b_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2671_, v_sz_2672_, v_i_2673_, v_b_2674_, v___y_2675_, v___y_2677_, v___y_2678_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___boxed(lean_object* v_as_2681_, lean_object* v_sz_2682_, lean_object* v_i_2683_, lean_object* v_b_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
size_t v_sz_boxed_2690_; size_t v_i_boxed_2691_; lean_object* v_res_2692_; 
v_sz_boxed_2690_ = lean_unbox_usize(v_sz_2682_);
lean_dec(v_sz_2682_);
v_i_boxed_2691_ = lean_unbox_usize(v_i_2683_);
lean_dec(v_i_2683_);
v_res_2692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(v_as_2681_, v_sz_boxed_2690_, v_i_boxed_2691_, v_b_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec_ref(v_as_2681_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(lean_object* v_msg_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v___f_2699_; lean_object* v___x_1608__overap_2700_; lean_object* v___x_2701_; 
v___f_2699_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1608__overap_2700_ = lean_panic_fn_borrowed(v___f_2699_, v_msg_2693_);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc_ref(v___y_2694_);
v___x_2701_ = lean_apply_5(v___x_1608__overap_2700_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, lean_box(0));
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0___boxed(lean_object* v_msg_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v_msg_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
return v_res_2708_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2709_; double v___x_2710_; 
v___x_2709_ = lean_unsigned_to_nat(0u);
v___x_2710_ = lean_float_of_nat(v___x_2709_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(lean_object* v_cls_2714_, lean_object* v_msg_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v_ref_2721_; lean_object* v___x_2722_; lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2768_; 
v_ref_2721_ = lean_ctor_get(v___y_2718_, 2);
v___x_2722_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msg_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2725_ = v___x_2722_;
v_isShared_2726_ = v_isSharedCheck_2768_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2722_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2768_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2727_; lean_object* v_traceState_2728_; lean_object* v_env_2729_; lean_object* v_nextMacroScope_2730_; lean_object* v_ngen_2731_; lean_object* v_auxDeclNGen_2732_; lean_object* v_cache_2733_; lean_object* v_recordedDeps_2734_; lean_object* v_messages_2735_; lean_object* v_infoState_2736_; lean_object* v_snapshotTasks_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2767_; 
v___x_2727_ = lean_st_ref_take(v___y_2719_);
v_traceState_2728_ = lean_ctor_get(v___x_2727_, 4);
v_env_2729_ = lean_ctor_get(v___x_2727_, 0);
v_nextMacroScope_2730_ = lean_ctor_get(v___x_2727_, 1);
v_ngen_2731_ = lean_ctor_get(v___x_2727_, 2);
v_auxDeclNGen_2732_ = lean_ctor_get(v___x_2727_, 3);
v_cache_2733_ = lean_ctor_get(v___x_2727_, 5);
v_recordedDeps_2734_ = lean_ctor_get(v___x_2727_, 6);
v_messages_2735_ = lean_ctor_get(v___x_2727_, 7);
v_infoState_2736_ = lean_ctor_get(v___x_2727_, 8);
v_snapshotTasks_2737_ = lean_ctor_get(v___x_2727_, 9);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2739_ = v___x_2727_;
v_isShared_2740_ = v_isSharedCheck_2767_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_snapshotTasks_2737_);
lean_inc(v_infoState_2736_);
lean_inc(v_messages_2735_);
lean_inc(v_recordedDeps_2734_);
lean_inc(v_cache_2733_);
lean_inc(v_traceState_2728_);
lean_inc(v_auxDeclNGen_2732_);
lean_inc(v_ngen_2731_);
lean_inc(v_nextMacroScope_2730_);
lean_inc(v_env_2729_);
lean_dec(v___x_2727_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2767_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
uint64_t v_tid_2741_; lean_object* v_traces_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2766_; 
v_tid_2741_ = lean_ctor_get_uint64(v_traceState_2728_, sizeof(void*)*1);
v_traces_2742_ = lean_ctor_get(v_traceState_2728_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v_traceState_2728_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2744_ = v_traceState_2728_;
v_isShared_2745_ = v_isSharedCheck_2766_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_traces_2742_);
lean_dec(v_traceState_2728_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2766_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; double v___x_2748_; uint8_t v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2757_; 
v___x_2746_ = lean_box(0);
v___x_2747_ = lean_box(0);
v___x_2748_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0);
v___x_2749_ = 0;
v___x_2750_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1));
v___x_2751_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2751_, 0, v_cls_2714_);
lean_ctor_set(v___x_2751_, 1, v___x_2747_);
lean_ctor_set(v___x_2751_, 2, v___x_2750_);
lean_ctor_set_float(v___x_2751_, sizeof(void*)*3, v___x_2748_);
lean_ctor_set_float(v___x_2751_, sizeof(void*)*3 + 8, v___x_2748_);
lean_ctor_set_uint8(v___x_2751_, sizeof(void*)*3 + 16, v___x_2749_);
v___x_2752_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2));
v___x_2753_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2751_);
lean_ctor_set(v___x_2753_, 1, v_a_2723_);
lean_ctor_set(v___x_2753_, 2, v___x_2752_);
lean_inc(v_ref_2721_);
v___x_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2754_, 0, v_ref_2721_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = l_Lean_PersistentArray_push___redArg(v_traces_2742_, v___x_2754_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 0, v___x_2755_);
v___x_2757_ = v___x_2744_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2755_);
lean_ctor_set_uint64(v_reuseFailAlloc_2765_, sizeof(void*)*1, v_tid_2741_);
v___x_2757_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
lean_object* v___x_2759_; 
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 4, v___x_2757_);
v___x_2759_ = v___x_2739_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_env_2729_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v_nextMacroScope_2730_);
lean_ctor_set(v_reuseFailAlloc_2764_, 2, v_ngen_2731_);
lean_ctor_set(v_reuseFailAlloc_2764_, 3, v_auxDeclNGen_2732_);
lean_ctor_set(v_reuseFailAlloc_2764_, 4, v___x_2757_);
lean_ctor_set(v_reuseFailAlloc_2764_, 5, v_cache_2733_);
lean_ctor_set(v_reuseFailAlloc_2764_, 6, v_recordedDeps_2734_);
lean_ctor_set(v_reuseFailAlloc_2764_, 7, v_messages_2735_);
lean_ctor_set(v_reuseFailAlloc_2764_, 8, v_infoState_2736_);
lean_ctor_set(v_reuseFailAlloc_2764_, 9, v_snapshotTasks_2737_);
v___x_2759_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
lean_object* v___x_2760_; lean_object* v___x_2762_; 
v___x_2760_ = lean_st_ref_put(v___y_2719_, v___x_2759_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 0, v___x_2746_);
v___x_2762_ = v___x_2725_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2746_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___boxed(lean_object* v_cls_2769_, lean_object* v_msg_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v_cls_2769_, v_msg_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
return v_res_2776_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2779_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1));
v___x_2780_ = lean_unsigned_to_nat(8u);
v___x_2781_ = lean_unsigned_to_nat(135u);
v___x_2782_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0));
v___x_2783_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2784_ = l_mkPanicMessageWithDecl(v___x_2783_, v___x_2782_, v___x_2781_, v___x_2780_, v___x_2779_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(lean_object* v___x_2785_, lean_object* v_unaryPreDefNonRec_2786_, lean_object* v___x_2787_, lean_object* v_us_2788_, lean_object* v_argsPacker_2789_, lean_object* v___x_2790_, lean_object* v_params_2791_, lean_object* v_x_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v___x_2798_; uint8_t v___x_2799_; 
v___x_2798_ = lean_array_get_size(v_params_2791_);
v___x_2799_ = lean_nat_dec_eq(v___x_2785_, v___x_2798_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
lean_dec(v___x_2790_);
lean_dec(v_us_2788_);
lean_dec_ref(v_unaryPreDefNonRec_2786_);
v___x_2800_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2);
v___x_2801_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v___x_2800_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
return v___x_2801_;
}
else
{
lean_object* v_declName_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_declName_2802_ = lean_ctor_get(v_unaryPreDefNonRec_2786_, 3);
lean_inc(v_declName_2802_);
lean_dec_ref(v_unaryPreDefNonRec_2786_);
v___x_2803_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v___x_2787_, v_params_2791_);
v___x_2804_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_2787_, v_params_2791_);
v___x_2805_ = l_Lean_mkConst(v_declName_2802_, v_us_2788_);
v___x_2806_ = l_Lean_mkAppN(v___x_2805_, v___x_2803_);
lean_dec_ref(v___x_2803_);
v___x_2807_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_2789_, v___x_2806_, v___x_2790_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; uint8_t v___x_2811_; lean_object* v___x_2812_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = l_Lean_Expr_beta(v_a_2808_, v___x_2804_);
v___x_2810_ = 0;
v___x_2811_ = 1;
v___x_2812_ = l_Lean_Meta_mkLambdaFVars(v_params_2791_, v___x_2809_, v___x_2810_, v___x_2799_, v___x_2810_, v___x_2799_, v___x_2811_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
return v___x_2812_;
}
else
{
lean_dec_ref(v___x_2804_);
return v___x_2807_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed(lean_object* v___x_2813_, lean_object* v_unaryPreDefNonRec_2814_, lean_object* v___x_2815_, lean_object* v_us_2816_, lean_object* v_argsPacker_2817_, lean_object* v___x_2818_, lean_object* v_params_2819_, lean_object* v_x_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(v___x_2813_, v_unaryPreDefNonRec_2814_, v___x_2815_, v_us_2816_, v_argsPacker_2817_, v___x_2818_, v_params_2819_, v_x_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec_ref(v_x_2820_);
lean_dec_ref(v_params_2819_);
lean_dec_ref(v_argsPacker_2817_);
lean_dec_ref(v___x_2815_);
lean_dec(v___x_2813_);
return v_res_2826_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2837_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2838_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5));
v___x_2839_ = l_Lean_Name_append(v___x_2838_, v___x_2837_);
return v___x_2839_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7));
v___x_2842_ = l_Lean_stringToMessageData(v___x_2841_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(lean_object* v_fixedParamPerms_2843_, lean_object* v_unaryPreDefNonRec_2844_, lean_object* v_us_2845_, lean_object* v_argsPacker_2846_, size_t v_sz_2847_, size_t v_i_2848_, lean_object* v_bs_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
uint8_t v___x_2855_; 
v___x_2855_ = lean_usize_dec_lt(v_i_2848_, v_sz_2847_);
if (v___x_2855_ == 0)
{
lean_object* v___x_2856_; 
lean_dec_ref(v_argsPacker_2846_);
lean_dec(v_us_2845_);
lean_dec_ref(v_unaryPreDefNonRec_2844_);
v___x_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2856_, 0, v_bs_2849_);
return v___x_2856_;
}
else
{
lean_object* v_v_2857_; lean_object* v_perms_2858_; lean_object* v_ref_2859_; uint8_t v_kind_2860_; lean_object* v_levelParams_2861_; lean_object* v_modifiers_2862_; lean_object* v_declName_2863_; lean_object* v_binders_2864_; lean_object* v_numSectionVars_2865_; lean_object* v_type_2866_; lean_object* v_termination_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2919_; 
v_v_2857_ = lean_array_uget(v_bs_2849_, v_i_2848_);
v_perms_2858_ = lean_ctor_get(v_fixedParamPerms_2843_, 1);
v_ref_2859_ = lean_ctor_get(v_v_2857_, 0);
v_kind_2860_ = lean_ctor_get_uint8(v_v_2857_, sizeof(void*)*9);
v_levelParams_2861_ = lean_ctor_get(v_v_2857_, 1);
v_modifiers_2862_ = lean_ctor_get(v_v_2857_, 2);
v_declName_2863_ = lean_ctor_get(v_v_2857_, 3);
v_binders_2864_ = lean_ctor_get(v_v_2857_, 4);
v_numSectionVars_2865_ = lean_ctor_get(v_v_2857_, 5);
v_type_2866_ = lean_ctor_get(v_v_2857_, 6);
v_termination_2867_ = lean_ctor_get(v_v_2857_, 8);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_v_2857_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; 
v_unused_2920_ = lean_ctor_get(v_v_2857_, 7);
lean_dec(v_unused_2920_);
v___x_2869_ = v_v_2857_;
v_isShared_2870_ = v_isSharedCheck_2919_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_termination_2867_);
lean_inc(v_type_2866_);
lean_inc(v_numSectionVars_2865_);
lean_inc(v_binders_2864_);
lean_inc(v_declName_2863_);
lean_inc(v_modifiers_2862_);
lean_inc(v_levelParams_2861_);
lean_inc(v_ref_2859_);
lean_dec(v_v_2857_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2919_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2871_; lean_object* v_bs_x27_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___f_2877_; lean_object* v___x_2878_; uint8_t v___x_2879_; lean_object* v___x_2880_; 
v___x_2871_ = lean_unsigned_to_nat(0u);
v_bs_x27_2872_ = lean_array_uset(v_bs_2849_, v_i_2848_, v___x_2871_);
v___x_2873_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2874_ = lean_usize_to_nat(v_i_2848_);
v___x_2875_ = lean_array_get_borrowed(v___x_2873_, v_perms_2858_, v___x_2874_);
v___x_2876_ = lean_array_get_size(v___x_2875_);
lean_inc_ref(v_argsPacker_2846_);
lean_inc(v_us_2845_);
lean_inc(v___x_2875_);
lean_inc_ref(v_unaryPreDefNonRec_2844_);
v___f_2877_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2877_, 0, v___x_2876_);
lean_closure_set(v___f_2877_, 1, v_unaryPreDefNonRec_2844_);
lean_closure_set(v___f_2877_, 2, v___x_2875_);
lean_closure_set(v___f_2877_, 3, v_us_2845_);
lean_closure_set(v___f_2877_, 4, v_argsPacker_2846_);
lean_closure_set(v___f_2877_, 5, v___x_2874_);
v___x_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2876_);
v___x_2879_ = 0;
lean_inc_ref(v_type_2866_);
v___x_2880_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2866_, v___x_2878_, v___f_2877_, v___x_2879_, v___x_2879_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v_toCold_2890_; lean_object* v_options_2891_; uint8_t v_hasTrace_2892_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref_known(v___x_2880_, 1);
v_toCold_2890_ = lean_ctor_get(v___y_2852_, 0);
v_options_2891_ = lean_ctor_get(v_toCold_2890_, 2);
v_hasTrace_2892_ = lean_ctor_get_uint8(v_options_2891_, sizeof(void*)*1);
if (v_hasTrace_2892_ == 0)
{
goto v___jp_2882_;
}
else
{
lean_object* v_inheritedTraceOptions_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; uint8_t v___x_2896_; 
v_inheritedTraceOptions_2893_ = lean_ctor_get(v_toCold_2890_, 11);
v___x_2894_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2895_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6);
v___x_2896_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2893_, v_options_2891_, v___x_2895_);
if (v___x_2896_ == 0)
{
goto v___jp_2882_;
}
else
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
lean_inc(v_declName_2863_);
v___x_2897_ = l_Lean_MessageData_ofName(v_declName_2863_);
v___x_2898_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8);
v___x_2899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2897_);
lean_ctor_set(v___x_2899_, 1, v___x_2898_);
lean_inc(v_a_2881_);
v___x_2900_ = l_Lean_MessageData_ofExpr(v_a_2881_);
v___x_2901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2899_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
v___x_2902_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v___x_2894_, v___x_2901_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_dec_ref_known(v___x_2902_, 1);
goto v___jp_2882_;
}
else
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
lean_dec(v_a_2881_);
lean_dec_ref(v_bs_x27_2872_);
lean_del_object(v___x_2869_);
lean_dec_ref(v_termination_2867_);
lean_dec_ref(v_type_2866_);
lean_dec(v_numSectionVars_2865_);
lean_dec(v_binders_2864_);
lean_dec(v_declName_2863_);
lean_dec_ref(v_modifiers_2862_);
lean_dec(v_levelParams_2861_);
lean_dec(v_ref_2859_);
lean_dec_ref(v_argsPacker_2846_);
lean_dec(v_us_2845_);
lean_dec_ref(v_unaryPreDefNonRec_2844_);
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___x_2902_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2902_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2903_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
}
v___jp_2882_:
{
lean_object* v___x_2884_; 
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 7, v_a_2881_);
v___x_2884_ = v___x_2869_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_ref_2859_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v_levelParams_2861_);
lean_ctor_set(v_reuseFailAlloc_2889_, 2, v_modifiers_2862_);
lean_ctor_set(v_reuseFailAlloc_2889_, 3, v_declName_2863_);
lean_ctor_set(v_reuseFailAlloc_2889_, 4, v_binders_2864_);
lean_ctor_set(v_reuseFailAlloc_2889_, 5, v_numSectionVars_2865_);
lean_ctor_set(v_reuseFailAlloc_2889_, 6, v_type_2866_);
lean_ctor_set(v_reuseFailAlloc_2889_, 7, v_a_2881_);
lean_ctor_set(v_reuseFailAlloc_2889_, 8, v_termination_2867_);
lean_ctor_set_uint8(v_reuseFailAlloc_2889_, sizeof(void*)*9, v_kind_2860_);
v___x_2884_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
size_t v___x_2885_; size_t v___x_2886_; lean_object* v___x_2887_; 
v___x_2885_ = ((size_t)1ULL);
v___x_2886_ = lean_usize_add(v_i_2848_, v___x_2885_);
v___x_2887_ = lean_array_uset(v_bs_x27_2872_, v_i_2848_, v___x_2884_);
v_i_2848_ = v___x_2886_;
v_bs_2849_ = v___x_2887_;
goto _start;
}
}
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec_ref(v_bs_x27_2872_);
lean_del_object(v___x_2869_);
lean_dec_ref(v_termination_2867_);
lean_dec_ref(v_type_2866_);
lean_dec(v_numSectionVars_2865_);
lean_dec(v_binders_2864_);
lean_dec(v_declName_2863_);
lean_dec_ref(v_modifiers_2862_);
lean_dec(v_levelParams_2861_);
lean_dec(v_ref_2859_);
lean_dec_ref(v_argsPacker_2846_);
lean_dec(v_us_2845_);
lean_dec_ref(v_unaryPreDefNonRec_2844_);
v_a_2911_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2880_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2880_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_2921_, lean_object* v_unaryPreDefNonRec_2922_, lean_object* v_us_2923_, lean_object* v_argsPacker_2924_, lean_object* v_sz_2925_, lean_object* v_i_2926_, lean_object* v_bs_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
size_t v_sz_boxed_2933_; size_t v_i_boxed_2934_; lean_object* v_res_2935_; 
v_sz_boxed_2933_ = lean_unbox_usize(v_sz_2925_);
lean_dec(v_sz_2925_);
v_i_boxed_2934_ = lean_unbox_usize(v_i_2926_);
lean_dec(v_i_2926_);
v_res_2935_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2921_, v_unaryPreDefNonRec_2922_, v_us_2923_, v_argsPacker_2924_, v_sz_boxed_2933_, v_i_boxed_2934_, v_bs_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec_ref(v_fixedParamPerms_2921_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(lean_object* v_unaryPreDefNonRec_2936_, lean_object* v_preDefs_2937_, lean_object* v_fixedParamPerms_2938_, lean_object* v_us_2939_, lean_object* v_argsPacker_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v___x_2946_; 
lean_inc_ref(v_unaryPreDefNonRec_2936_);
v___x_2946_ = l_Lean_Elab_addAsAxiom___redArg(v_unaryPreDefNonRec_2936_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_2946_) == 0)
{
size_t v_sz_2947_; size_t v___x_2948_; lean_object* v___x_2949_; 
lean_dec_ref_known(v___x_2946_, 1);
v_sz_2947_ = lean_array_size(v_preDefs_2937_);
v___x_2948_ = ((size_t)0ULL);
v___x_2949_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2938_, v_unaryPreDefNonRec_2936_, v_us_2939_, v_argsPacker_2940_, v_sz_2947_, v___x_2948_, v_preDefs_2937_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
return v___x_2949_;
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
lean_dec_ref(v_argsPacker_2940_);
lean_dec(v_us_2939_);
lean_dec_ref(v_preDefs_2937_);
lean_dec_ref(v_unaryPreDefNonRec_2936_);
v_a_2950_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2946_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2946_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed(lean_object* v_unaryPreDefNonRec_2958_, lean_object* v_preDefs_2959_, lean_object* v_fixedParamPerms_2960_, lean_object* v_us_2961_, lean_object* v_argsPacker_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(v_unaryPreDefNonRec_2958_, v_preDefs_2959_, v_fixedParamPerms_2960_, v_us_2961_, v_argsPacker_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec_ref(v_fixedParamPerms_2960_);
return v_res_2968_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2969_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2970_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg(){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg___closed__1);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v___dummy_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg();
return v_res_2975_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_2977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
return v___x_2977_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0);
v___x_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2978_);
lean_ctor_set(v___x_2979_, 1, v___x_2978_);
return v___x_2979_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5___redArg();
return v___x_2980_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2981_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0);
v___x_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2981_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
return v___x_2982_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2983_ = lean_unsigned_to_nat(0u);
v___x_2984_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0);
v___x_2985_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
lean_ctor_set(v___x_2985_, 1, v___x_2984_);
lean_ctor_set(v___x_2985_, 2, v___x_2983_);
return v___x_2985_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2986_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__4, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__4_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__4);
v___x_2987_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3);
v___x_2988_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0);
v___x_2989_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2);
v___x_2990_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
lean_ctor_set(v___x_2990_, 1, v___x_2988_);
lean_ctor_set(v___x_2990_, 2, v___x_2987_);
lean_ctor_set(v___x_2990_, 3, v___x_2988_);
lean_ctor_set(v___x_2990_, 4, v___x_2988_);
lean_ctor_set(v___x_2990_, 5, v___x_2988_);
lean_ctor_set(v___x_2990_, 6, v___x_2986_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(lean_object* v_env_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
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
v___x_3007_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
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
v___x_3020_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__5, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__5_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__5);
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
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___boxed(lean_object* v_env_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3032_, v___y_3033_, v___y_3034_);
lean_dec(v___y_3034_);
lean_dec(v___y_3033_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(lean_object* v_env_3037_, lean_object* v_x_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v___x_3044_; lean_object* v_env_3045_; lean_object* v_a_3047_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3044_ = lean_st_ref_get(v___y_3042_);
v_env_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc_ref(v_env_3045_);
lean_dec(v___x_3044_);
v___x_3057_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3037_, v___y_3040_, v___y_3042_);
lean_dec_ref(v___x_3057_);
lean_inc(v___y_3042_);
lean_inc_ref(v___y_3041_);
lean_inc(v___y_3040_);
lean_inc_ref(v___y_3039_);
v___x_3058_ = lean_apply_5(v_x_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, lean_box(0));
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref_known(v___x_3058_, 1);
v___x_3060_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3045_, v___y_3040_, v___y_3042_);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3067_ == 0)
{
lean_object* v_unused_3068_; 
v_unused_3068_ = lean_ctor_get(v___x_3060_, 0);
lean_dec(v_unused_3068_);
v___x_3062_ = v___x_3060_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_dec(v___x_3060_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 0, v_a_3059_);
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3059_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
else
{
lean_object* v_a_3069_; 
v_a_3069_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3069_);
lean_dec_ref_known(v___x_3058_, 1);
v_a_3047_ = v_a_3069_;
goto v___jp_3046_;
}
v___jp_3046_:
{
lean_object* v___x_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
v___x_3048_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3045_, v___y_3040_, v___y_3042_);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3055_ == 0)
{
lean_object* v_unused_3056_; 
v_unused_3056_ = lean_ctor_get(v___x_3048_, 0);
lean_dec(v_unused_3056_);
v___x_3050_ = v___x_3048_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_dec(v___x_3048_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
lean_ctor_set_tag(v___x_3050_, 1);
lean_ctor_set(v___x_3050_, 0, v_a_3047_);
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3047_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___boxed(lean_object* v_env_3070_, lean_object* v_x_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_3070_, v_x_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object* v_fixedParamPerms_3078_, lean_object* v_argsPacker_3079_, lean_object* v_preDefs_3080_, lean_object* v_unaryPreDefNonRec_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_){
_start:
{
lean_object* v_levelParams_3087_; lean_object* v___x_3088_; lean_object* v_us_3089_; lean_object* v___f_3090_; lean_object* v___x_3091_; lean_object* v_env_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v_levelParams_3087_ = lean_ctor_get(v_unaryPreDefNonRec_3081_, 1);
v___x_3088_ = lean_box(0);
lean_inc(v_levelParams_3087_);
v_us_3089_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_3087_, v___x_3088_);
v___f_3090_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3090_, 0, v_unaryPreDefNonRec_3081_);
lean_closure_set(v___f_3090_, 1, v_preDefs_3080_);
lean_closure_set(v___f_3090_, 2, v_fixedParamPerms_3078_);
lean_closure_set(v___f_3090_, 3, v_us_3089_);
lean_closure_set(v___f_3090_, 4, v_argsPacker_3079_);
v___x_3091_ = lean_st_ref_get(v_a_3085_);
v_env_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc_ref(v_env_3092_);
lean_dec(v___x_3091_);
v___x_3093_ = l_Lean_Environment_unlockAsync(v_env_3092_);
v___x_3094_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v___x_3093_, v___f_3090_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___boxed(lean_object* v_fixedParamPerms_3095_, lean_object* v_argsPacker_3096_, lean_object* v_preDefs_3097_, lean_object* v_unaryPreDefNonRec_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fixedParamPerms_3095_, v_argsPacker_3096_, v_preDefs_3097_, v_unaryPreDefNonRec_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
lean_dec(v_a_3102_);
lean_dec_ref(v_a_3101_);
lean_dec(v_a_3100_);
lean_dec_ref(v_a_3099_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(lean_object* v_fixedParamPerms_3105_, lean_object* v_unaryPreDefNonRec_3106_, lean_object* v_us_3107_, lean_object* v_argsPacker_3108_, lean_object* v_as_3109_, size_t v_sz_3110_, size_t v_i_3111_, lean_object* v_bs_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v___x_3118_; 
v___x_3118_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_3105_, v_unaryPreDefNonRec_3106_, v_us_3107_, v_argsPacker_3108_, v_sz_3110_, v_i_3111_, v_bs_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___boxed(lean_object* v_fixedParamPerms_3119_, lean_object* v_unaryPreDefNonRec_3120_, lean_object* v_us_3121_, lean_object* v_argsPacker_3122_, lean_object* v_as_3123_, lean_object* v_sz_3124_, lean_object* v_i_3125_, lean_object* v_bs_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
size_t v_sz_boxed_3132_; size_t v_i_boxed_3133_; lean_object* v_res_3134_; 
v_sz_boxed_3132_ = lean_unbox_usize(v_sz_3124_);
lean_dec(v_sz_3124_);
v_i_boxed_3133_ = lean_unbox_usize(v_i_3125_);
lean_dec(v_i_3125_);
v_res_3134_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(v_fixedParamPerms_3119_, v_unaryPreDefNonRec_3120_, v_us_3121_, v_argsPacker_3122_, v_as_3123_, v_sz_boxed_3132_, v_i_boxed_3133_, v_bs_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec_ref(v_as_3123_);
lean_dec_ref(v_fixedParamPerms_3119_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(lean_object* v_00_u03b1_3135_, lean_object* v_env_3136_, lean_object* v_x_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v___x_3143_; 
v___x_3143_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_3136_, v_x_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___boxed(lean_object* v_00_u03b1_3144_, lean_object* v_env_3145_, lean_object* v_x_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_){
_start:
{
lean_object* v_res_3152_; 
v_res_3152_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(v_00_u03b1_3144_, v_env_3145_, v_x_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(lean_object* v_env_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3153_, v___y_3155_, v___y_3157_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___boxed(lean_object* v_env_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v_res_3166_; 
v_res_3166_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(v_env_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_3167_){
_start:
{
lean_object* v___x_3168_; 
v___x_3168_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4___redArg(){
_start:
{
lean_object* v___x_3170_; 
v___x_3170_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v___dummy_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4___redArg();
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_3173_){
_start:
{
lean_object* v___x_3174_; 
v___x_3174_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2);
return v___x_3174_;
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
