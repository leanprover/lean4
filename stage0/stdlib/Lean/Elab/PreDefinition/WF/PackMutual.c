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
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_pack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* l_Lean_Meta_ArgsPacker_uncurry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_ArgsPacker_numFuncs(lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
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
static const lean_closure_object l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_packCalls___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Elab.PreDefinition.WF.PackMutual"};
static const lean_object* l_Lean_Elab_WF_packCalls___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_WF_packCalls___lam__2___closed__0_value;
static const lean_string_object l_Lean_Elab_WF_packCalls___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Elab.WF.packCalls"};
static const lean_object* l_Lean_Elab_WF_packCalls___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_WF_packCalls___lam__2___closed__1_value;
static const lean_string_object l_Lean_Elab_WF_packCalls___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "assertion violation: fidx < fixedParamPerms.perms.size\n      "};
static const lean_object* l_Lean_Elab_WF_packCalls___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_WF_packCalls___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_Elab_WF_packCalls___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_packCalls___lam__2___closed__3;
static lean_once_cell_t l_Lean_Elab_WF_packCalls___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_packCalls___lam__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_WF_packCalls___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Not a forall: "};
static const lean_object* l_Lean_Elab_WF_packCalls___closed__1 = (const lean_object*)&l_Lean_Elab_WF_packCalls___closed__1_value;
static lean_once_cell_t l_Lean_Elab_WF_packCalls___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_packCalls___closed__2;
static const lean_string_object l_Lean_Elab_WF_packCalls___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_Elab_WF_packCalls___closed__3 = (const lean_object*)&l_Lean_Elab_WF_packCalls___closed__3_value;
static lean_once_cell_t l_Lean_Elab_WF_packCalls___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_packCalls___closed__4;
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
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_92_; lean_object* v_env_93_; lean_object* v___x_94_; lean_object* v_mctx_95_; lean_object* v_lctx_96_; lean_object* v_options_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_92_ = lean_st_ref_get(v___y_90_);
v_env_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc_ref(v_env_93_);
lean_dec(v___x_92_);
v___x_94_ = lean_st_ref_get(v___y_88_);
v_mctx_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc_ref(v_mctx_95_);
lean_dec(v___x_94_);
v_lctx_96_ = lean_ctor_get(v___y_87_, 2);
v_options_97_ = lean_ctor_get(v___y_89_, 2);
lean_inc_ref(v_options_97_);
lean_inc_ref(v_lctx_96_);
v___x_98_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_98_, 0, v_env_93_);
lean_ctor_set(v___x_98_, 1, v_mctx_95_);
lean_ctor_set(v___x_98_, 2, v_lctx_96_);
lean_ctor_set(v___x_98_, 3, v_options_97_);
v___x_99_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v_msgData_86_);
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0___boxed(lean_object* v_msgData_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msgData_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(lean_object* v_msg_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_ref_114_; lean_object* v___x_115_; lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_124_; 
v_ref_114_ = lean_ctor_get(v___y_111_, 5);
v___x_115_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msg_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
v_a_116_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_124_ == 0)
{
v___x_118_ = v___x_115_;
v_isShared_119_ = v_isSharedCheck_124_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_124_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; lean_object* v___x_122_; 
lean_inc(v_ref_114_);
v___x_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_120_, 0, v_ref_114_);
lean_ctor_set(v___x_120_, 1, v_a_116_);
if (v_isShared_119_ == 0)
{
lean_ctor_set_tag(v___x_118_, 1);
lean_ctor_set(v___x_118_, 0, v___x_120_);
v___x_122_ = v___x_118_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_120_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg___boxed(lean_object* v_msg_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v_msg_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
return v_res_131_;
}
}
static lean_object* _init_l_Lean_Elab_WF_withAppN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = ((lean_object*)(l_Lean_Elab_WF_withAppN___lam__0___closed__0));
v___x_134_ = l_Lean_stringToMessageData(v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___lam__0(lean_object* v_args_135_, lean_object* v_k_136_, uint8_t v___x_137_, lean_object* v_missing_138_, lean_object* v_xs_139_, lean_object* v_x_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = lean_array_get_size(v_xs_139_);
v___x_154_ = lean_nat_dec_lt(v___x_153_, v_missing_138_);
if (v___x_154_ == 0)
{
goto v___jp_146_;
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
lean_dec_ref(v_k_136_);
lean_dec_ref(v_args_135_);
v___x_155_ = lean_obj_once(&l_Lean_Elab_WF_withAppN___lam__0___closed__1, &l_Lean_Elab_WF_withAppN___lam__0___closed__1_once, _init_l_Lean_Elab_WF_withAppN___lam__0___closed__1);
v___x_156_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v___x_155_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
v_a_157_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_156_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
v___jp_146_:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = l_Array_append___redArg(v_args_135_, v_xs_139_);
lean_inc(v___y_144_);
lean_inc_ref(v___y_143_);
lean_inc(v___y_142_);
lean_inc_ref(v___y_141_);
v___x_148_ = lean_apply_6(v_k_136_, v___x_147_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, lean_box(0));
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_149_; uint8_t v___x_150_; uint8_t v___x_151_; lean_object* v___x_152_; 
v_a_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_a_149_);
lean_dec_ref_known(v___x_148_, 1);
v___x_150_ = 1;
v___x_151_ = 1;
v___x_152_ = l_Lean_Meta_mkLambdaFVars(v_xs_139_, v_a_149_, v___x_137_, v___x_150_, v___x_137_, v___x_150_, v___x_151_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
return v___x_152_;
}
else
{
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___lam__0___boxed(lean_object* v_args_165_, lean_object* v_k_166_, lean_object* v___x_167_, lean_object* v_missing_168_, lean_object* v_xs_169_, lean_object* v_x_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
uint8_t v___x_2318__boxed_176_; lean_object* v_res_177_; 
v___x_2318__boxed_176_ = lean_unbox(v___x_167_);
v_res_177_ = l_Lean_Elab_WF_withAppN___lam__0(v_args_165_, v_k_166_, v___x_2318__boxed_176_, v_missing_168_, v_xs_169_, v_x_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec_ref(v_x_170_);
lean_dec_ref(v_xs_169_);
lean_dec(v_missing_168_);
return v_res_177_;
}
}
static lean_object* _init_l_Lean_Elab_WF_withAppN___closed__0(void){
_start:
{
lean_object* v___x_178_; lean_object* v_dummy_179_; 
v___x_178_ = lean_box(0);
v_dummy_179_ = l_Lean_Expr_sort___override(v___x_178_);
return v_dummy_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN(lean_object* v_n_180_, lean_object* v_e_181_, lean_object* v_k_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_dummy_188_; lean_object* v_nargs_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v_args_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v_dummy_188_ = lean_obj_once(&l_Lean_Elab_WF_withAppN___closed__0, &l_Lean_Elab_WF_withAppN___closed__0_once, _init_l_Lean_Elab_WF_withAppN___closed__0);
v_nargs_189_ = l_Lean_Expr_getAppNumArgs(v_e_181_);
lean_inc(v_nargs_189_);
v___x_190_ = lean_mk_array(v_nargs_189_, v_dummy_188_);
v___x_191_ = lean_unsigned_to_nat(1u);
v___x_192_ = lean_nat_sub(v_nargs_189_, v___x_191_);
lean_dec(v_nargs_189_);
lean_inc_ref(v_e_181_);
v_args_193_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_181_, v___x_190_, v___x_192_);
v___x_194_ = lean_array_get_size(v_args_193_);
v___x_195_ = lean_nat_dec_le(v_n_180_, v___x_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; 
lean_inc(v_a_186_);
lean_inc_ref(v_a_185_);
lean_inc(v_a_184_);
lean_inc_ref(v_a_183_);
v___x_196_ = lean_infer_type(v_e_181_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_208_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_208_ == 0)
{
v___x_199_ = v___x_196_;
v_isShared_200_ = v_isSharedCheck_208_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_196_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_208_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v_missing_201_; lean_object* v___x_202_; lean_object* v___f_203_; lean_object* v___x_205_; 
v_missing_201_ = lean_nat_sub(v_n_180_, v___x_194_);
lean_dec(v_n_180_);
v___x_202_ = lean_box(v___x_195_);
lean_inc(v_missing_201_);
v___f_203_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_withAppN___lam__0___boxed), 11, 4);
lean_closure_set(v___f_203_, 0, v_args_193_);
lean_closure_set(v___f_203_, 1, v_k_182_);
lean_closure_set(v___f_203_, 2, v___x_202_);
lean_closure_set(v___f_203_, 3, v_missing_201_);
if (v_isShared_200_ == 0)
{
lean_ctor_set_tag(v___x_199_, 1);
lean_ctor_set(v___x_199_, 0, v_missing_201_);
v___x_205_ = v___x_199_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_missing_201_);
v___x_205_ = v_reuseFailAlloc_207_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_a_197_, v___x_205_, v___f_203_, v___x_195_, v___x_195_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
return v___x_206_;
}
}
}
else
{
lean_dec_ref(v_args_193_);
lean_dec_ref(v_k_182_);
lean_dec(v_n_180_);
return v___x_196_;
}
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec_ref(v_e_181_);
v___x_209_ = lean_unsigned_to_nat(0u);
lean_inc(v_n_180_);
lean_inc_ref(v_args_193_);
v___x_210_ = l_Array_toSubarray___redArg(v_args_193_, v___x_209_, v_n_180_);
v___x_211_ = l_Subarray_copy___redArg(v___x_210_);
lean_inc(v_a_186_);
lean_inc_ref(v_a_185_);
lean_inc(v_a_184_);
lean_inc_ref(v_a_183_);
v___x_212_ = lean_apply_6(v_k_182_, v___x_211_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, lean_box(0));
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_227_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_227_ == 0)
{
v___x_215_ = v___x_212_;
v_isShared_216_ = v_isSharedCheck_227_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_212_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_227_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_lower_218_; lean_object* v_upper_219_; uint8_t v___x_226_; 
v___x_226_ = lean_nat_dec_le(v_n_180_, v___x_209_);
if (v___x_226_ == 0)
{
v_lower_218_ = v_n_180_;
v_upper_219_ = v___x_194_;
goto v___jp_217_;
}
else
{
lean_dec(v_n_180_);
v_lower_218_ = v___x_209_;
v_upper_219_ = v___x_194_;
goto v___jp_217_;
}
v___jp_217_:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_220_ = l_Array_toSubarray___redArg(v_args_193_, v_lower_218_, v_upper_219_);
v___x_221_ = l_Subarray_copy___redArg(v___x_220_);
v___x_222_ = l_Lean_mkAppN(v_a_213_, v___x_221_);
lean_dec_ref(v___x_221_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_222_);
v___x_224_ = v___x_215_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
else
{
lean_dec_ref(v_args_193_);
lean_dec(v_n_180_);
return v___x_212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___boxed(lean_object* v_n_228_, lean_object* v_e_229_, lean_object* v_k_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Elab_WF_withAppN(v_n_228_, v_e_229_, v_k_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec(v_a_232_);
lean_dec_ref(v_a_231_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0(lean_object* v_00_u03b1_237_, lean_object* v_msg_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v_msg_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___boxed(lean_object* v_00_u03b1_245_, lean_object* v_msg_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0(v_00_u03b1_245_, v_msg_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_packCalls_spec__1(lean_object* v_msg_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___f_260_; lean_object* v___x_1447__overap_261_; lean_object* v___x_262_; 
v___f_260_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1447__overap_261_ = lean_panic_fn_borrowed(v___f_260_, v_msg_254_);
lean_inc(v___y_258_);
lean_inc_ref(v___y_257_);
lean_inc(v___y_256_);
lean_inc_ref(v___y_255_);
v___x_262_ = lean_apply_5(v___x_1447__overap_261_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, lean_box(0));
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_packCalls_spec__1___boxed(lean_object* v_msg_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_panic___at___00Lean_Elab_WF_packCalls_spec__1(v_msg_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__0(lean_object* v_x_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__0___closed__0));
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__0___boxed(lean_object* v_x_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Elab_WF_packCalls___lam__0(v_x_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec_ref(v_x_280_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__1(lean_object* v___x_287_, lean_object* v_argsPacker_288_, lean_object* v___x_289_, lean_object* v_val_290_, lean_object* v_newF_291_, lean_object* v_args_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_287_, v_args_292_);
v___x_299_ = l_Lean_Meta_ArgsPacker_pack(v_argsPacker_288_, v___x_289_, v_val_290_, v___x_298_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec_ref(v___x_298_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_308_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_308_ == 0)
{
v___x_302_ = v___x_299_;
v_isShared_303_ = v_isSharedCheck_308_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_308_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_304_ = l_Lean_Expr_app___override(v_newF_291_, v_a_300_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_304_);
v___x_306_ = v___x_302_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_304_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
else
{
lean_dec_ref(v_newF_291_);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__1___boxed(lean_object* v___x_309_, lean_object* v_argsPacker_310_, lean_object* v___x_311_, lean_object* v_val_312_, lean_object* v_newF_313_, lean_object* v_args_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Elab_WF_packCalls___lam__1(v___x_309_, v_argsPacker_310_, v___x_311_, v_val_312_, v_newF_313_, v_args_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec_ref(v_args_314_);
lean_dec_ref(v_argsPacker_310_);
lean_dec_ref(v___x_309_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2(lean_object* v_xs_321_, lean_object* v_v_322_, lean_object* v_i_323_){
_start:
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = lean_array_get_size(v_xs_321_);
v___x_325_ = lean_nat_dec_lt(v_i_323_, v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
lean_dec(v_i_323_);
v___x_326_ = lean_box(0);
return v___x_326_;
}
else
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = lean_array_fget_borrowed(v_xs_321_, v_i_323_);
v___x_328_ = lean_name_eq(v___x_327_, v_v_322_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_unsigned_to_nat(1u);
v___x_330_ = lean_nat_add(v_i_323_, v___x_329_);
lean_dec(v_i_323_);
v_i_323_ = v___x_330_;
goto _start;
}
else
{
lean_object* v___x_332_; 
v___x_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_332_, 0, v_i_323_);
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2___boxed(lean_object* v_xs_333_, lean_object* v_v_334_, lean_object* v_i_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2(v_xs_333_, v_v_334_, v_i_335_);
lean_dec(v_v_334_);
lean_dec_ref(v_xs_333_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0(lean_object* v_xs_337_, lean_object* v_v_338_){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2(v_xs_337_, v_v_338_, v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0___boxed(lean_object* v_xs_341_, lean_object* v_v_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0(v_xs_341_, v_v_342_);
lean_dec(v_v_342_);
lean_dec_ref(v_xs_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(lean_object* v_xs_344_, lean_object* v_v_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0(v_xs_344_, v_v_345_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v___x_347_; 
v___x_347_ = lean_box(0);
return v___x_347_;
}
else
{
lean_object* v_val_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
v_val_348_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_346_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_val_348_);
lean_dec(v___x_346_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_val_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0___boxed(lean_object* v_xs_356_, lean_object* v_v_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(v_xs_356_, v_v_357_);
lean_dec(v_v_357_);
lean_dec_ref(v_xs_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(uint8_t v___x_359_, size_t v_sz_360_, size_t v_i_361_, lean_object* v_bs_362_){
_start:
{
uint8_t v___x_363_; 
v___x_363_ = lean_usize_dec_lt(v_i_361_, v_sz_360_);
if (v___x_363_ == 0)
{
return v_bs_362_;
}
else
{
lean_object* v_v_364_; lean_object* v___x_365_; lean_object* v_bs_x27_366_; uint8_t v___y_368_; 
v_v_364_ = lean_array_uget(v_bs_362_, v_i_361_);
v___x_365_ = lean_unsigned_to_nat(0u);
v_bs_x27_366_ = lean_array_uset(v_bs_362_, v_i_361_, v___x_365_);
if (lean_obj_tag(v_v_364_) == 0)
{
uint8_t v___x_374_; 
v___x_374_ = 0;
v___y_368_ = v___x_374_;
goto v___jp_367_;
}
else
{
lean_dec_ref_known(v_v_364_, 1);
v___y_368_ = v___x_359_;
goto v___jp_367_;
}
v___jp_367_:
{
size_t v___x_369_; size_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_369_ = ((size_t)1ULL);
v___x_370_ = lean_usize_add(v_i_361_, v___x_369_);
v___x_371_ = lean_box(v___y_368_);
v___x_372_ = lean_array_uset(v_bs_x27_366_, v_i_361_, v___x_371_);
v_i_361_ = v___x_370_;
v_bs_362_ = v___x_372_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2___boxed(lean_object* v___x_375_, lean_object* v_sz_376_, lean_object* v_i_377_, lean_object* v_bs_378_){
_start:
{
uint8_t v___x_9900__boxed_379_; size_t v_sz_boxed_380_; size_t v_i_boxed_381_; lean_object* v_res_382_; 
v___x_9900__boxed_379_ = lean_unbox(v___x_375_);
v_sz_boxed_380_ = lean_unbox_usize(v_sz_376_);
lean_dec(v_sz_376_);
v_i_boxed_381_ = lean_unbox_usize(v_i_377_);
lean_dec(v_i_377_);
v_res_382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(v___x_9900__boxed_379_, v_sz_boxed_380_, v_i_boxed_381_, v_bs_378_);
return v_res_382_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___lam__2___closed__3(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_386_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__2));
v___x_387_ = lean_unsigned_to_nat(6u);
v___x_388_ = lean_unsigned_to_nat(55u);
v___x_389_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__1));
v___x_390_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_391_ = l_mkPanicMessageWithDecl(v___x_390_, v___x_389_, v___x_388_, v___x_387_, v___x_386_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4(void){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Array_instInhabited(lean_box(0));
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__2(lean_object* v_funNames_393_, lean_object* v_fixedParamPerms_394_, lean_object* v_argsPacker_395_, lean_object* v___x_396_, lean_object* v_newF_397_, lean_object* v_e_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = l_Lean_Expr_getAppFn(v_e_398_);
v___x_405_ = l_Lean_Expr_isConst(v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec_ref(v___x_404_);
lean_dec_ref(v_newF_397_);
lean_dec_ref(v___x_396_);
lean_dec_ref(v_argsPacker_395_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v_e_398_);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = l_Lean_Expr_constName_x21(v___x_404_);
lean_dec_ref(v___x_404_);
v___x_409_ = l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(v_funNames_393_, v___x_408_);
lean_dec(v___x_408_);
if (lean_obj_tag(v___x_409_) == 1)
{
lean_object* v_val_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_446_; 
v_val_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_446_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_446_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_val_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_446_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v_perms_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v_perms_414_ = lean_ctor_get(v_fixedParamPerms_394_, 1);
v___x_415_ = lean_array_get_size(v_perms_414_);
v___x_416_ = lean_nat_dec_lt(v_val_410_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_418_; 
lean_del_object(v___x_412_);
lean_dec(v_val_410_);
lean_dec_ref(v_e_398_);
lean_dec_ref(v_newF_397_);
lean_dec_ref(v___x_396_);
lean_dec_ref(v_argsPacker_395_);
v___x_417_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__3, &l_Lean_Elab_WF_packCalls___lam__2___closed__3_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__3);
v___x_418_ = l_panic___at___00Lean_Elab_WF_packCalls_spec__1(v___x_417_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
return v___x_418_;
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___f_421_; size_t v_sz_422_; size_t v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_419_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_420_ = lean_array_get_borrowed(v___x_419_, v_perms_414_, v_val_410_);
lean_inc_n(v___x_420_, 2);
v___f_421_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packCalls___lam__1___boxed), 11, 5);
lean_closure_set(v___f_421_, 0, v___x_420_);
lean_closure_set(v___f_421_, 1, v_argsPacker_395_);
lean_closure_set(v___f_421_, 2, v___x_396_);
lean_closure_set(v___f_421_, 3, v_val_410_);
lean_closure_set(v___f_421_, 4, v_newF_397_);
v_sz_422_ = lean_array_size(v___x_420_);
v___x_423_ = ((size_t)0ULL);
v___x_424_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(v___x_405_, v_sz_422_, v___x_423_, v___x_420_);
v___x_425_ = lean_array_get_size(v___x_424_);
lean_dec_ref(v___x_424_);
v___x_426_ = l_Lean_Elab_WF_withAppN(v___x_425_, v_e_398_, v___f_421_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_437_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_437_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_437_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_437_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set_tag(v___x_412_, 0);
lean_ctor_set(v___x_412_, 0, v_a_427_);
v___x_432_ = v___x_412_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_436_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_434_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_432_);
v___x_434_ = v___x_429_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_del_object(v___x_412_);
v_a_438_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_426_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_426_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec(v___x_409_);
lean_dec_ref(v_newF_397_);
lean_dec_ref(v___x_396_);
lean_dec_ref(v_argsPacker_395_);
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v_e_398_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__2___boxed(lean_object* v_funNames_449_, lean_object* v_fixedParamPerms_450_, lean_object* v_argsPacker_451_, lean_object* v___x_452_, lean_object* v_newF_453_, lean_object* v_e_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_Elab_WF_packCalls___lam__2(v_funNames_449_, v_fixedParamPerms_450_, v_argsPacker_451_, v___x_452_, v_newF_453_, v_e_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec_ref(v_fixedParamPerms_450_);
lean_dec_ref(v_funNames_449_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_object* v_00_u03b1_461_, lean_object* v_x_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_apply_1(v_x_462_, lean_box(0));
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0___boxed(lean_object* v_00_u03b1_470_, lean_object* v_x_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(v_00_u03b1_470_, v_x_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
return v_res_477_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = l_Lean_maxRecDepthErrorMessage;
v___x_484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3);
v___x_486_ = l_Lean_MessageData_ofFormat(v___x_485_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4);
v___x_488_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2));
v___x_489_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v___x_487_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(lean_object* v_ref_490_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5);
v___x_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_493_, 0, v_ref_490_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___boxed(lean_object* v_ref_495_, lean_object* v___y_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(lean_object* v_x_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___y_506_; lean_object* v_fileName_515_; lean_object* v_fileMap_516_; lean_object* v_options_517_; lean_object* v_currRecDepth_518_; lean_object* v_maxRecDepth_519_; lean_object* v_ref_520_; lean_object* v_currNamespace_521_; lean_object* v_openDecls_522_; lean_object* v_initHeartbeats_523_; lean_object* v_maxHeartbeats_524_; lean_object* v_quotContext_525_; lean_object* v_currMacroScope_526_; uint8_t v_diag_527_; lean_object* v_cancelTk_x3f_528_; uint8_t v_suppressElabErrors_529_; lean_object* v_inheritedTraceOptions_530_; lean_object* v___x_536_; uint8_t v___x_537_; 
v_fileName_515_ = lean_ctor_get(v___y_502_, 0);
v_fileMap_516_ = lean_ctor_get(v___y_502_, 1);
v_options_517_ = lean_ctor_get(v___y_502_, 2);
v_currRecDepth_518_ = lean_ctor_get(v___y_502_, 3);
v_maxRecDepth_519_ = lean_ctor_get(v___y_502_, 4);
v_ref_520_ = lean_ctor_get(v___y_502_, 5);
v_currNamespace_521_ = lean_ctor_get(v___y_502_, 6);
v_openDecls_522_ = lean_ctor_get(v___y_502_, 7);
v_initHeartbeats_523_ = lean_ctor_get(v___y_502_, 8);
v_maxHeartbeats_524_ = lean_ctor_get(v___y_502_, 9);
v_quotContext_525_ = lean_ctor_get(v___y_502_, 10);
v_currMacroScope_526_ = lean_ctor_get(v___y_502_, 11);
v_diag_527_ = lean_ctor_get_uint8(v___y_502_, sizeof(void*)*14);
v_cancelTk_x3f_528_ = lean_ctor_get(v___y_502_, 12);
v_suppressElabErrors_529_ = lean_ctor_get_uint8(v___y_502_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_530_ = lean_ctor_get(v___y_502_, 13);
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = lean_nat_dec_eq(v_maxRecDepth_519_, v___x_536_);
if (v___x_537_ == 0)
{
uint8_t v___x_538_; 
v___x_538_ = lean_nat_dec_eq(v_currRecDepth_518_, v_maxRecDepth_519_);
if (v___x_538_ == 0)
{
goto v___jp_531_;
}
else
{
lean_object* v___x_539_; 
lean_dec_ref(v_x_498_);
lean_inc(v_ref_520_);
v___x_539_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_520_);
v___y_506_ = v___x_539_;
goto v___jp_505_;
}
}
else
{
goto v___jp_531_;
}
v___jp_505_:
{
if (lean_obj_tag(v___y_506_) == 0)
{
return v___y_506_;
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
v_a_507_ = lean_ctor_get(v___y_506_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___y_506_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___y_506_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___y_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
v___jp_531_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_532_ = lean_unsigned_to_nat(1u);
v___x_533_ = lean_nat_add(v_currRecDepth_518_, v___x_532_);
lean_inc_ref(v_inheritedTraceOptions_530_);
lean_inc(v_cancelTk_x3f_528_);
lean_inc(v_currMacroScope_526_);
lean_inc(v_quotContext_525_);
lean_inc(v_maxHeartbeats_524_);
lean_inc(v_initHeartbeats_523_);
lean_inc(v_openDecls_522_);
lean_inc(v_currNamespace_521_);
lean_inc(v_ref_520_);
lean_inc(v_maxRecDepth_519_);
lean_inc_ref(v_options_517_);
lean_inc_ref(v_fileMap_516_);
lean_inc_ref(v_fileName_515_);
v___x_534_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_534_, 0, v_fileName_515_);
lean_ctor_set(v___x_534_, 1, v_fileMap_516_);
lean_ctor_set(v___x_534_, 2, v_options_517_);
lean_ctor_set(v___x_534_, 3, v___x_533_);
lean_ctor_set(v___x_534_, 4, v_maxRecDepth_519_);
lean_ctor_set(v___x_534_, 5, v_ref_520_);
lean_ctor_set(v___x_534_, 6, v_currNamespace_521_);
lean_ctor_set(v___x_534_, 7, v_openDecls_522_);
lean_ctor_set(v___x_534_, 8, v_initHeartbeats_523_);
lean_ctor_set(v___x_534_, 9, v_maxHeartbeats_524_);
lean_ctor_set(v___x_534_, 10, v_quotContext_525_);
lean_ctor_set(v___x_534_, 11, v_currMacroScope_526_);
lean_ctor_set(v___x_534_, 12, v_cancelTk_x3f_528_);
lean_ctor_set(v___x_534_, 13, v_inheritedTraceOptions_530_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*14, v_diag_527_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*14 + 1, v_suppressElabErrors_529_);
lean_inc(v___y_503_);
lean_inc(v___y_501_);
lean_inc_ref(v___y_500_);
lean_inc(v___y_499_);
v___x_535_ = lean_apply_6(v_x_498_, v___y_499_, v___y_500_, v___y_501_, v___x_534_, v___y_503_, lean_box(0));
v___y_506_ = v___x_535_;
goto v___jp_505_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg___boxed(lean_object* v_x_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(lean_object* v___x_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_548_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2___boxed(lean_object* v___x_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(v___x_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(lean_object* v_k_562_, lean_object* v___y_563_, lean_object* v_b_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___x_570_; 
lean_inc(v___y_568_);
lean_inc_ref(v___y_567_);
lean_inc(v___y_566_);
lean_inc_ref(v___y_565_);
lean_inc(v___y_563_);
v___x_570_ = lean_apply_7(v_k_562_, v_b_564_, v___y_563_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, lean_box(0));
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed(lean_object* v_k_571_, lean_object* v___y_572_, lean_object* v_b_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(v_k_571_, v___y_572_, v_b_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_572_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(lean_object* v_name_580_, lean_object* v_type_581_, lean_object* v_val_582_, lean_object* v_k_583_, uint8_t v_nondep_584_, uint8_t v_kind_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v___f_592_; lean_object* v___x_593_; 
lean_inc(v___y_586_);
v___f_592_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_592_, 0, v_k_583_);
lean_closure_set(v___f_592_, 1, v___y_586_);
v___x_593_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_580_, v_type_581_, v_val_582_, v___f_592_, v_nondep_584_, v_kind_585_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_593_) == 0)
{
return v___x_593_;
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg___boxed(lean_object* v_name_602_, lean_object* v_type_603_, lean_object* v_val_604_, lean_object* v_k_605_, lean_object* v_nondep_606_, lean_object* v_kind_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
uint8_t v_nondep_boxed_614_; uint8_t v_kind_boxed_615_; lean_object* v_res_616_; 
v_nondep_boxed_614_ = lean_unbox(v_nondep_606_);
v_kind_boxed_615_ = lean_unbox(v_kind_607_);
v_res_616_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_602_, v_type_603_, v_val_604_, v_k_605_, v_nondep_boxed_614_, v_kind_boxed_615_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(lean_object* v_name_617_, uint8_t v_bi_618_, lean_object* v_type_619_, lean_object* v_k_620_, uint8_t v_kind_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___f_628_; lean_object* v___x_629_; 
lean_inc(v___y_622_);
v___f_628_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_628_, 0, v_k_620_);
lean_closure_set(v___f_628_, 1, v___y_622_);
v___x_629_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_617_, v_bi_618_, v_type_619_, v___f_628_, v_kind_621_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_629_) == 0)
{
return v___x_629_;
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___boxed(lean_object* v_name_638_, lean_object* v_bi_639_, lean_object* v_type_640_, lean_object* v_k_641_, lean_object* v_kind_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
uint8_t v_bi_boxed_649_; uint8_t v_kind_boxed_650_; lean_object* v_res_651_; 
v_bi_boxed_649_ = lean_unbox(v_bi_639_);
v_kind_boxed_650_ = lean_unbox(v_kind_642_);
v_res_651_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_638_, v_bi_boxed_649_, v_type_640_, v_k_641_, v_kind_boxed_650_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_object* v_00_u03b1_652_, lean_object* v_x_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_apply_1(v_x_653_, lean_box(0));
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0___boxed(lean_object* v_00_u03b1_661_, lean_object* v_x_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(v_00_u03b1_661_, v_x_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(lean_object* v_a_669_, lean_object* v_x_670_){
_start:
{
if (lean_obj_tag(v_x_670_) == 0)
{
lean_object* v___x_671_; 
v___x_671_ = lean_box(0);
return v___x_671_;
}
else
{
lean_object* v_key_672_; lean_object* v_value_673_; lean_object* v_tail_674_; uint8_t v___x_675_; 
v_key_672_ = lean_ctor_get(v_x_670_, 0);
v_value_673_ = lean_ctor_get(v_x_670_, 1);
v_tail_674_ = lean_ctor_get(v_x_670_, 2);
v___x_675_ = l_Lean_ExprStructEq_beq(v_key_672_, v_a_669_);
if (v___x_675_ == 0)
{
v_x_670_ = v_tail_674_;
goto _start;
}
else
{
lean_object* v___x_677_; 
lean_inc(v_value_673_);
v___x_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_677_, 0, v_value_673_);
return v___x_677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg___boxed(lean_object* v_a_678_, lean_object* v_x_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_678_, v_x_679_);
lean_dec(v_x_679_);
lean_dec_ref(v_a_678_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(lean_object* v_m_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_buckets_683_; lean_object* v___x_684_; uint64_t v___x_685_; uint64_t v___x_686_; uint64_t v___x_687_; uint64_t v_fold_688_; uint64_t v___x_689_; uint64_t v___x_690_; uint64_t v___x_691_; size_t v___x_692_; size_t v___x_693_; size_t v___x_694_; size_t v___x_695_; size_t v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v_buckets_683_ = lean_ctor_get(v_m_681_, 1);
v___x_684_ = lean_array_get_size(v_buckets_683_);
v___x_685_ = l_Lean_ExprStructEq_hash(v_a_682_);
v___x_686_ = 32ULL;
v___x_687_ = lean_uint64_shift_right(v___x_685_, v___x_686_);
v_fold_688_ = lean_uint64_xor(v___x_685_, v___x_687_);
v___x_689_ = 16ULL;
v___x_690_ = lean_uint64_shift_right(v_fold_688_, v___x_689_);
v___x_691_ = lean_uint64_xor(v_fold_688_, v___x_690_);
v___x_692_ = lean_uint64_to_usize(v___x_691_);
v___x_693_ = lean_usize_of_nat(v___x_684_);
v___x_694_ = ((size_t)1ULL);
v___x_695_ = lean_usize_sub(v___x_693_, v___x_694_);
v___x_696_ = lean_usize_land(v___x_692_, v___x_695_);
v___x_697_ = lean_array_uget_borrowed(v_buckets_683_, v___x_696_);
v___x_698_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_682_, v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___boxed(lean_object* v_m_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_m_699_, v_a_700_);
lean_dec_ref(v_a_700_);
lean_dec_ref(v_m_699_);
return v_res_701_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(lean_object* v_a_702_, lean_object* v_x_703_){
_start:
{
if (lean_obj_tag(v_x_703_) == 0)
{
uint8_t v___x_704_; 
v___x_704_ = 0;
return v___x_704_;
}
else
{
lean_object* v_key_705_; lean_object* v_tail_706_; uint8_t v___x_707_; 
v_key_705_ = lean_ctor_get(v_x_703_, 0);
v_tail_706_ = lean_ctor_get(v_x_703_, 2);
v___x_707_ = l_Lean_ExprStructEq_beq(v_key_705_, v_a_702_);
if (v___x_707_ == 0)
{
v_x_703_ = v_tail_706_;
goto _start;
}
else
{
return v___x_707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg___boxed(lean_object* v_a_709_, lean_object* v_x_710_){
_start:
{
uint8_t v_res_711_; lean_object* v_r_712_; 
v_res_711_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_709_, v_x_710_);
lean_dec(v_x_710_);
lean_dec_ref(v_a_709_);
v_r_712_ = lean_box(v_res_711_);
return v_r_712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(lean_object* v_x_713_, lean_object* v_x_714_){
_start:
{
if (lean_obj_tag(v_x_714_) == 0)
{
return v_x_713_;
}
else
{
lean_object* v_key_715_; lean_object* v_value_716_; lean_object* v_tail_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_740_; 
v_key_715_ = lean_ctor_get(v_x_714_, 0);
v_value_716_ = lean_ctor_get(v_x_714_, 1);
v_tail_717_ = lean_ctor_get(v_x_714_, 2);
v_isSharedCheck_740_ = !lean_is_exclusive(v_x_714_);
if (v_isSharedCheck_740_ == 0)
{
v___x_719_ = v_x_714_;
v_isShared_720_ = v_isSharedCheck_740_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_tail_717_);
lean_inc(v_value_716_);
lean_inc(v_key_715_);
lean_dec(v_x_714_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_740_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; uint64_t v___x_722_; uint64_t v___x_723_; uint64_t v___x_724_; uint64_t v_fold_725_; uint64_t v___x_726_; uint64_t v___x_727_; uint64_t v___x_728_; size_t v___x_729_; size_t v___x_730_; size_t v___x_731_; size_t v___x_732_; size_t v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_721_ = lean_array_get_size(v_x_713_);
v___x_722_ = l_Lean_ExprStructEq_hash(v_key_715_);
v___x_723_ = 32ULL;
v___x_724_ = lean_uint64_shift_right(v___x_722_, v___x_723_);
v_fold_725_ = lean_uint64_xor(v___x_722_, v___x_724_);
v___x_726_ = 16ULL;
v___x_727_ = lean_uint64_shift_right(v_fold_725_, v___x_726_);
v___x_728_ = lean_uint64_xor(v_fold_725_, v___x_727_);
v___x_729_ = lean_uint64_to_usize(v___x_728_);
v___x_730_ = lean_usize_of_nat(v___x_721_);
v___x_731_ = ((size_t)1ULL);
v___x_732_ = lean_usize_sub(v___x_730_, v___x_731_);
v___x_733_ = lean_usize_land(v___x_729_, v___x_732_);
v___x_734_ = lean_array_uget_borrowed(v_x_713_, v___x_733_);
lean_inc(v___x_734_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 2, v___x_734_);
v___x_736_ = v___x_719_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_key_715_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_value_716_);
lean_ctor_set(v_reuseFailAlloc_739_, 2, v___x_734_);
v___x_736_ = v_reuseFailAlloc_739_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_737_; 
v___x_737_ = lean_array_uset(v_x_713_, v___x_733_, v___x_736_);
v_x_713_ = v___x_737_;
v_x_714_ = v_tail_717_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(lean_object* v_i_741_, lean_object* v_source_742_, lean_object* v_target_743_){
_start:
{
lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_744_ = lean_array_get_size(v_source_742_);
v___x_745_ = lean_nat_dec_lt(v_i_741_, v___x_744_);
if (v___x_745_ == 0)
{
lean_dec_ref(v_source_742_);
lean_dec(v_i_741_);
return v_target_743_;
}
else
{
lean_object* v_es_746_; lean_object* v___x_747_; lean_object* v_source_748_; lean_object* v_target_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v_es_746_ = lean_array_fget(v_source_742_, v_i_741_);
v___x_747_ = lean_box(0);
v_source_748_ = lean_array_fset(v_source_742_, v_i_741_, v___x_747_);
v_target_749_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(v_target_743_, v_es_746_);
v___x_750_ = lean_unsigned_to_nat(1u);
v___x_751_ = lean_nat_add(v_i_741_, v___x_750_);
lean_dec(v_i_741_);
v_i_741_ = v___x_751_;
v_source_742_ = v_source_748_;
v_target_743_ = v_target_749_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(lean_object* v_data_753_){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v_nbuckets_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_754_ = lean_array_get_size(v_data_753_);
v___x_755_ = lean_unsigned_to_nat(2u);
v_nbuckets_756_ = lean_nat_mul(v___x_754_, v___x_755_);
v___x_757_ = lean_unsigned_to_nat(0u);
v___x_758_ = lean_box(0);
v___x_759_ = lean_mk_array(v_nbuckets_756_, v___x_758_);
v___x_760_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v___x_757_, v_data_753_, v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(lean_object* v_a_761_, lean_object* v_b_762_, lean_object* v_x_763_){
_start:
{
if (lean_obj_tag(v_x_763_) == 0)
{
lean_dec(v_b_762_);
lean_dec_ref(v_a_761_);
return v_x_763_;
}
else
{
lean_object* v_key_764_; lean_object* v_value_765_; lean_object* v_tail_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_778_; 
v_key_764_ = lean_ctor_get(v_x_763_, 0);
v_value_765_ = lean_ctor_get(v_x_763_, 1);
v_tail_766_ = lean_ctor_get(v_x_763_, 2);
v_isSharedCheck_778_ = !lean_is_exclusive(v_x_763_);
if (v_isSharedCheck_778_ == 0)
{
v___x_768_ = v_x_763_;
v_isShared_769_ = v_isSharedCheck_778_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_tail_766_);
lean_inc(v_value_765_);
lean_inc(v_key_764_);
lean_dec(v_x_763_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_778_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
uint8_t v___x_770_; 
v___x_770_ = l_Lean_ExprStructEq_beq(v_key_764_, v_a_761_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_771_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_761_, v_b_762_, v_tail_766_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 2, v___x_771_);
v___x_773_ = v___x_768_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_key_764_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_value_765_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
else
{
lean_object* v___x_776_; 
lean_dec(v_value_765_);
lean_dec(v_key_764_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v_b_762_);
lean_ctor_set(v___x_768_, 0, v_a_761_);
v___x_776_ = v___x_768_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_761_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_b_762_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v_tail_766_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(lean_object* v_m_779_, lean_object* v_a_780_, lean_object* v_b_781_){
_start:
{
lean_object* v_size_782_; lean_object* v_buckets_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_826_; 
v_size_782_ = lean_ctor_get(v_m_779_, 0);
v_buckets_783_ = lean_ctor_get(v_m_779_, 1);
v_isSharedCheck_826_ = !lean_is_exclusive(v_m_779_);
if (v_isSharedCheck_826_ == 0)
{
v___x_785_ = v_m_779_;
v_isShared_786_ = v_isSharedCheck_826_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_buckets_783_);
lean_inc(v_size_782_);
lean_dec(v_m_779_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_826_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; uint64_t v___x_788_; uint64_t v___x_789_; uint64_t v___x_790_; uint64_t v_fold_791_; uint64_t v___x_792_; uint64_t v___x_793_; uint64_t v___x_794_; size_t v___x_795_; size_t v___x_796_; size_t v___x_797_; size_t v___x_798_; size_t v___x_799_; lean_object* v_bkt_800_; uint8_t v___x_801_; 
v___x_787_ = lean_array_get_size(v_buckets_783_);
v___x_788_ = l_Lean_ExprStructEq_hash(v_a_780_);
v___x_789_ = 32ULL;
v___x_790_ = lean_uint64_shift_right(v___x_788_, v___x_789_);
v_fold_791_ = lean_uint64_xor(v___x_788_, v___x_790_);
v___x_792_ = 16ULL;
v___x_793_ = lean_uint64_shift_right(v_fold_791_, v___x_792_);
v___x_794_ = lean_uint64_xor(v_fold_791_, v___x_793_);
v___x_795_ = lean_uint64_to_usize(v___x_794_);
v___x_796_ = lean_usize_of_nat(v___x_787_);
v___x_797_ = ((size_t)1ULL);
v___x_798_ = lean_usize_sub(v___x_796_, v___x_797_);
v___x_799_ = lean_usize_land(v___x_795_, v___x_798_);
v_bkt_800_ = lean_array_uget_borrowed(v_buckets_783_, v___x_799_);
v___x_801_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_780_, v_bkt_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v_size_x27_803_; lean_object* v___x_804_; lean_object* v_buckets_x27_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_802_ = lean_unsigned_to_nat(1u);
v_size_x27_803_ = lean_nat_add(v_size_782_, v___x_802_);
lean_dec(v_size_782_);
lean_inc(v_bkt_800_);
v___x_804_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_804_, 0, v_a_780_);
lean_ctor_set(v___x_804_, 1, v_b_781_);
lean_ctor_set(v___x_804_, 2, v_bkt_800_);
v_buckets_x27_805_ = lean_array_uset(v_buckets_783_, v___x_799_, v___x_804_);
v___x_806_ = lean_unsigned_to_nat(4u);
v___x_807_ = lean_nat_mul(v_size_x27_803_, v___x_806_);
v___x_808_ = lean_unsigned_to_nat(3u);
v___x_809_ = lean_nat_div(v___x_807_, v___x_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_array_get_size(v_buckets_x27_805_);
v___x_811_ = lean_nat_dec_le(v___x_809_, v___x_810_);
lean_dec(v___x_809_);
if (v___x_811_ == 0)
{
lean_object* v_val_812_; lean_object* v___x_814_; 
v_val_812_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_buckets_x27_805_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 1, v_val_812_);
lean_ctor_set(v___x_785_, 0, v_size_x27_803_);
v___x_814_ = v___x_785_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_size_x27_803_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_val_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
else
{
lean_object* v___x_817_; 
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 1, v_buckets_x27_805_);
lean_ctor_set(v___x_785_, 0, v_size_x27_803_);
v___x_817_ = v___x_785_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_size_x27_803_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_buckets_x27_805_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
else
{
lean_object* v___x_819_; lean_object* v_buckets_x27_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
lean_inc(v_bkt_800_);
v___x_819_ = lean_box(0);
v_buckets_x27_820_ = lean_array_uset(v_buckets_783_, v___x_799_, v___x_819_);
v___x_821_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_780_, v_b_781_, v_bkt_800_);
v___x_822_ = lean_array_uset(v_buckets_x27_820_, v___x_799_, v___x_821_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 1, v___x_822_);
v___x_824_ = v___x_785_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_size_782_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(lean_object* v_a_827_, lean_object* v_e_828_, lean_object* v_a_829_){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_831_ = lean_st_ref_take(v_a_827_);
v___x_832_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v___x_831_, v_e_828_, v_a_829_);
v___x_833_ = lean_st_ref_set(v_a_827_, v___x_832_);
v___x_834_ = lean_box(0);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed(lean_object* v_a_835_, lean_object* v_e_836_, lean_object* v_a_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(v_a_835_, v_e_836_, v_a_837_);
lean_dec(v_a_835_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(lean_object* v_fvars_843_, lean_object* v_pre_844_, lean_object* v_post_845_, uint8_t v_usedLetOnly_846_, uint8_t v_skipConstInApp_847_, uint8_t v_skipInstances_848_, lean_object* v_body_849_, lean_object* v_x_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_array_push(v_fvars_843_, v_x_850_);
v___x_858_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_844_, v_post_845_, v_usedLetOnly_846_, v_skipConstInApp_847_, v_skipInstances_848_, v___x_857_, v_body_849_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed(lean_object* v_fvars_859_, lean_object* v_pre_860_, lean_object* v_post_861_, lean_object* v_usedLetOnly_862_, lean_object* v_skipConstInApp_863_, lean_object* v_skipInstances_864_, lean_object* v_body_865_, lean_object* v_x_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
uint8_t v_usedLetOnly_boxed_873_; uint8_t v_skipConstInApp_boxed_874_; uint8_t v_skipInstances_boxed_875_; lean_object* v_res_876_; 
v_usedLetOnly_boxed_873_ = lean_unbox(v_usedLetOnly_862_);
v_skipConstInApp_boxed_874_ = lean_unbox(v_skipConstInApp_863_);
v_skipInstances_boxed_875_ = lean_unbox(v_skipInstances_864_);
v_res_876_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(v_fvars_859_, v_pre_860_, v_post_861_, v_usedLetOnly_boxed_873_, v_skipConstInApp_boxed_874_, v_skipInstances_boxed_875_, v_body_865_, v_x_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(lean_object* v_pre_877_, lean_object* v_post_878_, uint8_t v_usedLetOnly_879_, uint8_t v_skipConstInApp_880_, uint8_t v_skipInstances_881_, lean_object* v_e_882_, lean_object* v_a_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_889_; 
lean_inc_ref(v_post_878_);
lean_inc(v___y_887_);
lean_inc_ref(v___y_886_);
lean_inc(v___y_885_);
lean_inc_ref(v___y_884_);
lean_inc_ref(v_e_882_);
v___x_889_ = lean_apply_6(v_post_878_, v_e_882_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, lean_box(0));
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_908_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_908_ == 0)
{
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_908_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_908_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
switch(lean_obj_tag(v_a_890_))
{
case 0:
{
lean_object* v_e_894_; lean_object* v___x_896_; 
lean_dec_ref(v_e_882_);
lean_dec_ref(v_post_878_);
lean_dec_ref(v_pre_877_);
v_e_894_ = lean_ctor_get(v_a_890_, 0);
lean_inc_ref(v_e_894_);
lean_dec_ref_known(v_a_890_, 1);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v_e_894_);
v___x_896_ = v___x_892_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_e_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
case 1:
{
lean_object* v_e_898_; lean_object* v___x_899_; 
lean_del_object(v___x_892_);
lean_dec_ref(v_e_882_);
v_e_898_ = lean_ctor_get(v_a_890_, 0);
lean_inc_ref(v_e_898_);
lean_dec_ref_known(v_a_890_, 1);
v___x_899_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_877_, v_post_878_, v_usedLetOnly_879_, v_skipConstInApp_880_, v_skipInstances_881_, v_e_898_, v_a_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
return v___x_899_;
}
default: 
{
lean_object* v_e_x3f_900_; 
lean_dec_ref(v_post_878_);
lean_dec_ref(v_pre_877_);
v_e_x3f_900_ = lean_ctor_get(v_a_890_, 0);
lean_inc(v_e_x3f_900_);
lean_dec_ref_known(v_a_890_, 1);
if (lean_obj_tag(v_e_x3f_900_) == 0)
{
lean_object* v___x_902_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v_e_882_);
v___x_902_ = v___x_892_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_e_882_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
else
{
lean_object* v_val_904_; lean_object* v___x_906_; 
lean_dec_ref(v_e_882_);
v_val_904_ = lean_ctor_get(v_e_x3f_900_, 0);
lean_inc(v_val_904_);
lean_dec_ref_known(v_e_x3f_900_, 1);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v_val_904_);
v___x_906_ = v___x_892_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_val_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec_ref(v_e_882_);
lean_dec_ref(v_post_878_);
lean_dec_ref(v_pre_877_);
v_a_909_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_889_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_889_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(lean_object* v_pre_917_, lean_object* v_post_918_, uint8_t v_usedLetOnly_919_, uint8_t v_skipConstInApp_920_, uint8_t v_skipInstances_921_, lean_object* v_fvars_922_, lean_object* v_e_923_, lean_object* v_a_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
if (lean_obj_tag(v_e_923_) == 6)
{
lean_object* v_binderName_930_; lean_object* v_binderType_931_; lean_object* v_body_932_; uint8_t v_binderInfo_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v_binderName_930_ = lean_ctor_get(v_e_923_, 0);
lean_inc(v_binderName_930_);
v_binderType_931_ = lean_ctor_get(v_e_923_, 1);
lean_inc_ref(v_binderType_931_);
v_body_932_ = lean_ctor_get(v_e_923_, 2);
lean_inc_ref(v_body_932_);
v_binderInfo_933_ = lean_ctor_get_uint8(v_e_923_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_923_, 3);
v___x_934_ = lean_expr_instantiate_rev(v_binderType_931_, v_fvars_922_);
lean_dec_ref(v_binderType_931_);
lean_inc_ref(v_post_918_);
lean_inc_ref(v_pre_917_);
v___x_935_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_917_, v_post_918_, v_usedLetOnly_919_, v_skipConstInApp_920_, v_skipInstances_921_, v___x_934_, v_a_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___f_940_; uint8_t v___x_941_; lean_object* v___x_942_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_935_, 1);
v___x_937_ = lean_box(v_usedLetOnly_919_);
v___x_938_ = lean_box(v_skipConstInApp_920_);
v___x_939_ = lean_box(v_skipInstances_921_);
v___f_940_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed), 14, 7);
lean_closure_set(v___f_940_, 0, v_fvars_922_);
lean_closure_set(v___f_940_, 1, v_pre_917_);
lean_closure_set(v___f_940_, 2, v_post_918_);
lean_closure_set(v___f_940_, 3, v___x_937_);
lean_closure_set(v___f_940_, 4, v___x_938_);
lean_closure_set(v___f_940_, 5, v___x_939_);
lean_closure_set(v___f_940_, 6, v_body_932_);
v___x_941_ = 0;
v___x_942_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_930_, v_binderInfo_933_, v_a_936_, v___f_940_, v___x_941_, v_a_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
return v___x_942_;
}
else
{
lean_dec_ref(v_body_932_);
lean_dec(v_binderName_930_);
lean_dec_ref(v_fvars_922_);
lean_dec_ref(v_post_918_);
lean_dec_ref(v_pre_917_);
return v___x_935_;
}
}
else
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_expr_instantiate_rev(v_e_923_, v_fvars_922_);
lean_dec_ref(v_e_923_);
lean_inc_ref(v_post_918_);
lean_inc_ref(v_pre_917_);
v___x_944_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_917_, v_post_918_, v_usedLetOnly_919_, v_skipConstInApp_920_, v_skipInstances_921_, v___x_943_, v_a_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; uint8_t v___x_946_; uint8_t v___x_947_; uint8_t v___x_948_; lean_object* v___x_949_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_a_945_);
lean_dec_ref_known(v___x_944_, 1);
v___x_946_ = 0;
v___x_947_ = 1;
v___x_948_ = 1;
v___x_949_ = l_Lean_Meta_mkLambdaFVars(v_fvars_922_, v_a_945_, v___x_946_, v_usedLetOnly_919_, v___x_946_, v___x_947_, v___x_948_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec_ref(v_fvars_922_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_951_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
v___x_951_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_917_, v_post_918_, v_usedLetOnly_919_, v_skipConstInApp_920_, v_skipInstances_921_, v_a_950_, v_a_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
return v___x_951_;
}
else
{
lean_dec_ref(v_post_918_);
lean_dec_ref(v_pre_917_);
return v___x_949_;
}
}
else
{
lean_dec_ref(v_fvars_922_);
lean_dec_ref(v_post_918_);
lean_dec_ref(v_pre_917_);
return v___x_944_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(lean_object* v_fvars_952_, lean_object* v_pre_953_, lean_object* v_post_954_, uint8_t v_usedLetOnly_955_, uint8_t v_skipConstInApp_956_, uint8_t v_skipInstances_957_, lean_object* v_body_958_, lean_object* v_x_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_array_push(v_fvars_952_, v_x_959_);
v___x_967_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_953_, v_post_954_, v_usedLetOnly_955_, v_skipConstInApp_956_, v_skipInstances_957_, v___x_966_, v_body_958_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_968_, lean_object* v_pre_969_, lean_object* v_post_970_, lean_object* v_usedLetOnly_971_, lean_object* v_skipConstInApp_972_, lean_object* v_skipInstances_973_, lean_object* v_body_974_, lean_object* v_x_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
uint8_t v_usedLetOnly_boxed_982_; uint8_t v_skipConstInApp_boxed_983_; uint8_t v_skipInstances_boxed_984_; lean_object* v_res_985_; 
v_usedLetOnly_boxed_982_ = lean_unbox(v_usedLetOnly_971_);
v_skipConstInApp_boxed_983_ = lean_unbox(v_skipConstInApp_972_);
v_skipInstances_boxed_984_ = lean_unbox(v_skipInstances_973_);
v_res_985_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(v_fvars_968_, v_pre_969_, v_post_970_, v_usedLetOnly_boxed_982_, v_skipConstInApp_boxed_983_, v_skipInstances_boxed_984_, v_body_974_, v_x_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(lean_object* v_pre_986_, lean_object* v_post_987_, uint8_t v_usedLetOnly_988_, uint8_t v_skipConstInApp_989_, uint8_t v_skipInstances_990_, lean_object* v_fvars_991_, lean_object* v_e_992_, lean_object* v_a_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
if (lean_obj_tag(v_e_992_) == 8)
{
lean_object* v_declName_999_; lean_object* v_type_1000_; lean_object* v_value_1001_; lean_object* v_body_1002_; uint8_t v_nondep_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v_declName_999_ = lean_ctor_get(v_e_992_, 0);
lean_inc(v_declName_999_);
v_type_1000_ = lean_ctor_get(v_e_992_, 1);
lean_inc_ref(v_type_1000_);
v_value_1001_ = lean_ctor_get(v_e_992_, 2);
lean_inc_ref(v_value_1001_);
v_body_1002_ = lean_ctor_get(v_e_992_, 3);
lean_inc_ref(v_body_1002_);
v_nondep_1003_ = lean_ctor_get_uint8(v_e_992_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_992_, 4);
v___x_1004_ = lean_expr_instantiate_rev(v_type_1000_, v_fvars_991_);
lean_dec_ref(v_type_1000_);
lean_inc_ref(v_post_987_);
lean_inc_ref(v_pre_986_);
v___x_1005_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_986_, v_post_987_, v_usedLetOnly_988_, v_skipConstInApp_989_, v_skipInstances_990_, v___x_1004_, v_a_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___x_1007_ = lean_expr_instantiate_rev(v_value_1001_, v_fvars_991_);
lean_dec_ref(v_value_1001_);
lean_inc_ref(v_post_987_);
lean_inc_ref(v_pre_986_);
v___x_1008_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_986_, v_post_987_, v_usedLetOnly_988_, v_skipConstInApp_989_, v_skipInstances_990_, v___x_1007_, v_a_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___f_1013_; uint8_t v___x_1014_; lean_object* v___x_1015_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1010_ = lean_box(v_usedLetOnly_988_);
v___x_1011_ = lean_box(v_skipConstInApp_989_);
v___x_1012_ = lean_box(v_skipInstances_990_);
v___f_1013_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1013_, 0, v_fvars_991_);
lean_closure_set(v___f_1013_, 1, v_pre_986_);
lean_closure_set(v___f_1013_, 2, v_post_987_);
lean_closure_set(v___f_1013_, 3, v___x_1010_);
lean_closure_set(v___f_1013_, 4, v___x_1011_);
lean_closure_set(v___f_1013_, 5, v___x_1012_);
lean_closure_set(v___f_1013_, 6, v_body_1002_);
v___x_1014_ = 0;
v___x_1015_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_declName_999_, v_a_1006_, v_a_1009_, v___f_1013_, v_nondep_1003_, v___x_1014_, v_a_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
return v___x_1015_;
}
else
{
lean_dec(v_a_1006_);
lean_dec_ref(v_body_1002_);
lean_dec(v_declName_999_);
lean_dec_ref(v_fvars_991_);
lean_dec_ref(v_post_987_);
lean_dec_ref(v_pre_986_);
return v___x_1008_;
}
}
else
{
lean_dec_ref(v_body_1002_);
lean_dec_ref(v_value_1001_);
lean_dec(v_declName_999_);
lean_dec_ref(v_fvars_991_);
lean_dec_ref(v_post_987_);
lean_dec_ref(v_pre_986_);
return v___x_1005_;
}
}
else
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_expr_instantiate_rev(v_e_992_, v_fvars_991_);
lean_dec_ref(v_e_992_);
lean_inc_ref(v_post_987_);
lean_inc_ref(v_pre_986_);
v___x_1017_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_986_, v_post_987_, v_usedLetOnly_988_, v_skipConstInApp_989_, v_skipInstances_990_, v___x_1016_, v_a_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; uint8_t v___x_1019_; uint8_t v___x_1020_; lean_object* v___x_1021_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1017_, 1);
v___x_1019_ = 0;
v___x_1020_ = 1;
v___x_1021_ = l_Lean_Meta_mkLetFVars(v_fvars_991_, v_a_1018_, v_usedLetOnly_988_, v___x_1019_, v___x_1020_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec_ref(v_fvars_991_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v___x_1023_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_986_, v_post_987_, v_usedLetOnly_988_, v_skipConstInApp_989_, v_skipInstances_990_, v_a_1022_, v_a_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
return v___x_1023_;
}
else
{
lean_dec_ref(v_post_987_);
lean_dec_ref(v_pre_986_);
return v___x_1021_;
}
}
else
{
lean_dec_ref(v_fvars_991_);
lean_dec_ref(v_post_987_);
lean_dec_ref(v_pre_986_);
return v___x_1017_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(lean_object* v_pre_1024_, lean_object* v_post_1025_, uint8_t v_usedLetOnly_1026_, uint8_t v_skipConstInApp_1027_, uint8_t v_skipInstances_1028_, size_t v_sz_1029_, size_t v_i_1030_, lean_object* v_bs_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
uint8_t v___x_1038_; 
v___x_1038_ = lean_usize_dec_lt(v_i_1030_, v_sz_1029_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; 
lean_dec_ref(v_post_1025_);
lean_dec_ref(v_pre_1024_);
v___x_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1039_, 0, v_bs_1031_);
return v___x_1039_;
}
else
{
lean_object* v_v_1040_; lean_object* v___x_1041_; 
v_v_1040_ = lean_array_uget_borrowed(v_bs_1031_, v_i_1030_);
lean_inc(v_v_1040_);
lean_inc_ref(v_post_1025_);
lean_inc_ref(v_pre_1024_);
v___x_1041_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1024_, v_post_1025_, v_usedLetOnly_1026_, v_skipConstInApp_1027_, v_skipInstances_1028_, v_v_1040_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1043_; lean_object* v_bs_x27_1044_; size_t v___x_1045_; size_t v___x_1046_; lean_object* v___x_1047_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref_known(v___x_1041_, 1);
v___x_1043_ = lean_unsigned_to_nat(0u);
v_bs_x27_1044_ = lean_array_uset(v_bs_1031_, v_i_1030_, v___x_1043_);
v___x_1045_ = ((size_t)1ULL);
v___x_1046_ = lean_usize_add(v_i_1030_, v___x_1045_);
v___x_1047_ = lean_array_uset(v_bs_x27_1044_, v_i_1030_, v_a_1042_);
v_i_1030_ = v___x_1046_;
v_bs_1031_ = v___x_1047_;
goto _start;
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec_ref(v_bs_1031_);
lean_dec_ref(v_post_1025_);
lean_dec_ref(v_pre_1024_);
v_a_1049_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1041_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1041_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(lean_object* v_pre_1057_, lean_object* v_post_1058_, uint8_t v_usedLetOnly_1059_, uint8_t v_skipConstInApp_1060_, uint8_t v_skipInstances_1061_, lean_object* v___x_1062_, lean_object* v___y_1063_, lean_object* v_b_1064_, lean_object* v_a_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1057_, v_post_1058_, v_usedLetOnly_1059_, v_skipConstInApp_1060_, v_skipInstances_1061_, v___x_1062_, v___y_1063_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1081_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1074_ = v___x_1071_;
v_isShared_1075_ = v_isSharedCheck_1081_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1081_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1076_ = lean_array_fset(v_b_1064_, v_a_1065_, v_a_1072_);
v___x_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v___x_1077_);
v___x_1079_ = v___x_1074_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec_ref(v_b_1064_);
v_a_1082_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1071_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1071_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed(lean_object* v_pre_1090_, lean_object* v_post_1091_, lean_object* v_usedLetOnly_1092_, lean_object* v_skipConstInApp_1093_, lean_object* v_skipInstances_1094_, lean_object* v___x_1095_, lean_object* v___y_1096_, lean_object* v_b_1097_, lean_object* v_a_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
uint8_t v_usedLetOnly_boxed_1104_; uint8_t v_skipConstInApp_boxed_1105_; uint8_t v_skipInstances_boxed_1106_; lean_object* v_res_1107_; 
v_usedLetOnly_boxed_1104_ = lean_unbox(v_usedLetOnly_1092_);
v_skipConstInApp_boxed_1105_ = lean_unbox(v_skipConstInApp_1093_);
v_skipInstances_boxed_1106_ = lean_unbox(v_skipInstances_1094_);
v_res_1107_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(v_pre_1090_, v_post_1091_, v_usedLetOnly_boxed_1104_, v_skipConstInApp_boxed_1105_, v_skipInstances_boxed_1106_, v___x_1095_, v___y_1096_, v_b_1097_, v_a_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v_a_1098_);
lean_dec(v___y_1096_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(lean_object* v_upperBound_1108_, lean_object* v___x_1109_, lean_object* v_pre_1110_, lean_object* v_post_1111_, uint8_t v_usedLetOnly_1112_, uint8_t v_skipConstInApp_1113_, uint8_t v_skipInstances_1114_, lean_object* v_a_1115_, lean_object* v_b_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v___y_1124_; uint8_t v___x_1147_; 
v___x_1147_ = lean_nat_dec_lt(v_a_1115_, v_upperBound_1108_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; 
lean_dec(v_a_1115_);
lean_dec_ref(v_post_1111_);
lean_dec_ref(v_pre_1110_);
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_b_1116_);
return v___x_1148_;
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1149_ = lean_array_fget_borrowed(v_b_1116_, v_a_1115_);
v___x_1150_ = lean_array_get_size(v___x_1109_);
v___x_1151_ = lean_nat_dec_lt(v_a_1115_, v___x_1150_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___f_1155_; 
lean_inc(v___x_1149_);
v___x_1152_ = lean_box(v_usedLetOnly_1112_);
v___x_1153_ = lean_box(v_skipConstInApp_1113_);
v___x_1154_ = lean_box(v_skipInstances_1114_);
lean_inc(v_a_1115_);
lean_inc(v___y_1117_);
lean_inc_ref(v_post_1111_);
lean_inc_ref(v_pre_1110_);
v___f_1155_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1155_, 0, v_pre_1110_);
lean_closure_set(v___f_1155_, 1, v_post_1111_);
lean_closure_set(v___f_1155_, 2, v___x_1152_);
lean_closure_set(v___f_1155_, 3, v___x_1153_);
lean_closure_set(v___f_1155_, 4, v___x_1154_);
lean_closure_set(v___f_1155_, 5, v___x_1149_);
lean_closure_set(v___f_1155_, 6, v___y_1117_);
lean_closure_set(v___f_1155_, 7, v_b_1116_);
lean_closure_set(v___f_1155_, 8, v_a_1115_);
v___y_1124_ = v___f_1155_;
goto v___jp_1123_;
}
else
{
lean_object* v___x_1156_; uint8_t v_isInstance_1157_; 
v___x_1156_ = lean_array_fget_borrowed(v___x_1109_, v_a_1115_);
v_isInstance_1157_ = lean_ctor_get_uint8(v___x_1156_, sizeof(void*)*1 + 4);
if (v_isInstance_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___f_1161_; 
lean_inc(v___x_1149_);
v___x_1158_ = lean_box(v_usedLetOnly_1112_);
v___x_1159_ = lean_box(v_skipConstInApp_1113_);
v___x_1160_ = lean_box(v_skipInstances_1114_);
lean_inc(v_a_1115_);
lean_inc(v___y_1117_);
lean_inc_ref(v_post_1111_);
lean_inc_ref(v_pre_1110_);
v___f_1161_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1161_, 0, v_pre_1110_);
lean_closure_set(v___f_1161_, 1, v_post_1111_);
lean_closure_set(v___f_1161_, 2, v___x_1158_);
lean_closure_set(v___f_1161_, 3, v___x_1159_);
lean_closure_set(v___f_1161_, 4, v___x_1160_);
lean_closure_set(v___f_1161_, 5, v___x_1149_);
lean_closure_set(v___f_1161_, 6, v___y_1117_);
lean_closure_set(v___f_1161_, 7, v_b_1116_);
lean_closure_set(v___f_1161_, 8, v_a_1115_);
v___y_1124_ = v___f_1161_;
goto v___jp_1123_;
}
else
{
lean_object* v___x_1162_; lean_object* v___f_1163_; 
v___x_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1162_, 0, v_b_1116_);
v___f_1163_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1163_, 0, v___x_1162_);
v___y_1124_ = v___f_1163_;
goto v___jp_1123_;
}
}
}
v___jp_1123_:
{
lean_object* v___x_1125_; 
lean_inc(v___y_1121_);
lean_inc_ref(v___y_1120_);
lean_inc(v___y_1119_);
lean_inc_ref(v___y_1118_);
v___x_1125_ = lean_apply_5(v___y_1124_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, lean_box(0));
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1138_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1128_ = v___x_1125_;
v_isShared_1129_ = v_isSharedCheck_1138_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1125_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1138_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
if (lean_obj_tag(v_a_1126_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1132_; 
lean_dec(v_a_1115_);
lean_dec_ref(v_post_1111_);
lean_dec_ref(v_pre_1110_);
v_a_1130_ = lean_ctor_get(v_a_1126_, 0);
lean_inc(v_a_1130_);
lean_dec_ref_known(v_a_1126_, 1);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v_a_1130_);
v___x_1132_ = v___x_1128_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_del_object(v___x_1128_);
v_a_1134_ = lean_ctor_get(v_a_1126_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v_a_1126_, 1);
v___x_1135_ = lean_unsigned_to_nat(1u);
v___x_1136_ = lean_nat_add(v_a_1115_, v___x_1135_);
lean_dec(v_a_1115_);
v_a_1115_ = v___x_1136_;
v_b_1116_ = v_a_1134_;
goto _start;
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec(v_a_1115_);
lean_dec_ref(v_post_1111_);
lean_dec_ref(v_pre_1110_);
v_a_1139_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1125_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1125_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(uint8_t v_skipInstances_1164_, lean_object* v_pre_1165_, lean_object* v_post_1166_, uint8_t v_usedLetOnly_1167_, uint8_t v_skipConstInApp_1168_, lean_object* v_x_1169_, lean_object* v_x_1170_, lean_object* v_x_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_f_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; 
if (lean_obj_tag(v_x_1169_) == 5)
{
lean_object* v_fn_1227_; lean_object* v_arg_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v_fn_1227_ = lean_ctor_get(v_x_1169_, 0);
lean_inc_ref(v_fn_1227_);
v_arg_1228_ = lean_ctor_get(v_x_1169_, 1);
lean_inc_ref(v_arg_1228_);
lean_dec_ref_known(v_x_1169_, 2);
v___x_1229_ = lean_array_set(v_x_1170_, v_x_1171_, v_arg_1228_);
v___x_1230_ = lean_unsigned_to_nat(1u);
v___x_1231_ = lean_nat_sub(v_x_1171_, v___x_1230_);
lean_dec(v_x_1171_);
v_x_1169_ = v_fn_1227_;
v_x_1170_ = v___x_1229_;
v_x_1171_ = v___x_1231_;
goto _start;
}
else
{
lean_dec(v_x_1171_);
if (v_skipConstInApp_1168_ == 0)
{
goto v___jp_1224_;
}
else
{
uint8_t v___x_1233_; 
v___x_1233_ = l_Lean_Expr_isConst(v_x_1169_);
if (v___x_1233_ == 0)
{
goto v___jp_1224_;
}
else
{
v_f_1179_ = v_x_1169_;
v___y_1180_ = v___y_1172_;
v___y_1181_ = v___y_1173_;
v___y_1182_ = v___y_1174_;
v___y_1183_ = v___y_1175_;
v___y_1184_ = v___y_1176_;
goto v___jp_1178_;
}
}
}
v___jp_1178_:
{
if (v_skipInstances_1164_ == 0)
{
size_t v_sz_1185_; size_t v___x_1186_; lean_object* v___x_1187_; 
v_sz_1185_ = lean_array_size(v_x_1170_);
v___x_1186_ = ((size_t)0ULL);
lean_inc_ref(v_post_1166_);
lean_inc_ref(v_pre_1165_);
v___x_1187_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_1165_, v_post_1166_, v_usedLetOnly_1167_, v_skipConstInApp_1168_, v_skipInstances_1164_, v_sz_1185_, v___x_1186_, v_x_1170_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1187_, 1);
v___x_1189_ = l_Lean_mkAppN(v_f_1179_, v_a_1188_);
lean_dec(v_a_1188_);
v___x_1190_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1165_, v_post_1166_, v_usedLetOnly_1167_, v_skipConstInApp_1168_, v_skipInstances_1164_, v___x_1189_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
return v___x_1190_;
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec_ref(v_f_1179_);
lean_dec_ref(v_post_1166_);
lean_dec_ref(v_pre_1165_);
v_a_1191_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1187_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1187_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_array_get_size(v_x_1170_);
lean_inc_ref(v_f_1179_);
v___x_1200_ = l_Lean_Meta_getFunInfoNArgs(v_f_1179_, v___x_1199_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v_paramInfo_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1201_);
lean_dec_ref_known(v___x_1200_, 1);
v_paramInfo_1202_ = lean_ctor_get(v_a_1201_, 0);
lean_inc_ref(v_paramInfo_1202_);
lean_dec(v_a_1201_);
v___x_1203_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1166_);
lean_inc_ref(v_pre_1165_);
v___x_1204_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v___x_1199_, v_paramInfo_1202_, v_pre_1165_, v_post_1166_, v_usedLetOnly_1167_, v_skipConstInApp_1168_, v_skipInstances_1164_, v___x_1203_, v_x_1170_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec_ref(v_paramInfo_1202_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_a_1205_);
lean_dec_ref_known(v___x_1204_, 1);
v___x_1206_ = l_Lean_mkAppN(v_f_1179_, v_a_1205_);
lean_dec(v_a_1205_);
v___x_1207_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1165_, v_post_1166_, v_usedLetOnly_1167_, v_skipConstInApp_1168_, v_skipInstances_1164_, v___x_1206_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
return v___x_1207_;
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_dec_ref(v_f_1179_);
lean_dec_ref(v_post_1166_);
lean_dec_ref(v_pre_1165_);
v_a_1208_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1204_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1204_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec_ref(v_f_1179_);
lean_dec_ref(v_x_1170_);
lean_dec_ref(v_post_1166_);
lean_dec_ref(v_pre_1165_);
v_a_1216_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1200_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1200_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
v___jp_1224_:
{
lean_object* v___x_1225_; 
lean_inc_ref(v_post_1166_);
lean_inc_ref(v_pre_1165_);
v___x_1225_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1165_, v_post_1166_, v_usedLetOnly_1167_, v_skipConstInApp_1168_, v_skipInstances_1164_, v_x_1169_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref_known(v___x_1225_, 1);
v_f_1179_ = v_a_1226_;
v___y_1180_ = v___y_1172_;
v___y_1181_ = v___y_1173_;
v___y_1182_ = v___y_1174_;
v___y_1183_ = v___y_1175_;
v___y_1184_ = v___y_1176_;
goto v___jp_1178_;
}
else
{
lean_dec_ref(v_x_1170_);
lean_dec_ref(v_post_1166_);
lean_dec_ref(v_pre_1165_);
return v___x_1225_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(lean_object* v___x_1234_, lean_object* v_pre_1235_, lean_object* v_e_1236_, lean_object* v_post_1237_, uint8_t v_usedLetOnly_1238_, uint8_t v_skipConstInApp_1239_, uint8_t v_skipInstances_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Lean_Core_checkSystem(v___x_1234_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v___x_1248_; 
lean_dec_ref_known(v___x_1247_, 1);
lean_inc_ref(v_pre_1235_);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc_ref(v_e_1236_);
v___x_1248_ = lean_apply_6(v_pre_1235_, v_e_1236_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, lean_box(0));
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1297_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1297_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1297_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___y_1254_; 
switch(lean_obj_tag(v_a_1249_))
{
case 0:
{
lean_object* v_e_1289_; lean_object* v___x_1291_; 
lean_dec_ref(v_post_1237_);
lean_dec_ref(v_e_1236_);
lean_dec_ref(v_pre_1235_);
v_e_1289_ = lean_ctor_get(v_a_1249_, 0);
lean_inc_ref(v_e_1289_);
lean_dec_ref_known(v_a_1249_, 1);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v_e_1289_);
v___x_1291_ = v___x_1251_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_e_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
case 1:
{
lean_object* v_e_1293_; lean_object* v___x_1294_; 
lean_del_object(v___x_1251_);
lean_dec_ref(v_e_1236_);
v_e_1293_ = lean_ctor_get(v_a_1249_, 0);
lean_inc_ref(v_e_1293_);
lean_dec_ref_known(v_a_1249_, 1);
v___x_1294_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1235_, v_post_1237_, v_usedLetOnly_1238_, v_skipConstInApp_1239_, v_skipInstances_1240_, v_e_1293_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1294_;
}
default: 
{
lean_object* v_e_x3f_1295_; 
lean_del_object(v___x_1251_);
v_e_x3f_1295_ = lean_ctor_get(v_a_1249_, 0);
lean_inc(v_e_x3f_1295_);
lean_dec_ref_known(v_a_1249_, 1);
if (lean_obj_tag(v_e_x3f_1295_) == 0)
{
v___y_1254_ = v_e_1236_;
goto v___jp_1253_;
}
else
{
lean_object* v_val_1296_; 
lean_dec_ref(v_e_1236_);
v_val_1296_ = lean_ctor_get(v_e_x3f_1295_, 0);
lean_inc(v_val_1296_);
lean_dec_ref_known(v_e_x3f_1295_, 1);
v___y_1254_ = v_val_1296_;
goto v___jp_1253_;
}
}
}
v___jp_1253_:
{
switch(lean_obj_tag(v___y_1254_))
{
case 7:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1256_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1235_, v_post_1237_, v_usedLetOnly_1238_, v_skipConstInApp_1239_, v_skipInstances_1240_, v___x_1255_, v___y_1254_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1256_;
}
case 6:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1258_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1235_, v_post_1237_, v_usedLetOnly_1238_, v_skipConstInApp_1239_, v_skipInstances_1240_, v___x_1257_, v___y_1254_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1258_;
}
case 8:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1260_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1235_, v_post_1237_, v_usedLetOnly_1238_, v_skipConstInApp_1239_, v_skipInstances_1240_, v___x_1259_, v___y_1254_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1260_;
}
case 5:
{
lean_object* v_dummy_1261_; lean_object* v_nargs_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v_dummy_1261_ = lean_obj_once(&l_Lean_Elab_WF_withAppN___closed__0, &l_Lean_Elab_WF_withAppN___closed__0_once, _init_l_Lean_Elab_WF_withAppN___closed__0);
v_nargs_1262_ = l_Lean_Expr_getAppNumArgs(v___y_1254_);
lean_inc(v_nargs_1262_);
v___x_1263_ = lean_mk_array(v_nargs_1262_, v_dummy_1261_);
v___x_1264_ = lean_unsigned_to_nat(1u);
v___x_1265_ = lean_nat_sub(v_nargs_1262_, v___x_1264_);
lean_dec(v_nargs_1262_);
v___x_1266_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_1240_, v_pre_1235_, v_post_1237_, v_usedLetOnly_1238_, v_skipConstInApp_1239_, v___y_1254_, v___x_1263_, v___x_1265_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1266_;
}
case 10:
{
lean_object* v_data_1267_; lean_object* v_expr_1268_; lean_object* v___x_1269_; 
v_data_1267_ = lean_ctor_get(v___y_1254_, 0);
v_expr_1268_ = lean_ctor_get(v___y_1254_, 1);
lean_inc_ref(v_expr_1268_);
lean_inc_ref(v_post_1237_);
lean_inc_ref(v_pre_1235_);
v___x_1269_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1235_, v_post_1237_, v_usedLetOnly_1238_, v_skipConstInApp_1239_, v_skipInstances_1240_, v_expr_1268_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; size_t v___x_1271_; size_t v___x_1272_; uint8_t v___x_1273_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1269_, 1);
v___x_1271_ = lean_ptr_addr(v_expr_1268_);
v___x_1272_ = lean_ptr_addr(v_a_1270_);
v___x_1273_ = lean_usize_dec_eq(v___x_1271_, v___x_1272_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
lean_inc(v_data_1267_);
lean_dec_ref_known(v___y_1254_, 2);
v___x_1274_ = l_Lean_Expr_mdata___override(v_data_1267_, v_a_1270_);
v___x_1275_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1235_, v_post_1237_, v_usedLetOnly_1238_, v_skipConstInApp_1239_, v_skipInstances_1240_, v___x_1274_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1275_;
}
else
{
lean_object* v___x_1276_; 
lean_dec(v_a_1270_);
v___x_1276_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1235_, v_post_1237_, v_usedLetOnly_1238_, v_skipConstInApp_1239_, v_skipInstances_1240_, v___y_1254_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1276_;
}
}
else
{
lean_dec_ref_known(v___y_1254_, 2);
lean_dec_ref(v_post_1237_);
lean_dec_ref(v_pre_1235_);
return v___x_1269_;
}
}
case 11:
{
lean_object* v_typeName_1277_; lean_object* v_idx_1278_; lean_object* v_struct_1279_; lean_object* v___x_1280_; 
v_typeName_1277_ = lean_ctor_get(v___y_1254_, 0);
v_idx_1278_ = lean_ctor_get(v___y_1254_, 1);
v_struct_1279_ = lean_ctor_get(v___y_1254_, 2);
lean_inc_ref(v_struct_1279_);
lean_inc_ref(v_post_1237_);
lean_inc_ref(v_pre_1235_);
v___x_1280_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1235_, v_post_1237_, v_usedLetOnly_1238_, v_skipConstInApp_1239_, v_skipInstances_1240_, v_struct_1279_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; size_t v___x_1282_; size_t v___x_1283_; uint8_t v___x_1284_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1280_, 1);
v___x_1282_ = lean_ptr_addr(v_struct_1279_);
v___x_1283_ = lean_ptr_addr(v_a_1281_);
v___x_1284_ = lean_usize_dec_eq(v___x_1282_, v___x_1283_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
lean_inc(v_idx_1278_);
lean_inc(v_typeName_1277_);
lean_dec_ref_known(v___y_1254_, 3);
v___x_1285_ = l_Lean_Expr_proj___override(v_typeName_1277_, v_idx_1278_, v_a_1281_);
v___x_1286_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1235_, v_post_1237_, v_usedLetOnly_1238_, v_skipConstInApp_1239_, v_skipInstances_1240_, v___x_1285_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1286_;
}
else
{
lean_object* v___x_1287_; 
lean_dec(v_a_1281_);
v___x_1287_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1235_, v_post_1237_, v_usedLetOnly_1238_, v_skipConstInApp_1239_, v_skipInstances_1240_, v___y_1254_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1287_;
}
}
else
{
lean_dec_ref_known(v___y_1254_, 3);
lean_dec_ref(v_post_1237_);
lean_dec_ref(v_pre_1235_);
return v___x_1280_;
}
}
default: 
{
lean_object* v___x_1288_; 
v___x_1288_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1235_, v_post_1237_, v_usedLetOnly_1238_, v_skipConstInApp_1239_, v_skipInstances_1240_, v___y_1254_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1288_;
}
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec_ref(v_post_1237_);
lean_dec_ref(v_e_1236_);
lean_dec_ref(v_pre_1235_);
v_a_1298_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1248_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1248_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec_ref(v_post_1237_);
lean_dec_ref(v_e_1236_);
lean_dec_ref(v_pre_1235_);
v_a_1306_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1247_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1247_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed(lean_object* v___x_1314_, lean_object* v_pre_1315_, lean_object* v_e_1316_, lean_object* v_post_1317_, lean_object* v_usedLetOnly_1318_, lean_object* v_skipConstInApp_1319_, lean_object* v_skipInstances_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
uint8_t v_usedLetOnly_boxed_1327_; uint8_t v_skipConstInApp_boxed_1328_; uint8_t v_skipInstances_boxed_1329_; lean_object* v_res_1330_; 
v_usedLetOnly_boxed_1327_ = lean_unbox(v_usedLetOnly_1318_);
v_skipConstInApp_boxed_1328_ = lean_unbox(v_skipConstInApp_1319_);
v_skipInstances_boxed_1329_ = lean_unbox(v_skipInstances_1320_);
v_res_1330_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(v___x_1314_, v_pre_1315_, v_e_1316_, v_post_1317_, v_usedLetOnly_boxed_1327_, v_skipConstInApp_boxed_1328_, v_skipInstances_boxed_1329_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(lean_object* v_pre_1331_, lean_object* v_post_1332_, uint8_t v_usedLetOnly_1333_, uint8_t v_skipConstInApp_1334_, uint8_t v_skipInstances_1335_, lean_object* v_e_1336_, lean_object* v_a_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
lean_inc(v_a_1337_);
v___x_1343_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1343_, 0, lean_box(0));
lean_closure_set(v___x_1343_, 1, lean_box(0));
lean_closure_set(v___x_1343_, 2, v_a_1337_);
v___x_1344_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___x_1343_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1379_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1379_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1379_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_a_1345_, v_e_1336_);
lean_dec(v_a_1345_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___f_1354_; lean_object* v___x_1355_; 
lean_del_object(v___x_1347_);
v___x_1350_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0));
v___x_1351_ = lean_box(v_usedLetOnly_1333_);
v___x_1352_ = lean_box(v_skipConstInApp_1334_);
v___x_1353_ = lean_box(v_skipInstances_1335_);
lean_inc_ref(v_e_1336_);
v___f_1354_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed), 13, 7);
lean_closure_set(v___f_1354_, 0, v___x_1350_);
lean_closure_set(v___f_1354_, 1, v_pre_1331_);
lean_closure_set(v___f_1354_, 2, v_e_1336_);
lean_closure_set(v___f_1354_, 3, v_post_1332_);
lean_closure_set(v___f_1354_, 4, v___x_1351_);
lean_closure_set(v___f_1354_, 5, v___x_1352_);
lean_closure_set(v___f_1354_, 6, v___x_1353_);
v___x_1355_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v___f_1354_, v_a_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___f_1357_; lean_object* v___x_1358_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc_n(v_a_1356_, 2);
lean_dec_ref_known(v___x_1355_, 1);
lean_inc(v_a_1337_);
v___f_1357_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1357_, 0, v_a_1337_);
lean_closure_set(v___f_1357_, 1, v_e_1336_);
lean_closure_set(v___f_1357_, 2, v_a_1356_);
v___x_1358_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___f_1357_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1365_ == 0)
{
lean_object* v_unused_1366_; 
v_unused_1366_ = lean_ctor_get(v___x_1358_, 0);
lean_dec(v_unused_1366_);
v___x_1360_ = v___x_1358_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_dec(v___x_1358_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v_a_1356_);
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1356_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec(v_a_1356_);
v_a_1367_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1358_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1358_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
else
{
lean_dec_ref(v_e_1336_);
return v___x_1355_;
}
}
else
{
lean_object* v_val_1375_; lean_object* v___x_1377_; 
lean_dec_ref(v_e_1336_);
lean_dec_ref(v_post_1332_);
lean_dec_ref(v_pre_1331_);
v_val_1375_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_val_1375_);
lean_dec_ref_known(v___x_1349_, 1);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v_val_1375_);
v___x_1377_ = v___x_1347_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_val_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec_ref(v_e_1336_);
lean_dec_ref(v_post_1332_);
lean_dec_ref(v_pre_1331_);
v_a_1380_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1344_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1344_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed(lean_object* v_fvars_1388_, lean_object* v_pre_1389_, lean_object* v_post_1390_, lean_object* v_usedLetOnly_1391_, lean_object* v_skipConstInApp_1392_, lean_object* v_skipInstances_1393_, lean_object* v_body_1394_, lean_object* v_x_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
uint8_t v_usedLetOnly_boxed_1402_; uint8_t v_skipConstInApp_boxed_1403_; uint8_t v_skipInstances_boxed_1404_; lean_object* v_res_1405_; 
v_usedLetOnly_boxed_1402_ = lean_unbox(v_usedLetOnly_1391_);
v_skipConstInApp_boxed_1403_ = lean_unbox(v_skipConstInApp_1392_);
v_skipInstances_boxed_1404_ = lean_unbox(v_skipInstances_1393_);
v_res_1405_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(v_fvars_1388_, v_pre_1389_, v_post_1390_, v_usedLetOnly_boxed_1402_, v_skipConstInApp_boxed_1403_, v_skipInstances_boxed_1404_, v_body_1394_, v_x_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(lean_object* v_pre_1406_, lean_object* v_post_1407_, uint8_t v_usedLetOnly_1408_, uint8_t v_skipConstInApp_1409_, uint8_t v_skipInstances_1410_, lean_object* v_fvars_1411_, lean_object* v_e_1412_, lean_object* v_a_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
if (lean_obj_tag(v_e_1412_) == 7)
{
lean_object* v_binderName_1419_; lean_object* v_binderType_1420_; lean_object* v_body_1421_; uint8_t v_binderInfo_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v_binderName_1419_ = lean_ctor_get(v_e_1412_, 0);
lean_inc(v_binderName_1419_);
v_binderType_1420_ = lean_ctor_get(v_e_1412_, 1);
lean_inc_ref(v_binderType_1420_);
v_body_1421_ = lean_ctor_get(v_e_1412_, 2);
lean_inc_ref(v_body_1421_);
v_binderInfo_1422_ = lean_ctor_get_uint8(v_e_1412_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1412_, 3);
v___x_1423_ = lean_expr_instantiate_rev(v_binderType_1420_, v_fvars_1411_);
lean_dec_ref(v_binderType_1420_);
lean_inc_ref(v_post_1407_);
lean_inc_ref(v_pre_1406_);
v___x_1424_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1406_, v_post_1407_, v_usedLetOnly_1408_, v_skipConstInApp_1409_, v_skipInstances_1410_, v___x_1423_, v_a_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___f_1429_; uint8_t v___x_1430_; lean_object* v___x_1431_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v___x_1426_ = lean_box(v_usedLetOnly_1408_);
v___x_1427_ = lean_box(v_skipConstInApp_1409_);
v___x_1428_ = lean_box(v_skipInstances_1410_);
v___f_1429_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1429_, 0, v_fvars_1411_);
lean_closure_set(v___f_1429_, 1, v_pre_1406_);
lean_closure_set(v___f_1429_, 2, v_post_1407_);
lean_closure_set(v___f_1429_, 3, v___x_1426_);
lean_closure_set(v___f_1429_, 4, v___x_1427_);
lean_closure_set(v___f_1429_, 5, v___x_1428_);
lean_closure_set(v___f_1429_, 6, v_body_1421_);
v___x_1430_ = 0;
v___x_1431_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_1419_, v_binderInfo_1422_, v_a_1425_, v___f_1429_, v___x_1430_, v_a_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
return v___x_1431_;
}
else
{
lean_dec_ref(v_body_1421_);
lean_dec(v_binderName_1419_);
lean_dec_ref(v_fvars_1411_);
lean_dec_ref(v_post_1407_);
lean_dec_ref(v_pre_1406_);
return v___x_1424_;
}
}
else
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = lean_expr_instantiate_rev(v_e_1412_, v_fvars_1411_);
lean_dec_ref(v_e_1412_);
lean_inc_ref(v_post_1407_);
lean_inc_ref(v_pre_1406_);
v___x_1433_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1406_, v_post_1407_, v_usedLetOnly_1408_, v_skipConstInApp_1409_, v_skipInstances_1410_, v___x_1432_, v_a_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; uint8_t v___x_1435_; uint8_t v___x_1436_; uint8_t v___x_1437_; lean_object* v___x_1438_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1435_ = 0;
v___x_1436_ = 1;
v___x_1437_ = 1;
v___x_1438_ = l_Lean_Meta_mkForallFVars(v_fvars_1411_, v_a_1434_, v___x_1435_, v_usedLetOnly_1408_, v___x_1436_, v___x_1437_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
lean_dec_ref(v_fvars_1411_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1440_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1439_);
lean_dec_ref_known(v___x_1438_, 1);
v___x_1440_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1406_, v_post_1407_, v_usedLetOnly_1408_, v_skipConstInApp_1409_, v_skipInstances_1410_, v_a_1439_, v_a_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
return v___x_1440_;
}
else
{
lean_dec_ref(v_post_1407_);
lean_dec_ref(v_pre_1406_);
return v___x_1438_;
}
}
else
{
lean_dec_ref(v_fvars_1411_);
lean_dec_ref(v_post_1407_);
lean_dec_ref(v_pre_1406_);
return v___x_1433_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(lean_object* v_fvars_1441_, lean_object* v_pre_1442_, lean_object* v_post_1443_, uint8_t v_usedLetOnly_1444_, uint8_t v_skipConstInApp_1445_, uint8_t v_skipInstances_1446_, lean_object* v_body_1447_, lean_object* v_x_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_array_push(v_fvars_1441_, v_x_1448_);
v___x_1456_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1442_, v_post_1443_, v_usedLetOnly_1444_, v_skipConstInApp_1445_, v_skipInstances_1446_, v___x_1455_, v_body_1447_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7___boxed(lean_object* v_pre_1457_, lean_object* v_post_1458_, lean_object* v_usedLetOnly_1459_, lean_object* v_skipConstInApp_1460_, lean_object* v_skipInstances_1461_, lean_object* v_e_1462_, lean_object* v_a_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
uint8_t v_usedLetOnly_boxed_1469_; uint8_t v_skipConstInApp_boxed_1470_; uint8_t v_skipInstances_boxed_1471_; lean_object* v_res_1472_; 
v_usedLetOnly_boxed_1469_ = lean_unbox(v_usedLetOnly_1459_);
v_skipConstInApp_boxed_1470_ = lean_unbox(v_skipConstInApp_1460_);
v_skipInstances_boxed_1471_ = lean_unbox(v_skipInstances_1461_);
v_res_1472_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1457_, v_post_1458_, v_usedLetOnly_boxed_1469_, v_skipConstInApp_boxed_1470_, v_skipInstances_boxed_1471_, v_e_1462_, v_a_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v_a_1463_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___boxed(lean_object* v_pre_1473_, lean_object* v_post_1474_, lean_object* v_usedLetOnly_1475_, lean_object* v_skipConstInApp_1476_, lean_object* v_skipInstances_1477_, lean_object* v_sz_1478_, lean_object* v_i_1479_, lean_object* v_bs_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
uint8_t v_usedLetOnly_boxed_1487_; uint8_t v_skipConstInApp_boxed_1488_; uint8_t v_skipInstances_boxed_1489_; size_t v_sz_boxed_1490_; size_t v_i_boxed_1491_; lean_object* v_res_1492_; 
v_usedLetOnly_boxed_1487_ = lean_unbox(v_usedLetOnly_1475_);
v_skipConstInApp_boxed_1488_ = lean_unbox(v_skipConstInApp_1476_);
v_skipInstances_boxed_1489_ = lean_unbox(v_skipInstances_1477_);
v_sz_boxed_1490_ = lean_unbox_usize(v_sz_1478_);
lean_dec(v_sz_1478_);
v_i_boxed_1491_ = lean_unbox_usize(v_i_1479_);
lean_dec(v_i_1479_);
v_res_1492_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_1473_, v_post_1474_, v_usedLetOnly_boxed_1487_, v_skipConstInApp_boxed_1488_, v_skipInstances_boxed_1489_, v_sz_boxed_1490_, v_i_boxed_1491_, v_bs_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___boxed(lean_object* v_pre_1493_, lean_object* v_post_1494_, lean_object* v_usedLetOnly_1495_, lean_object* v_skipConstInApp_1496_, lean_object* v_skipInstances_1497_, lean_object* v_e_1498_, lean_object* v_a_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
uint8_t v_usedLetOnly_boxed_1505_; uint8_t v_skipConstInApp_boxed_1506_; uint8_t v_skipInstances_boxed_1507_; lean_object* v_res_1508_; 
v_usedLetOnly_boxed_1505_ = lean_unbox(v_usedLetOnly_1495_);
v_skipConstInApp_boxed_1506_ = lean_unbox(v_skipConstInApp_1496_);
v_skipInstances_boxed_1507_ = lean_unbox(v_skipInstances_1497_);
v_res_1508_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1493_, v_post_1494_, v_usedLetOnly_boxed_1505_, v_skipConstInApp_boxed_1506_, v_skipInstances_boxed_1507_, v_e_1498_, v_a_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v_a_1499_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___boxed(lean_object* v_pre_1509_, lean_object* v_post_1510_, lean_object* v_usedLetOnly_1511_, lean_object* v_skipConstInApp_1512_, lean_object* v_skipInstances_1513_, lean_object* v_fvars_1514_, lean_object* v_e_1515_, lean_object* v_a_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
uint8_t v_usedLetOnly_boxed_1522_; uint8_t v_skipConstInApp_boxed_1523_; uint8_t v_skipInstances_boxed_1524_; lean_object* v_res_1525_; 
v_usedLetOnly_boxed_1522_ = lean_unbox(v_usedLetOnly_1511_);
v_skipConstInApp_boxed_1523_ = lean_unbox(v_skipConstInApp_1512_);
v_skipInstances_boxed_1524_ = lean_unbox(v_skipInstances_1513_);
v_res_1525_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1509_, v_post_1510_, v_usedLetOnly_boxed_1522_, v_skipConstInApp_boxed_1523_, v_skipInstances_boxed_1524_, v_fvars_1514_, v_e_1515_, v_a_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v_a_1516_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___boxed(lean_object* v_pre_1526_, lean_object* v_post_1527_, lean_object* v_usedLetOnly_1528_, lean_object* v_skipConstInApp_1529_, lean_object* v_skipInstances_1530_, lean_object* v_fvars_1531_, lean_object* v_e_1532_, lean_object* v_a_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
uint8_t v_usedLetOnly_boxed_1539_; uint8_t v_skipConstInApp_boxed_1540_; uint8_t v_skipInstances_boxed_1541_; lean_object* v_res_1542_; 
v_usedLetOnly_boxed_1539_ = lean_unbox(v_usedLetOnly_1528_);
v_skipConstInApp_boxed_1540_ = lean_unbox(v_skipConstInApp_1529_);
v_skipInstances_boxed_1541_ = lean_unbox(v_skipInstances_1530_);
v_res_1542_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1526_, v_post_1527_, v_usedLetOnly_boxed_1539_, v_skipConstInApp_boxed_1540_, v_skipInstances_boxed_1541_, v_fvars_1531_, v_e_1532_, v_a_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v_a_1533_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___boxed(lean_object* v_pre_1543_, lean_object* v_post_1544_, lean_object* v_usedLetOnly_1545_, lean_object* v_skipConstInApp_1546_, lean_object* v_skipInstances_1547_, lean_object* v_fvars_1548_, lean_object* v_e_1549_, lean_object* v_a_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
uint8_t v_usedLetOnly_boxed_1556_; uint8_t v_skipConstInApp_boxed_1557_; uint8_t v_skipInstances_boxed_1558_; lean_object* v_res_1559_; 
v_usedLetOnly_boxed_1556_ = lean_unbox(v_usedLetOnly_1545_);
v_skipConstInApp_boxed_1557_ = lean_unbox(v_skipConstInApp_1546_);
v_skipInstances_boxed_1558_ = lean_unbox(v_skipInstances_1547_);
v_res_1559_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1543_, v_post_1544_, v_usedLetOnly_boxed_1556_, v_skipConstInApp_boxed_1557_, v_skipInstances_boxed_1558_, v_fvars_1548_, v_e_1549_, v_a_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v_a_1550_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___boxed(lean_object* v_upperBound_1560_, lean_object* v___x_1561_, lean_object* v_pre_1562_, lean_object* v_post_1563_, lean_object* v_usedLetOnly_1564_, lean_object* v_skipConstInApp_1565_, lean_object* v_skipInstances_1566_, lean_object* v_a_1567_, lean_object* v_b_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
uint8_t v_usedLetOnly_boxed_1575_; uint8_t v_skipConstInApp_boxed_1576_; uint8_t v_skipInstances_boxed_1577_; lean_object* v_res_1578_; 
v_usedLetOnly_boxed_1575_ = lean_unbox(v_usedLetOnly_1564_);
v_skipConstInApp_boxed_1576_ = lean_unbox(v_skipConstInApp_1565_);
v_skipInstances_boxed_1577_ = lean_unbox(v_skipInstances_1566_);
v_res_1578_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_1560_, v___x_1561_, v_pre_1562_, v_post_1563_, v_usedLetOnly_boxed_1575_, v_skipConstInApp_boxed_1576_, v_skipInstances_boxed_1577_, v_a_1567_, v_b_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___x_1561_);
lean_dec(v_upperBound_1560_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13___boxed(lean_object* v_skipInstances_1579_, lean_object* v_pre_1580_, lean_object* v_post_1581_, lean_object* v_usedLetOnly_1582_, lean_object* v_skipConstInApp_1583_, lean_object* v_x_1584_, lean_object* v_x_1585_, lean_object* v_x_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
uint8_t v_skipInstances_boxed_1593_; uint8_t v_usedLetOnly_boxed_1594_; uint8_t v_skipConstInApp_boxed_1595_; lean_object* v_res_1596_; 
v_skipInstances_boxed_1593_ = lean_unbox(v_skipInstances_1579_);
v_usedLetOnly_boxed_1594_ = lean_unbox(v_usedLetOnly_1582_);
v_skipConstInApp_boxed_1595_ = lean_unbox(v_skipConstInApp_1583_);
v_res_1596_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_boxed_1593_, v_pre_1580_, v_post_1581_, v_usedLetOnly_boxed_1594_, v_skipConstInApp_boxed_1595_, v_x_1584_, v_x_1585_, v_x_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
return v_res_1596_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = lean_box(0);
v___x_1598_ = lean_unsigned_to_nat(16u);
v___x_1599_ = lean_mk_array(v___x_1598_, v___x_1597_);
return v___x_1599_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1600_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0);
v___x_1601_ = lean_unsigned_to_nat(0u);
v___x_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
lean_ctor_set(v___x_1602_, 1, v___x_1600_);
return v___x_1602_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1);
v___x_1604_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1604_, 0, lean_box(0));
lean_closure_set(v___x_1604_, 1, lean_box(0));
lean_closure_set(v___x_1604_, 2, v___x_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(lean_object* v_input_1605_, lean_object* v_pre_1606_, lean_object* v_post_1607_, uint8_t v_usedLetOnly_1608_, uint8_t v_skipConstInApp_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v_a_1617_; uint8_t v___x_1618_; lean_object* v___x_1619_; 
v___x_1615_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2);
v___x_1616_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1615_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref(v___x_1616_);
v___x_1618_ = 0;
v___x_1619_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1606_, v_post_1607_, v_usedLetOnly_1608_, v_skipConstInApp_1609_, v___x_1618_, v_input_1605_, v_a_1617_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
v___x_1621_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1621_, 0, lean_box(0));
lean_closure_set(v___x_1621_, 1, lean_box(0));
lean_closure_set(v___x_1621_, 2, v_a_1617_);
v___x_1622_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1621_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1629_ == 0)
{
lean_object* v_unused_1630_; 
v_unused_1630_ = lean_ctor_get(v___x_1622_, 0);
lean_dec(v_unused_1630_);
v___x_1624_ = v___x_1622_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_dec(v___x_1622_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v_a_1620_);
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1620_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
else
{
lean_dec(v_a_1617_);
return v___x_1619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___boxed(lean_object* v_input_1631_, lean_object* v_pre_1632_, lean_object* v_post_1633_, lean_object* v_usedLetOnly_1634_, lean_object* v_skipConstInApp_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
uint8_t v_usedLetOnly_boxed_1641_; uint8_t v_skipConstInApp_boxed_1642_; lean_object* v_res_1643_; 
v_usedLetOnly_boxed_1641_ = lean_unbox(v_usedLetOnly_1634_);
v_skipConstInApp_boxed_1642_ = lean_unbox(v_skipConstInApp_1635_);
v_res_1643_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_input_1631_, v_pre_1632_, v_post_1633_, v_usedLetOnly_boxed_1641_, v_skipConstInApp_boxed_1642_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
return v_res_1643_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__2(void){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__1));
v___x_1647_ = l_Lean_stringToMessageData(v___x_1646_);
return v___x_1647_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__4(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__3));
v___x_1650_ = l_Lean_stringToMessageData(v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls(lean_object* v_fixedParamPerms_1651_, lean_object* v_argsPacker_1652_, lean_object* v_funNames_1653_, lean_object* v_newF_1654_, lean_object* v_e_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v___x_1661_; 
lean_inc(v_a_1659_);
lean_inc_ref(v_a_1658_);
lean_inc(v_a_1657_);
lean_inc_ref(v_a_1656_);
lean_inc_ref(v_newF_1654_);
v___x_1661_ = lean_infer_type(v_newF_1654_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___f_1663_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; uint8_t v___x_1674_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 1);
v___f_1663_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__0));
v___x_1674_ = l_Lean_Expr_isForall(v_a_1662_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec_ref(v_e_1655_);
lean_dec_ref(v_funNames_1653_);
lean_dec_ref(v_argsPacker_1652_);
lean_dec_ref(v_fixedParamPerms_1651_);
v___x_1675_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__2, &l_Lean_Elab_WF_packCalls___closed__2_once, _init_l_Lean_Elab_WF_packCalls___closed__2);
v___x_1676_ = l_Lean_MessageData_ofExpr(v_newF_1654_);
v___x_1677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1675_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v___x_1678_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__4, &l_Lean_Elab_WF_packCalls___closed__4_once, _init_l_Lean_Elab_WF_packCalls___closed__4);
v___x_1679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = l_Lean_MessageData_ofExpr(v_a_1662_);
v___x_1681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v___x_1681_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_);
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1682_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1682_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
else
{
v___y_1665_ = v_a_1656_;
v___y_1666_ = v_a_1657_;
v___y_1667_ = v_a_1658_;
v___y_1668_ = v_a_1659_;
goto v___jp_1664_;
}
v___jp_1664_:
{
lean_object* v___x_1669_; lean_object* v___f_1670_; uint8_t v___x_1671_; uint8_t v___x_1672_; lean_object* v___x_1673_; 
v___x_1669_ = l_Lean_Expr_bindingDomain_x21(v_a_1662_);
lean_dec(v_a_1662_);
v___f_1670_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packCalls___lam__2___boxed), 11, 5);
lean_closure_set(v___f_1670_, 0, v_funNames_1653_);
lean_closure_set(v___f_1670_, 1, v_fixedParamPerms_1651_);
lean_closure_set(v___f_1670_, 2, v_argsPacker_1652_);
lean_closure_set(v___f_1670_, 3, v___x_1669_);
lean_closure_set(v___f_1670_, 4, v_newF_1654_);
v___x_1671_ = 0;
v___x_1672_ = 1;
v___x_1673_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_e_1655_, v___f_1663_, v___f_1670_, v___x_1671_, v___x_1672_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
return v___x_1673_;
}
}
else
{
lean_dec_ref(v_e_1655_);
lean_dec_ref(v_newF_1654_);
lean_dec_ref(v_funNames_1653_);
lean_dec_ref(v_argsPacker_1652_);
lean_dec_ref(v_fixedParamPerms_1651_);
return v___x_1661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___boxed(lean_object* v_fixedParamPerms_1691_, lean_object* v_argsPacker_1692_, lean_object* v_funNames_1693_, lean_object* v_newF_1694_, lean_object* v_e_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_1691_, v_argsPacker_1692_, v_funNames_1693_, v_newF_1694_, v_e_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(lean_object* v_upperBound_1702_, lean_object* v___x_1703_, lean_object* v_pre_1704_, lean_object* v_post_1705_, uint8_t v_usedLetOnly_1706_, uint8_t v_skipConstInApp_1707_, uint8_t v_skipInstances_1708_, lean_object* v___x_1709_, lean_object* v_inst_1710_, lean_object* v_R_1711_, lean_object* v_a_1712_, lean_object* v_b_1713_, lean_object* v_c_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_1702_, v___x_1703_, v_pre_1704_, v_post_1705_, v_usedLetOnly_1706_, v_skipConstInApp_1707_, v_skipInstances_1708_, v_a_1712_, v_b_1713_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1722_ = _args[0];
lean_object* v___x_1723_ = _args[1];
lean_object* v_pre_1724_ = _args[2];
lean_object* v_post_1725_ = _args[3];
lean_object* v_usedLetOnly_1726_ = _args[4];
lean_object* v_skipConstInApp_1727_ = _args[5];
lean_object* v_skipInstances_1728_ = _args[6];
lean_object* v___x_1729_ = _args[7];
lean_object* v_inst_1730_ = _args[8];
lean_object* v_R_1731_ = _args[9];
lean_object* v_a_1732_ = _args[10];
lean_object* v_b_1733_ = _args[11];
lean_object* v_c_1734_ = _args[12];
lean_object* v___y_1735_ = _args[13];
lean_object* v___y_1736_ = _args[14];
lean_object* v___y_1737_ = _args[15];
lean_object* v___y_1738_ = _args[16];
lean_object* v___y_1739_ = _args[17];
lean_object* v___y_1740_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_1741_; uint8_t v_skipConstInApp_boxed_1742_; uint8_t v_skipInstances_boxed_1743_; lean_object* v_res_1744_; 
v_usedLetOnly_boxed_1741_ = lean_unbox(v_usedLetOnly_1726_);
v_skipConstInApp_boxed_1742_ = lean_unbox(v_skipConstInApp_1727_);
v_skipInstances_boxed_1743_ = lean_unbox(v_skipInstances_1728_);
v_res_1744_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_upperBound_1722_, v___x_1723_, v_pre_1724_, v_post_1725_, v_usedLetOnly_boxed_1741_, v_skipConstInApp_boxed_1742_, v_skipInstances_boxed_1743_, v___x_1729_, v_inst_1730_, v_R_1731_, v_a_1732_, v_b_1733_, v_c_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec(v___x_1729_);
lean_dec_ref(v___x_1723_);
lean_dec(v_upperBound_1722_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1745_, lean_object* v_m_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_m_1746_, v_a_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___boxed(lean_object* v_00_u03b2_1749_, lean_object* v_m_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(v_00_u03b2_1749_, v_m_1750_, v_a_1751_);
lean_dec_ref(v_a_1751_);
lean_dec_ref(v_m_1750_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_1753_, lean_object* v_name_1754_, uint8_t v_bi_1755_, lean_object* v_type_1756_, lean_object* v_k_1757_, uint8_t v_kind_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_1754_, v_bi_1755_, v_type_1756_, v_k_1757_, v_kind_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_1766_, lean_object* v_name_1767_, lean_object* v_bi_1768_, lean_object* v_type_1769_, lean_object* v_k_1770_, lean_object* v_kind_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
uint8_t v_bi_boxed_1778_; uint8_t v_kind_boxed_1779_; lean_object* v_res_1780_; 
v_bi_boxed_1778_ = lean_unbox(v_bi_1768_);
v_kind_boxed_1779_ = lean_unbox(v_kind_1771_);
v_res_1780_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(v_00_u03b1_1766_, v_name_1767_, v_bi_boxed_1778_, v_type_1769_, v_k_1770_, v_kind_boxed_1779_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(lean_object* v_00_u03b1_1781_, lean_object* v_name_1782_, lean_object* v_type_1783_, lean_object* v_val_1784_, lean_object* v_k_1785_, uint8_t v_nondep_1786_, uint8_t v_kind_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_1782_, v_type_1783_, v_val_1784_, v_k_1785_, v_nondep_1786_, v_kind_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___boxed(lean_object* v_00_u03b1_1795_, lean_object* v_name_1796_, lean_object* v_type_1797_, lean_object* v_val_1798_, lean_object* v_k_1799_, lean_object* v_nondep_1800_, lean_object* v_kind_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
uint8_t v_nondep_boxed_1808_; uint8_t v_kind_boxed_1809_; lean_object* v_res_1810_; 
v_nondep_boxed_1808_ = lean_unbox(v_nondep_1800_);
v_kind_boxed_1809_ = lean_unbox(v_kind_1801_);
v_res_1810_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(v_00_u03b1_1795_, v_name_1796_, v_type_1797_, v_val_1798_, v_k_1799_, v_nondep_boxed_1808_, v_kind_boxed_1809_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(lean_object* v_00_u03b1_1811_, lean_object* v_ref_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_1812_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___boxed(lean_object* v_00_u03b1_1819_, lean_object* v_ref_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(v_00_u03b1_1819_, v_ref_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(lean_object* v_00_u03b1_1827_, lean_object* v_x_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___boxed(lean_object* v_00_u03b1_1836_, lean_object* v_x_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(v_00_u03b1_1836_, v_x_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15(lean_object* v_00_u03b2_1845_, lean_object* v_m_1846_, lean_object* v_a_1847_, lean_object* v_b_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v_m_1846_, v_a_1847_, v_b_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(lean_object* v_00_u03b2_1850_, lean_object* v_a_1851_, lean_object* v_x_1852_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_1851_, v_x_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___boxed(lean_object* v_00_u03b2_1854_, lean_object* v_a_1855_, lean_object* v_x_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(v_00_u03b2_1854_, v_a_1855_, v_x_1856_);
lean_dec(v_x_1856_);
lean_dec_ref(v_a_1855_);
return v_res_1857_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(lean_object* v_00_u03b2_1858_, lean_object* v_a_1859_, lean_object* v_x_1860_){
_start:
{
uint8_t v___x_1861_; 
v___x_1861_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_1859_, v_x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___boxed(lean_object* v_00_u03b2_1862_, lean_object* v_a_1863_, lean_object* v_x_1864_){
_start:
{
uint8_t v_res_1865_; lean_object* v_r_1866_; 
v_res_1865_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(v_00_u03b2_1862_, v_a_1863_, v_x_1864_);
lean_dec(v_x_1864_);
lean_dec_ref(v_a_1863_);
v_r_1866_ = lean_box(v_res_1865_);
return v_r_1866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21(lean_object* v_00_u03b2_1867_, lean_object* v_data_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_data_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22(lean_object* v_00_u03b2_1870_, lean_object* v_a_1871_, lean_object* v_b_1872_, lean_object* v_x_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_1871_, v_b_1872_, v_x_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22(lean_object* v_00_u03b2_1875_, lean_object* v_i_1876_, lean_object* v_source_1877_, lean_object* v_target_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v_i_1876_, v_source_1877_, v_target_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23(lean_object* v_00_u03b2_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(v_x_1881_, v_x_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName(lean_object* v_fixedParamPerms_1890_, lean_object* v_argsPacker_1891_, lean_object* v_preDefs_1892_){
_start:
{
uint8_t v___y_1894_; uint8_t v___x_1914_; 
v___x_1914_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_1890_);
if (v___x_1914_ == 0)
{
v___y_1894_ = v___x_1914_;
goto v___jp_1893_;
}
else
{
uint8_t v___x_1915_; 
v___x_1915_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_1891_);
v___y_1894_ = v___x_1915_;
goto v___jp_1893_;
}
v___jp_1893_:
{
if (v___y_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1895_ = lean_unsigned_to_nat(1u);
v___x_1896_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_1891_);
v___x_1897_ = lean_nat_dec_lt(v___x_1895_, v___x_1896_);
lean_dec(v___x_1896_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v_declName_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1898_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1899_ = lean_unsigned_to_nat(0u);
v___x_1900_ = lean_array_get_borrowed(v___x_1898_, v_preDefs_1892_, v___x_1899_);
v_declName_1901_ = lean_ctor_get(v___x_1900_, 3);
v___x_1902_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__1));
lean_inc(v_declName_1901_);
v___x_1903_ = l_Lean_Name_append(v_declName_1901_, v___x_1902_);
return v___x_1903_;
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v_declName_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1904_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1905_ = lean_unsigned_to_nat(0u);
v___x_1906_ = lean_array_get_borrowed(v___x_1904_, v_preDefs_1892_, v___x_1905_);
v_declName_1907_ = lean_ctor_get(v___x_1906_, 3);
v___x_1908_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__3));
lean_inc(v_declName_1907_);
v___x_1909_ = l_Lean_Name_append(v_declName_1907_, v___x_1908_);
return v___x_1909_;
}
}
else
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v_declName_1913_; 
v___x_1910_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1911_ = lean_unsigned_to_nat(0u);
v___x_1912_ = lean_array_get_borrowed(v___x_1910_, v_preDefs_1892_, v___x_1911_);
v_declName_1913_ = lean_ctor_get(v___x_1912_, 3);
lean_inc(v_declName_1913_);
return v_declName_1913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName___boxed(lean_object* v_fixedParamPerms_1916_, lean_object* v_argsPacker_1917_, lean_object* v_preDefs_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_1916_, v_argsPacker_1917_, v_preDefs_1918_);
lean_dec_ref(v_preDefs_1918_);
lean_dec_ref(v_argsPacker_1917_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(lean_object* v_k_1920_, lean_object* v_b_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v___x_1927_; 
lean_inc(v___y_1925_);
lean_inc_ref(v___y_1924_);
lean_inc(v___y_1923_);
lean_inc_ref(v___y_1922_);
v___x_1927_ = lean_apply_6(v_k_1920_, v_b_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, lean_box(0));
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed(lean_object* v_k_1928_, lean_object* v_b_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(v_k_1928_, v_b_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(lean_object* v_perm_1936_, lean_object* v_type_1937_, lean_object* v_k_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___f_1944_; lean_object* v___x_1945_; 
v___f_1944_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1944_, 0, v_k_1938_);
v___x_1945_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_1936_, v_type_1937_, v___f_1944_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1945_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
v_a_1954_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1945_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1945_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___boxed(lean_object* v_perm_1962_, lean_object* v_type_1963_, lean_object* v_k_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_1962_, v_type_1963_, v_k_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(lean_object* v_00_u03b1_1971_, lean_object* v_perm_1972_, lean_object* v_type_1973_, lean_object* v_k_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_1972_, v_type_1973_, v_k_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___boxed(lean_object* v_00_u03b1_1981_, lean_object* v_perm_1982_, lean_object* v_type_1983_, lean_object* v_k_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(v_00_u03b1_1981_, v_perm_1982_, v_type_1983_, v_k_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(lean_object* v___x_1991_, lean_object* v_ys_1992_, size_t v_sz_1993_, size_t v_i_1994_, lean_object* v_bs_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
uint8_t v___x_2001_; 
v___x_2001_ = lean_usize_dec_lt(v_i_1994_, v_sz_1993_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; 
lean_dec_ref(v_ys_1992_);
v___x_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2002_, 0, v_bs_1995_);
return v___x_2002_;
}
else
{
lean_object* v_v_2003_; lean_object* v_value_2004_; lean_object* v___x_2005_; lean_object* v_bs_x27_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v_v_2003_ = lean_array_uget_borrowed(v_bs_1995_, v_i_1994_);
v_value_2004_ = lean_ctor_get(v_v_2003_, 7);
lean_inc_ref(v_value_2004_);
v___x_2005_ = lean_unsigned_to_nat(0u);
v_bs_x27_2006_ = lean_array_uset(v_bs_1995_, v_i_1994_, v___x_2005_);
v___x_2007_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2008_ = lean_usize_to_nat(v_i_1994_);
v___x_2009_ = lean_array_get_borrowed(v___x_2007_, v___x_1991_, v___x_2008_);
lean_dec(v___x_2008_);
lean_inc_ref(v_ys_1992_);
lean_inc(v___x_2009_);
v___x_2010_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_2009_, v_value_2004_, v_ys_1992_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; size_t v___x_2012_; size_t v___x_2013_; lean_object* v___x_2014_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
v___x_2012_ = ((size_t)1ULL);
v___x_2013_ = lean_usize_add(v_i_1994_, v___x_2012_);
v___x_2014_ = lean_array_uset(v_bs_x27_2006_, v_i_1994_, v_a_2011_);
v_i_1994_ = v___x_2013_;
v_bs_1995_ = v___x_2014_;
goto _start;
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec_ref(v_bs_x27_2006_);
lean_dec_ref(v_ys_1992_);
v_a_2016_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2010_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2010_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg___boxed(lean_object* v___x_2024_, lean_object* v_ys_2025_, lean_object* v_sz_2026_, lean_object* v_i_2027_, lean_object* v_bs_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
size_t v_sz_boxed_2034_; size_t v_i_boxed_2035_; lean_object* v_res_2036_; 
v_sz_boxed_2034_ = lean_unbox_usize(v_sz_2026_);
lean_dec(v_sz_2026_);
v_i_boxed_2035_ = lean_unbox_usize(v_i_2027_);
lean_dec(v_i_2027_);
v_res_2036_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2024_, v_ys_2025_, v_sz_boxed_2034_, v_i_boxed_2035_, v_bs_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec_ref(v___x_2024_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(lean_object* v___x_2037_, lean_object* v_ys_2038_, size_t v_sz_2039_, size_t v_i_2040_, lean_object* v_bs_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
uint8_t v___x_2047_; 
v___x_2047_ = lean_usize_dec_lt(v_i_2040_, v_sz_2039_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; 
lean_dec_ref(v_ys_2038_);
v___x_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2048_, 0, v_bs_2041_);
return v___x_2048_;
}
else
{
lean_object* v_v_2049_; lean_object* v_type_2050_; lean_object* v___x_2051_; lean_object* v_bs_x27_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v_v_2049_ = lean_array_uget_borrowed(v_bs_2041_, v_i_2040_);
v_type_2050_ = lean_ctor_get(v_v_2049_, 6);
lean_inc_ref(v_type_2050_);
v___x_2051_ = lean_unsigned_to_nat(0u);
v_bs_x27_2052_ = lean_array_uset(v_bs_2041_, v_i_2040_, v___x_2051_);
v___x_2053_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2054_ = lean_usize_to_nat(v_i_2040_);
v___x_2055_ = lean_array_get_borrowed(v___x_2053_, v___x_2037_, v___x_2054_);
lean_dec(v___x_2054_);
lean_inc_ref(v_ys_2038_);
lean_inc(v___x_2055_);
v___x_2056_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_2055_, v_type_2050_, v_ys_2038_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; size_t v___x_2058_; size_t v___x_2059_; lean_object* v___x_2060_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v___x_2056_, 1);
v___x_2058_ = ((size_t)1ULL);
v___x_2059_ = lean_usize_add(v_i_2040_, v___x_2058_);
v___x_2060_ = lean_array_uset(v_bs_x27_2052_, v_i_2040_, v_a_2057_);
v_i_2040_ = v___x_2059_;
v_bs_2041_ = v___x_2060_;
goto _start;
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec_ref(v_bs_x27_2052_);
lean_dec_ref(v_ys_2038_);
v_a_2062_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2056_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2056_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg___boxed(lean_object* v___x_2070_, lean_object* v_ys_2071_, lean_object* v_sz_2072_, lean_object* v_i_2073_, lean_object* v_bs_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
size_t v_sz_boxed_2080_; size_t v_i_boxed_2081_; lean_object* v_res_2082_; 
v_sz_boxed_2080_ = lean_unbox_usize(v_sz_2072_);
lean_dec(v_sz_2072_);
v_i_boxed_2081_ = lean_unbox_usize(v_i_2073_);
lean_dec(v_i_2073_);
v_res_2082_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2070_, v_ys_2071_, v_sz_boxed_2080_, v_i_boxed_2081_, v_bs_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec_ref(v___x_2070_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(lean_object* v_a_2083_, lean_object* v_a_2084_){
_start:
{
if (lean_obj_tag(v_a_2083_) == 0)
{
lean_object* v___x_2085_; 
v___x_2085_ = l_List_reverse___redArg(v_a_2084_);
return v___x_2085_;
}
else
{
lean_object* v_head_2086_; lean_object* v_tail_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2096_; 
v_head_2086_ = lean_ctor_get(v_a_2083_, 0);
v_tail_2087_ = lean_ctor_get(v_a_2083_, 1);
v_isSharedCheck_2096_ = !lean_is_exclusive(v_a_2083_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2089_ = v_a_2083_;
v_isShared_2090_ = v_isSharedCheck_2096_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_tail_2087_);
lean_inc(v_head_2086_);
lean_dec(v_a_2083_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2096_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2091_ = l_Lean_mkLevelParam(v_head_2086_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 1, v_a_2084_);
lean_ctor_set(v___x_2089_, 0, v___x_2091_);
v___x_2093_ = v___x_2089_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_a_2084_);
v___x_2093_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
v_a_2083_ = v_tail_2087_;
v_a_2084_ = v___x_2093_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(size_t v_sz_2097_, size_t v_i_2098_, lean_object* v_bs_2099_){
_start:
{
uint8_t v___x_2100_; 
v___x_2100_ = lean_usize_dec_lt(v_i_2098_, v_sz_2097_);
if (v___x_2100_ == 0)
{
return v_bs_2099_;
}
else
{
lean_object* v_v_2101_; lean_object* v_declName_2102_; lean_object* v___x_2103_; lean_object* v_bs_x27_2104_; size_t v___x_2105_; size_t v___x_2106_; lean_object* v___x_2107_; 
v_v_2101_ = lean_array_uget_borrowed(v_bs_2099_, v_i_2098_);
v_declName_2102_ = lean_ctor_get(v_v_2101_, 3);
lean_inc(v_declName_2102_);
v___x_2103_ = lean_unsigned_to_nat(0u);
v_bs_x27_2104_ = lean_array_uset(v_bs_2099_, v_i_2098_, v___x_2103_);
v___x_2105_ = ((size_t)1ULL);
v___x_2106_ = lean_usize_add(v_i_2098_, v___x_2105_);
v___x_2107_ = lean_array_uset(v_bs_x27_2104_, v_i_2098_, v_declName_2102_);
v_i_2098_ = v___x_2106_;
v_bs_2099_ = v___x_2107_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3___boxed(lean_object* v_sz_2109_, lean_object* v_i_2110_, lean_object* v_bs_2111_){
_start:
{
size_t v_sz_boxed_2112_; size_t v_i_boxed_2113_; lean_object* v_res_2114_; 
v_sz_boxed_2112_ = lean_unbox_usize(v_sz_2109_);
lean_dec(v_sz_2109_);
v_i_boxed_2113_ = lean_unbox_usize(v_i_2110_);
lean_dec(v_i_2110_);
v_res_2114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_boxed_2112_, v_i_boxed_2113_, v_bs_2111_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0(lean_object* v_preDefs_2115_, lean_object* v_perms_2116_, lean_object* v_argsPacker_2117_, uint8_t v___x_2118_, lean_object* v_ref_2119_, uint8_t v_kind_2120_, lean_object* v_levelParams_2121_, lean_object* v_modifiers_2122_, lean_object* v_newFn_2123_, lean_object* v_binders_2124_, lean_object* v_numSectionVars_2125_, lean_object* v_value_2126_, lean_object* v_termination_2127_, lean_object* v_fixedParamPerms_2128_, lean_object* v_ys_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
size_t v_sz_2135_; size_t v___x_2136_; lean_object* v___x_2137_; 
v_sz_2135_ = lean_array_size(v_preDefs_2115_);
v___x_2136_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_2115_);
lean_inc_ref(v_ys_2129_);
v___x_2137_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v_perms_2116_, v_ys_2129_, v_sz_2135_, v___x_2136_, v_preDefs_2115_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2139_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
lean_inc_ref(v_preDefs_2115_);
lean_inc_ref(v_ys_2129_);
v___x_2139_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v_perms_2116_, v_ys_2129_, v_sz_2135_, v___x_2136_, v_preDefs_2115_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v___x_2141_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_2117_, v_a_2138_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec(v_a_2138_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; uint8_t v___x_2143_; uint8_t v___x_2144_; lean_object* v___x_2145_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
v___x_2143_ = 1;
v___x_2144_ = 1;
v___x_2145_ = l_Lean_Meta_mkForallFVars(v_ys_2129_, v_a_2142_, v___x_2118_, v___x_2143_, v___x_2143_, v___x_2144_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc_n(v_a_2146_, 2);
lean_dec_ref_known(v___x_2145_, 1);
lean_inc_ref(v_termination_2127_);
lean_inc(v_numSectionVars_2125_);
lean_inc(v_binders_2124_);
lean_inc(v_newFn_2123_);
lean_inc_ref(v_modifiers_2122_);
lean_inc(v_levelParams_2121_);
lean_inc(v_ref_2119_);
v___x_2147_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2147_, 0, v_ref_2119_);
lean_ctor_set(v___x_2147_, 1, v_levelParams_2121_);
lean_ctor_set(v___x_2147_, 2, v_modifiers_2122_);
lean_ctor_set(v___x_2147_, 3, v_newFn_2123_);
lean_ctor_set(v___x_2147_, 4, v_binders_2124_);
lean_ctor_set(v___x_2147_, 5, v_numSectionVars_2125_);
lean_ctor_set(v___x_2147_, 6, v_a_2146_);
lean_ctor_set(v___x_2147_, 7, v_value_2126_);
lean_ctor_set(v___x_2147_, 8, v_termination_2127_);
lean_ctor_set_uint8(v___x_2147_, sizeof(void*)*9, v_kind_2120_);
v___x_2148_ = l_Lean_Elab_addAsAxiom___redArg(v___x_2147_, v___y_2132_, v___y_2133_);
lean_dec_ref_known(v___x_2147_, 9);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v___x_2149_; 
lean_dec_ref_known(v___x_2148_, 1);
v___x_2149_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_2117_, v_a_2140_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec(v_a_2140_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v___x_2151_ = lean_box(0);
lean_inc(v_levelParams_2121_);
v___x_2152_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_2121_, v___x_2151_);
lean_inc(v_newFn_2123_);
v___x_2153_ = l_Lean_mkConst(v_newFn_2123_, v___x_2152_);
v___x_2154_ = l_Lean_mkAppN(v___x_2153_, v_ys_2129_);
v___x_2155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_2135_, v___x_2136_, v_preDefs_2115_);
v___x_2156_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_2128_, v_argsPacker_2117_, v___x_2155_, v___x_2154_, v_a_2150_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2158_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref_known(v___x_2156_, 1);
v___x_2158_ = l_Lean_Meta_mkLambdaFVars(v_ys_2129_, v_a_2157_, v___x_2118_, v___x_2143_, v___x_2118_, v___x_2143_, v___x_2144_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec_ref(v_ys_2129_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2167_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2161_ = v___x_2158_;
v_isShared_2162_ = v_isSharedCheck_2167_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2158_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2167_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2163_; lean_object* v___x_2165_; 
v___x_2163_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2163_, 0, v_ref_2119_);
lean_ctor_set(v___x_2163_, 1, v_levelParams_2121_);
lean_ctor_set(v___x_2163_, 2, v_modifiers_2122_);
lean_ctor_set(v___x_2163_, 3, v_newFn_2123_);
lean_ctor_set(v___x_2163_, 4, v_binders_2124_);
lean_ctor_set(v___x_2163_, 5, v_numSectionVars_2125_);
lean_ctor_set(v___x_2163_, 6, v_a_2146_);
lean_ctor_set(v___x_2163_, 7, v_a_2159_);
lean_ctor_set(v___x_2163_, 8, v_termination_2127_);
lean_ctor_set_uint8(v___x_2163_, sizeof(void*)*9, v_kind_2120_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v___x_2163_);
v___x_2165_ = v___x_2161_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec(v_a_2146_);
lean_dec_ref(v_termination_2127_);
lean_dec(v_numSectionVars_2125_);
lean_dec(v_binders_2124_);
lean_dec(v_newFn_2123_);
lean_dec_ref(v_modifiers_2122_);
lean_dec(v_levelParams_2121_);
lean_dec(v_ref_2119_);
v_a_2168_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2158_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2158_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec(v_a_2146_);
lean_dec_ref(v_ys_2129_);
lean_dec_ref(v_termination_2127_);
lean_dec(v_numSectionVars_2125_);
lean_dec(v_binders_2124_);
lean_dec(v_newFn_2123_);
lean_dec_ref(v_modifiers_2122_);
lean_dec(v_levelParams_2121_);
lean_dec(v_ref_2119_);
v_a_2176_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2156_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2156_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec(v_a_2146_);
lean_dec_ref(v_ys_2129_);
lean_dec_ref(v_fixedParamPerms_2128_);
lean_dec_ref(v_termination_2127_);
lean_dec(v_numSectionVars_2125_);
lean_dec(v_binders_2124_);
lean_dec(v_newFn_2123_);
lean_dec_ref(v_modifiers_2122_);
lean_dec(v_levelParams_2121_);
lean_dec(v_ref_2119_);
lean_dec_ref(v_argsPacker_2117_);
lean_dec_ref(v_preDefs_2115_);
v_a_2184_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2149_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2149_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec(v_a_2146_);
lean_dec(v_a_2140_);
lean_dec_ref(v_ys_2129_);
lean_dec_ref(v_fixedParamPerms_2128_);
lean_dec_ref(v_termination_2127_);
lean_dec(v_numSectionVars_2125_);
lean_dec(v_binders_2124_);
lean_dec(v_newFn_2123_);
lean_dec_ref(v_modifiers_2122_);
lean_dec(v_levelParams_2121_);
lean_dec(v_ref_2119_);
lean_dec_ref(v_argsPacker_2117_);
lean_dec_ref(v_preDefs_2115_);
v_a_2192_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2148_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2148_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec(v_a_2140_);
lean_dec_ref(v_ys_2129_);
lean_dec_ref(v_fixedParamPerms_2128_);
lean_dec_ref(v_termination_2127_);
lean_dec_ref(v_value_2126_);
lean_dec(v_numSectionVars_2125_);
lean_dec(v_binders_2124_);
lean_dec(v_newFn_2123_);
lean_dec_ref(v_modifiers_2122_);
lean_dec(v_levelParams_2121_);
lean_dec(v_ref_2119_);
lean_dec_ref(v_argsPacker_2117_);
lean_dec_ref(v_preDefs_2115_);
v_a_2200_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2145_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2145_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_dec(v_a_2140_);
lean_dec_ref(v_ys_2129_);
lean_dec_ref(v_fixedParamPerms_2128_);
lean_dec_ref(v_termination_2127_);
lean_dec_ref(v_value_2126_);
lean_dec(v_numSectionVars_2125_);
lean_dec(v_binders_2124_);
lean_dec(v_newFn_2123_);
lean_dec_ref(v_modifiers_2122_);
lean_dec(v_levelParams_2121_);
lean_dec(v_ref_2119_);
lean_dec_ref(v_argsPacker_2117_);
lean_dec_ref(v_preDefs_2115_);
v_a_2208_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2141_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2141_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec(v_a_2138_);
lean_dec_ref(v_ys_2129_);
lean_dec_ref(v_fixedParamPerms_2128_);
lean_dec_ref(v_termination_2127_);
lean_dec_ref(v_value_2126_);
lean_dec(v_numSectionVars_2125_);
lean_dec(v_binders_2124_);
lean_dec(v_newFn_2123_);
lean_dec_ref(v_modifiers_2122_);
lean_dec(v_levelParams_2121_);
lean_dec(v_ref_2119_);
lean_dec_ref(v_argsPacker_2117_);
lean_dec_ref(v_preDefs_2115_);
v_a_2216_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2139_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2139_);
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
lean_dec_ref(v_ys_2129_);
lean_dec_ref(v_fixedParamPerms_2128_);
lean_dec_ref(v_termination_2127_);
lean_dec_ref(v_value_2126_);
lean_dec(v_numSectionVars_2125_);
lean_dec(v_binders_2124_);
lean_dec(v_newFn_2123_);
lean_dec_ref(v_modifiers_2122_);
lean_dec(v_levelParams_2121_);
lean_dec(v_ref_2119_);
lean_dec_ref(v_argsPacker_2117_);
lean_dec_ref(v_preDefs_2115_);
v_a_2224_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2137_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2137_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0___boxed(lean_object** _args){
lean_object* v_preDefs_2232_ = _args[0];
lean_object* v_perms_2233_ = _args[1];
lean_object* v_argsPacker_2234_ = _args[2];
lean_object* v___x_2235_ = _args[3];
lean_object* v_ref_2236_ = _args[4];
lean_object* v_kind_2237_ = _args[5];
lean_object* v_levelParams_2238_ = _args[6];
lean_object* v_modifiers_2239_ = _args[7];
lean_object* v_newFn_2240_ = _args[8];
lean_object* v_binders_2241_ = _args[9];
lean_object* v_numSectionVars_2242_ = _args[10];
lean_object* v_value_2243_ = _args[11];
lean_object* v_termination_2244_ = _args[12];
lean_object* v_fixedParamPerms_2245_ = _args[13];
lean_object* v_ys_2246_ = _args[14];
lean_object* v___y_2247_ = _args[15];
lean_object* v___y_2248_ = _args[16];
lean_object* v___y_2249_ = _args[17];
lean_object* v___y_2250_ = _args[18];
lean_object* v___y_2251_ = _args[19];
_start:
{
uint8_t v___x_2529__boxed_2252_; uint8_t v_kind_boxed_2253_; lean_object* v_res_2254_; 
v___x_2529__boxed_2252_ = lean_unbox(v___x_2235_);
v_kind_boxed_2253_ = lean_unbox(v_kind_2237_);
v_res_2254_ = l_Lean_Elab_WF_packMutual___lam__0(v_preDefs_2232_, v_perms_2233_, v_argsPacker_2234_, v___x_2529__boxed_2252_, v_ref_2236_, v_kind_boxed_2253_, v_levelParams_2238_, v_modifiers_2239_, v_newFn_2240_, v_binders_2241_, v_numSectionVars_2242_, v_value_2243_, v_termination_2244_, v_fixedParamPerms_2245_, v_ys_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec_ref(v_perms_2233_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual(lean_object* v_fixedParamPerms_2255_, lean_object* v_argsPacker_2256_, lean_object* v_preDefs_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v_ref_2266_; uint8_t v_kind_2267_; lean_object* v_levelParams_2268_; lean_object* v_modifiers_2269_; lean_object* v_declName_2270_; lean_object* v_binders_2271_; lean_object* v_numSectionVars_2272_; lean_object* v_type_2273_; lean_object* v_value_2274_; lean_object* v_termination_2275_; lean_object* v_newFn_2276_; uint8_t v___x_2277_; 
v___x_2263_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_2264_ = lean_unsigned_to_nat(0u);
v___x_2265_ = lean_array_get_borrowed(v___x_2263_, v_preDefs_2257_, v___x_2264_);
v_ref_2266_ = lean_ctor_get(v___x_2265_, 0);
v_kind_2267_ = lean_ctor_get_uint8(v___x_2265_, sizeof(void*)*9);
v_levelParams_2268_ = lean_ctor_get(v___x_2265_, 1);
v_modifiers_2269_ = lean_ctor_get(v___x_2265_, 2);
v_declName_2270_ = lean_ctor_get(v___x_2265_, 3);
v_binders_2271_ = lean_ctor_get(v___x_2265_, 4);
v_numSectionVars_2272_ = lean_ctor_get(v___x_2265_, 5);
v_type_2273_ = lean_ctor_get(v___x_2265_, 6);
v_value_2274_ = lean_ctor_get(v___x_2265_, 7);
v_termination_2275_ = lean_ctor_get(v___x_2265_, 8);
lean_inc_ref(v_fixedParamPerms_2255_);
v_newFn_2276_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_2255_, v_argsPacker_2256_, v_preDefs_2257_);
v___x_2277_ = lean_name_eq(v_newFn_2276_, v_declName_2270_);
if (v___x_2277_ == 0)
{
lean_object* v_perms_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___f_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
lean_inc_ref(v_termination_2275_);
lean_inc_ref(v_value_2274_);
lean_inc_ref(v_type_2273_);
lean_inc(v_numSectionVars_2272_);
lean_inc(v_binders_2271_);
lean_inc_ref(v_modifiers_2269_);
lean_inc(v_levelParams_2268_);
lean_inc(v_ref_2266_);
v_perms_2278_ = lean_ctor_get(v_fixedParamPerms_2255_, 1);
lean_inc_ref_n(v_perms_2278_, 2);
v___x_2279_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2280_ = lean_box(v___x_2277_);
v___x_2281_ = lean_box(v_kind_2267_);
v___f_2282_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packMutual___lam__0___boxed), 20, 14);
lean_closure_set(v___f_2282_, 0, v_preDefs_2257_);
lean_closure_set(v___f_2282_, 1, v_perms_2278_);
lean_closure_set(v___f_2282_, 2, v_argsPacker_2256_);
lean_closure_set(v___f_2282_, 3, v___x_2280_);
lean_closure_set(v___f_2282_, 4, v_ref_2266_);
lean_closure_set(v___f_2282_, 5, v___x_2281_);
lean_closure_set(v___f_2282_, 6, v_levelParams_2268_);
lean_closure_set(v___f_2282_, 7, v_modifiers_2269_);
lean_closure_set(v___f_2282_, 8, v_newFn_2276_);
lean_closure_set(v___f_2282_, 9, v_binders_2271_);
lean_closure_set(v___f_2282_, 10, v_numSectionVars_2272_);
lean_closure_set(v___f_2282_, 11, v_value_2274_);
lean_closure_set(v___f_2282_, 12, v_termination_2275_);
lean_closure_set(v___f_2282_, 13, v_fixedParamPerms_2255_);
v___x_2283_ = lean_array_get(v___x_2279_, v_perms_2278_, v___x_2264_);
lean_dec_ref(v_perms_2278_);
v___x_2284_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v___x_2283_, v_type_2273_, v___f_2282_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
return v___x_2284_;
}
else
{
lean_object* v___x_2285_; 
lean_inc(v___x_2265_);
lean_dec(v_newFn_2276_);
lean_dec_ref(v_preDefs_2257_);
lean_dec_ref(v_argsPacker_2256_);
lean_dec_ref(v_fixedParamPerms_2255_);
v___x_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2265_);
return v___x_2285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___boxed(lean_object* v_fixedParamPerms_2286_, lean_object* v_argsPacker_2287_, lean_object* v_preDefs_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_Elab_WF_packMutual(v_fixedParamPerms_2286_, v_argsPacker_2287_, v_preDefs_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(lean_object* v___x_2295_, lean_object* v_ys_2296_, lean_object* v_as_2297_, size_t v_sz_2298_, size_t v_i_2299_, lean_object* v_bs_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2295_, v_ys_2296_, v_sz_2298_, v_i_2299_, v_bs_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___boxed(lean_object* v___x_2307_, lean_object* v_ys_2308_, lean_object* v_as_2309_, lean_object* v_sz_2310_, lean_object* v_i_2311_, lean_object* v_bs_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
size_t v_sz_boxed_2318_; size_t v_i_boxed_2319_; lean_object* v_res_2320_; 
v_sz_boxed_2318_ = lean_unbox_usize(v_sz_2310_);
lean_dec(v_sz_2310_);
v_i_boxed_2319_ = lean_unbox_usize(v_i_2311_);
lean_dec(v_i_2311_);
v_res_2320_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(v___x_2307_, v_ys_2308_, v_as_2309_, v_sz_boxed_2318_, v_i_boxed_2319_, v_bs_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec_ref(v_as_2309_);
lean_dec_ref(v___x_2307_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(lean_object* v___x_2321_, lean_object* v_ys_2322_, lean_object* v_as_2323_, size_t v_sz_2324_, size_t v_i_2325_, lean_object* v_bs_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2321_, v_ys_2322_, v_sz_2324_, v_i_2325_, v_bs_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___boxed(lean_object* v___x_2333_, lean_object* v_ys_2334_, lean_object* v_as_2335_, lean_object* v_sz_2336_, lean_object* v_i_2337_, lean_object* v_bs_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
size_t v_sz_boxed_2344_; size_t v_i_boxed_2345_; lean_object* v_res_2346_; 
v_sz_boxed_2344_ = lean_unbox_usize(v_sz_2336_);
lean_dec(v_sz_2336_);
v_i_boxed_2345_ = lean_unbox_usize(v_i_2337_);
lean_dec(v_i_2337_);
v_res_2346_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(v___x_2333_, v_ys_2334_, v_as_2335_, v_sz_boxed_2344_, v_i_boxed_2345_, v_bs_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec_ref(v_as_2335_);
lean_dec_ref(v___x_2333_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(lean_object* v_e_2347_, lean_object* v_k_2348_, uint8_t v_cleanupAnnotations_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v___f_2355_; uint8_t v___x_2356_; uint8_t v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___f_2355_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2355_, 0, v_k_2348_);
v___x_2356_ = 1;
v___x_2357_ = 0;
v___x_2358_ = lean_box(0);
v___x_2359_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2347_, v___x_2356_, v___x_2357_, v___x_2356_, v___x_2357_, v___x_2358_, v___f_2355_, v_cleanupAnnotations_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2359_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2359_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
v_a_2368_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2359_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2359_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg___boxed(lean_object* v_e_2376_, lean_object* v_k_2377_, lean_object* v_cleanupAnnotations_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2384_; lean_object* v_res_2385_; 
v_cleanupAnnotations_boxed_2384_ = lean_unbox(v_cleanupAnnotations_2378_);
v_res_2385_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2376_, v_k_2377_, v_cleanupAnnotations_boxed_2384_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(lean_object* v_00_u03b1_2386_, lean_object* v_e_2387_, lean_object* v_k_2388_, uint8_t v_cleanupAnnotations_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2387_, v_k_2388_, v_cleanupAnnotations_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___boxed(lean_object* v_00_u03b1_2396_, lean_object* v_e_2397_, lean_object* v_k_2398_, lean_object* v_cleanupAnnotations_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2405_; lean_object* v_res_2406_; 
v_cleanupAnnotations_boxed_2405_ = lean_unbox(v_cleanupAnnotations_2399_);
v_res_2406_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(v_00_u03b1_2396_, v_e_2397_, v_k_2398_, v_cleanupAnnotations_boxed_2405_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(lean_object* v_msg_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v___f_2413_; lean_object* v___x_1717__overap_2414_; lean_object* v___x_2415_; 
v___f_2413_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1717__overap_2414_ = lean_panic_fn_borrowed(v___f_2413_, v_msg_2407_);
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
lean_inc(v___y_2409_);
lean_inc_ref(v___y_2408_);
v___x_2415_ = lean_apply_5(v___x_1717__overap_2414_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, lean_box(0));
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1___boxed(lean_object* v_msg_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v_msg_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0(lean_object* v_xs_2423_, lean_object* v_x_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = lean_array_get_size(v_xs_2423_);
v___x_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0___boxed(lean_object* v_xs_2432_, lean_object* v_x_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Lean_Elab_WF_varyingVarNames___lam__0(v_xs_2432_, v_x_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec_ref(v_x_2433_);
lean_dec_ref(v_xs_2432_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(lean_object* v_as_2440_, size_t v_sz_2441_, size_t v_i_2442_, lean_object* v_b_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_a_2449_; uint8_t v___x_2453_; 
v___x_2453_ = lean_usize_dec_lt(v_i_2442_, v_sz_2441_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; 
v___x_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2454_, 0, v_b_2443_);
return v___x_2454_;
}
else
{
lean_object* v_snd_2455_; lean_object* v_fst_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2500_; 
v_snd_2455_ = lean_ctor_get(v_b_2443_, 1);
v_fst_2456_ = lean_ctor_get(v_b_2443_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v_b_2443_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2458_ = v_b_2443_;
v_isShared_2459_ = v_isSharedCheck_2500_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_snd_2455_);
lean_inc(v_fst_2456_);
lean_dec(v_b_2443_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2500_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v_array_2460_; lean_object* v_start_2461_; lean_object* v_stop_2462_; uint8_t v___x_2463_; 
v_array_2460_ = lean_ctor_get(v_snd_2455_, 0);
v_start_2461_ = lean_ctor_get(v_snd_2455_, 1);
v_stop_2462_ = lean_ctor_get(v_snd_2455_, 2);
v___x_2463_ = lean_nat_dec_lt(v_start_2461_, v_stop_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2465_; 
if (v_isShared_2459_ == 0)
{
v___x_2465_ = v___x_2458_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_fst_2456_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_snd_2455_);
v___x_2465_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
lean_object* v___x_2466_; 
v___x_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
return v___x_2466_;
}
}
else
{
lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2496_; 
lean_inc(v_stop_2462_);
lean_inc(v_start_2461_);
lean_inc_ref(v_array_2460_);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_snd_2455_);
if (v_isSharedCheck_2496_ == 0)
{
lean_object* v_unused_2497_; lean_object* v_unused_2498_; lean_object* v_unused_2499_; 
v_unused_2497_ = lean_ctor_get(v_snd_2455_, 2);
lean_dec(v_unused_2497_);
v_unused_2498_ = lean_ctor_get(v_snd_2455_, 1);
lean_dec(v_unused_2498_);
v_unused_2499_ = lean_ctor_get(v_snd_2455_, 0);
lean_dec(v_unused_2499_);
v___x_2469_ = v_snd_2455_;
v_isShared_2470_ = v_isSharedCheck_2496_;
goto v_resetjp_2468_;
}
else
{
lean_dec(v_snd_2455_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2496_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2471_ = lean_array_fget(v_array_2460_, v_start_2461_);
v___x_2472_ = lean_unsigned_to_nat(1u);
v___x_2473_ = lean_nat_add(v_start_2461_, v___x_2472_);
lean_dec(v_start_2461_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 1, v___x_2473_);
v___x_2475_ = v___x_2469_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_array_2460_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2495_, 2, v_stop_2462_);
v___x_2475_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v_a_2476_ = lean_array_uget_borrowed(v_as_2440_, v_i_2442_);
v___x_2477_ = l_Lean_Expr_fvarId_x21(v_a_2476_);
v___x_2478_ = l_Lean_FVarId_getUserName___redArg(v___x_2477_, v___y_2444_, v___y_2445_, v___y_2446_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2480_; lean_object* v___x_2482_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2479_);
lean_dec_ref_known(v___x_2478_, 1);
v___x_2480_ = lean_array_push(v_fst_2456_, v_a_2479_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 1, v___x_2475_);
lean_ctor_set(v___x_2458_, 0, v___x_2480_);
v___x_2482_ = v___x_2458_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2480_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v___x_2475_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
v_a_2449_ = v___x_2482_;
goto v___jp_2448_;
}
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec_ref(v___x_2475_);
lean_del_object(v___x_2458_);
lean_dec(v_fst_2456_);
v_a_2484_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2478_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2478_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
else
{
lean_object* v___x_2493_; 
lean_dec_ref_known(v___x_2471_, 1);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 1, v___x_2475_);
v___x_2493_ = v___x_2458_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_fst_2456_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v___x_2475_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
v_a_2449_ = v___x_2493_;
goto v___jp_2448_;
}
}
}
}
}
}
}
v___jp_2448_:
{
size_t v___x_2450_; size_t v___x_2451_; 
v___x_2450_ = ((size_t)1ULL);
v___x_2451_ = lean_usize_add(v_i_2442_, v___x_2450_);
v_i_2442_ = v___x_2451_;
v_b_2443_ = v_a_2449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg___boxed(lean_object* v_as_2501_, lean_object* v_sz_2502_, lean_object* v_i_2503_, lean_object* v_b_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
size_t v_sz_boxed_2509_; size_t v_i_boxed_2510_; lean_object* v_res_2511_; 
v_sz_boxed_2509_ = lean_unbox_usize(v_sz_2502_);
lean_dec(v_sz_2502_);
v_i_boxed_2510_ = lean_unbox_usize(v_i_2503_);
lean_dec(v_i_2503_);
v_res_2511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2501_, v_sz_boxed_2509_, v_i_boxed_2510_, v_b_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec_ref(v_as_2501_);
return v_res_2511_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2514_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1));
v___x_2515_ = lean_unsigned_to_nat(4u);
v___x_2516_ = lean_unsigned_to_nat(119u);
v___x_2517_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2518_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2519_ = l_mkPanicMessageWithDecl(v___x_2518_, v___x_2517_, v___x_2516_, v___x_2515_, v___x_2514_);
return v___x_2519_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2521_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3));
v___x_2522_ = lean_unsigned_to_nat(4u);
v___x_2523_ = lean_unsigned_to_nat(120u);
v___x_2524_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2525_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2526_ = l_mkPanicMessageWithDecl(v___x_2525_, v___x_2524_, v___x_2523_, v___x_2522_, v___x_2521_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1(lean_object* v_a_2529_, lean_object* v_fixedParamPerms_2530_, lean_object* v_preDefIdx_2531_, lean_object* v_xs_2532_, lean_object* v_x_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2539_ = lean_array_get_size(v_xs_2532_);
v___x_2540_ = lean_nat_dec_eq(v___x_2539_, v_a_2529_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2);
v___x_2542_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2541_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
return v___x_2542_;
}
else
{
lean_object* v_perms_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v_perms_2543_ = lean_ctor_get(v_fixedParamPerms_2530_, 1);
v___x_2544_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2545_ = lean_array_get_borrowed(v___x_2544_, v_perms_2543_, v_preDefIdx_2531_);
v___x_2546_ = lean_array_get_size(v___x_2545_);
v___x_2547_ = lean_nat_dec_eq(v___x_2546_, v_a_2529_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4);
v___x_2549_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2548_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
return v___x_2549_;
}
else
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; size_t v_sz_2554_; size_t v___x_2555_; lean_object* v___x_2556_; 
v___x_2550_ = lean_unsigned_to_nat(0u);
v___x_2551_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5));
lean_inc(v___x_2545_);
v___x_2552_ = l_Array_toSubarray___redArg(v___x_2545_, v___x_2550_, v___x_2546_);
v___x_2553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2551_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v_sz_2554_ = lean_array_size(v_xs_2532_);
v___x_2555_ = ((size_t)0ULL);
v___x_2556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_xs_2532_, v_sz_2554_, v___x_2555_, v___x_2553_, v___y_2534_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2565_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2565_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2565_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v_fst_2561_; lean_object* v___x_2563_; 
v_fst_2561_ = lean_ctor_get(v_a_2557_, 0);
lean_inc(v_fst_2561_);
lean_dec(v_a_2557_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v_fst_2561_);
v___x_2563_ = v___x_2559_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_fst_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
v_a_2566_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2556_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2556_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___boxed(lean_object* v_a_2574_, lean_object* v_fixedParamPerms_2575_, lean_object* v_preDefIdx_2576_, lean_object* v_xs_2577_, lean_object* v_x_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Lean_Elab_WF_varyingVarNames___lam__1(v_a_2574_, v_fixedParamPerms_2575_, v_preDefIdx_2576_, v_xs_2577_, v_x_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec_ref(v_x_2578_);
lean_dec_ref(v_xs_2577_);
lean_dec(v_preDefIdx_2576_);
lean_dec_ref(v_fixedParamPerms_2575_);
lean_dec(v_a_2574_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object* v_fixedParamPerms_2586_, lean_object* v_preDefIdx_2587_, lean_object* v_preDef_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v_type_2594_; lean_object* v_value_2595_; lean_object* v___f_2596_; uint8_t v___x_2597_; lean_object* v___x_2598_; 
v_type_2594_ = lean_ctor_get(v_preDef_2588_, 6);
lean_inc_ref(v_type_2594_);
v_value_2595_ = lean_ctor_get(v_preDef_2588_, 7);
lean_inc_ref(v_value_2595_);
lean_dec_ref(v_preDef_2588_);
v___f_2596_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___closed__0));
v___x_2597_ = 0;
v___x_2598_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_value_2595_, v___f_2596_, v___x_2597_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___f_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc_n(v_a_2599_, 2);
lean_dec_ref_known(v___x_2598_, 1);
v___f_2600_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_varyingVarNames___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2600_, 0, v_a_2599_);
lean_closure_set(v___f_2600_, 1, v_fixedParamPerms_2586_);
lean_closure_set(v___f_2600_, 2, v_preDefIdx_2587_);
v___x_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2601_, 0, v_a_2599_);
v___x_2602_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2594_, v___x_2601_, v___f_2600_, v___x_2597_, v___x_2597_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_);
return v___x_2602_;
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_dec_ref(v_type_2594_);
lean_dec(v_preDefIdx_2587_);
lean_dec_ref(v_fixedParamPerms_2586_);
v_a_2603_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2598_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2598_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___boxed(lean_object* v_fixedParamPerms_2611_, lean_object* v_preDefIdx_2612_, lean_object* v_preDef_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Lean_Elab_WF_varyingVarNames(v_fixedParamPerms_2611_, v_preDefIdx_2612_, v_preDef_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(lean_object* v_as_2620_, size_t v_sz_2621_, size_t v_i_2622_, lean_object* v_b_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v___x_2629_; 
v___x_2629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2620_, v_sz_2621_, v_i_2622_, v_b_2623_, v___y_2624_, v___y_2626_, v___y_2627_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___boxed(lean_object* v_as_2630_, lean_object* v_sz_2631_, lean_object* v_i_2632_, lean_object* v_b_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
size_t v_sz_boxed_2639_; size_t v_i_boxed_2640_; lean_object* v_res_2641_; 
v_sz_boxed_2639_ = lean_unbox_usize(v_sz_2631_);
lean_dec(v_sz_2631_);
v_i_boxed_2640_ = lean_unbox_usize(v_i_2632_);
lean_dec(v_i_2632_);
v_res_2641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(v_as_2630_, v_sz_boxed_2639_, v_i_boxed_2640_, v_b_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec_ref(v_as_2630_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(lean_object* v_msg_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v___f_2648_; lean_object* v___x_1720__overap_2649_; lean_object* v___x_2650_; 
v___f_2648_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1720__overap_2649_ = lean_panic_fn_borrowed(v___f_2648_, v_msg_2642_);
lean_inc(v___y_2646_);
lean_inc_ref(v___y_2645_);
lean_inc(v___y_2644_);
lean_inc_ref(v___y_2643_);
v___x_2650_ = lean_apply_5(v___x_1720__overap_2649_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, lean_box(0));
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0___boxed(lean_object* v_msg_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v_msg_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
return v_res_2657_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2658_; double v___x_2659_; 
v___x_2658_ = lean_unsigned_to_nat(0u);
v___x_2659_ = lean_float_of_nat(v___x_2658_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(lean_object* v_cls_2663_, lean_object* v_msg_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v_ref_2670_; lean_object* v___x_2671_; lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2716_; 
v_ref_2670_ = lean_ctor_get(v___y_2667_, 5);
v___x_2671_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msg_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2674_ = v___x_2671_;
v_isShared_2675_ = v_isSharedCheck_2716_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2716_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2676_; lean_object* v_traceState_2677_; lean_object* v_env_2678_; lean_object* v_nextMacroScope_2679_; lean_object* v_ngen_2680_; lean_object* v_auxDeclNGen_2681_; lean_object* v_cache_2682_; lean_object* v_messages_2683_; lean_object* v_infoState_2684_; lean_object* v_snapshotTasks_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2715_; 
v___x_2676_ = lean_st_ref_take(v___y_2668_);
v_traceState_2677_ = lean_ctor_get(v___x_2676_, 4);
v_env_2678_ = lean_ctor_get(v___x_2676_, 0);
v_nextMacroScope_2679_ = lean_ctor_get(v___x_2676_, 1);
v_ngen_2680_ = lean_ctor_get(v___x_2676_, 2);
v_auxDeclNGen_2681_ = lean_ctor_get(v___x_2676_, 3);
v_cache_2682_ = lean_ctor_get(v___x_2676_, 5);
v_messages_2683_ = lean_ctor_get(v___x_2676_, 6);
v_infoState_2684_ = lean_ctor_get(v___x_2676_, 7);
v_snapshotTasks_2685_ = lean_ctor_get(v___x_2676_, 8);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2687_ = v___x_2676_;
v_isShared_2688_ = v_isSharedCheck_2715_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_snapshotTasks_2685_);
lean_inc(v_infoState_2684_);
lean_inc(v_messages_2683_);
lean_inc(v_cache_2682_);
lean_inc(v_traceState_2677_);
lean_inc(v_auxDeclNGen_2681_);
lean_inc(v_ngen_2680_);
lean_inc(v_nextMacroScope_2679_);
lean_inc(v_env_2678_);
lean_dec(v___x_2676_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2715_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
uint64_t v_tid_2689_; lean_object* v_traces_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2714_; 
v_tid_2689_ = lean_ctor_get_uint64(v_traceState_2677_, sizeof(void*)*1);
v_traces_2690_ = lean_ctor_get(v_traceState_2677_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_traceState_2677_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2692_ = v_traceState_2677_;
v_isShared_2693_ = v_isSharedCheck_2714_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_traces_2690_);
lean_dec(v_traceState_2677_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2714_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; double v___x_2695_; uint8_t v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2694_ = lean_box(0);
v___x_2695_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0);
v___x_2696_ = 0;
v___x_2697_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1));
v___x_2698_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2698_, 0, v_cls_2663_);
lean_ctor_set(v___x_2698_, 1, v___x_2694_);
lean_ctor_set(v___x_2698_, 2, v___x_2697_);
lean_ctor_set_float(v___x_2698_, sizeof(void*)*3, v___x_2695_);
lean_ctor_set_float(v___x_2698_, sizeof(void*)*3 + 8, v___x_2695_);
lean_ctor_set_uint8(v___x_2698_, sizeof(void*)*3 + 16, v___x_2696_);
v___x_2699_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2));
v___x_2700_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v_a_2672_);
lean_ctor_set(v___x_2700_, 2, v___x_2699_);
lean_inc(v_ref_2670_);
v___x_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2701_, 0, v_ref_2670_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = l_Lean_PersistentArray_push___redArg(v_traces_2690_, v___x_2701_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v___x_2702_);
v___x_2704_ = v___x_2692_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2702_);
lean_ctor_set_uint64(v_reuseFailAlloc_2713_, sizeof(void*)*1, v_tid_2689_);
v___x_2704_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2706_; 
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 4, v___x_2704_);
v___x_2706_ = v___x_2687_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_env_2678_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v_nextMacroScope_2679_);
lean_ctor_set(v_reuseFailAlloc_2712_, 2, v_ngen_2680_);
lean_ctor_set(v_reuseFailAlloc_2712_, 3, v_auxDeclNGen_2681_);
lean_ctor_set(v_reuseFailAlloc_2712_, 4, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2712_, 5, v_cache_2682_);
lean_ctor_set(v_reuseFailAlloc_2712_, 6, v_messages_2683_);
lean_ctor_set(v_reuseFailAlloc_2712_, 7, v_infoState_2684_);
lean_ctor_set(v_reuseFailAlloc_2712_, 8, v_snapshotTasks_2685_);
v___x_2706_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2710_; 
v___x_2707_ = lean_st_ref_set(v___y_2668_, v___x_2706_);
v___x_2708_ = lean_box(0);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2708_);
v___x_2710_ = v___x_2674_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2708_);
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
lean_object* v_declName_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v_declName_2750_ = lean_ctor_get(v_unaryPreDefNonRec_2734_, 3);
lean_inc(v_declName_2750_);
lean_dec_ref(v_unaryPreDefNonRec_2734_);
v___x_2751_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v___x_2735_, v_params_2739_);
v___x_2752_ = l_Lean_mkConst(v_declName_2750_, v_us_2736_);
v___x_2753_ = l_Lean_mkAppN(v___x_2752_, v___x_2751_);
lean_dec_ref(v___x_2751_);
v___x_2754_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_2737_, v___x_2753_, v___x_2738_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; uint8_t v___x_2758_; uint8_t v___x_2759_; lean_object* v___x_2760_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2755_);
lean_dec_ref_known(v___x_2754_, 1);
v___x_2756_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_2735_, v_params_2739_);
v___x_2757_ = l_Lean_Expr_beta(v_a_2755_, v___x_2756_);
v___x_2758_ = 0;
v___x_2759_ = 1;
v___x_2760_ = l_Lean_Meta_mkLambdaFVars(v_params_2739_, v___x_2757_, v___x_2758_, v___x_2747_, v___x_2758_, v___x_2747_, v___x_2759_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
return v___x_2760_;
}
else
{
return v___x_2754_;
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
lean_object* v_v_2805_; lean_object* v_perms_2806_; lean_object* v_ref_2807_; uint8_t v_kind_2808_; lean_object* v_levelParams_2809_; lean_object* v_modifiers_2810_; lean_object* v_declName_2811_; lean_object* v_binders_2812_; lean_object* v_numSectionVars_2813_; lean_object* v_type_2814_; lean_object* v_termination_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2866_; 
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
v_isSharedCheck_2866_ = !lean_is_exclusive(v_v_2805_);
if (v_isSharedCheck_2866_ == 0)
{
lean_object* v_unused_2867_; 
v_unused_2867_ = lean_ctor_get(v_v_2805_, 7);
lean_dec(v_unused_2867_);
v___x_2817_ = v_v_2805_;
v_isShared_2818_ = v_isSharedCheck_2866_;
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
v_isShared_2818_ = v_isSharedCheck_2866_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v_bs_x27_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___f_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; lean_object* v___x_2828_; 
v___x_2819_ = lean_unsigned_to_nat(0u);
v_bs_x27_2820_ = lean_array_uset(v_bs_2797_, v_i_2796_, v___x_2819_);
v___x_2821_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
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
lean_object* v_a_2829_; lean_object* v_options_2838_; uint8_t v_hasTrace_2839_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_a_2829_);
lean_dec_ref_known(v___x_2828_, 1);
v_options_2838_ = lean_ctor_get(v___y_2800_, 2);
v_hasTrace_2839_ = lean_ctor_get_uint8(v_options_2838_, sizeof(void*)*1);
if (v_hasTrace_2839_ == 0)
{
goto v___jp_2830_;
}
else
{
lean_object* v_inheritedTraceOptions_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
v_inheritedTraceOptions_2840_ = lean_ctor_get(v___y_2800_, 13);
v___x_2841_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2842_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6);
v___x_2843_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2840_, v_options_2838_, v___x_2842_);
if (v___x_2843_ == 0)
{
goto v___jp_2830_;
}
else
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
lean_inc(v_declName_2811_);
v___x_2844_ = l_Lean_MessageData_ofName(v_declName_2811_);
v___x_2845_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8);
v___x_2846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2844_);
lean_ctor_set(v___x_2846_, 1, v___x_2845_);
lean_inc(v_a_2829_);
v___x_2847_ = l_Lean_MessageData_ofExpr(v_a_2829_);
v___x_2848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2846_);
lean_ctor_set(v___x_2848_, 1, v___x_2847_);
v___x_2849_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v___x_2841_, v___x_2848_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_dec_ref_known(v___x_2849_, 1);
goto v___jp_2830_;
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
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
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
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
v_a_2858_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2828_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2828_);
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
v___x_2916_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_2927_; lean_object* v_nextMacroScope_2928_; lean_object* v_ngen_2929_; lean_object* v_auxDeclNGen_2930_; lean_object* v_traceState_2931_; lean_object* v_messages_2932_; lean_object* v_infoState_2933_; lean_object* v_snapshotTasks_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2960_; 
v___x_2927_ = lean_st_ref_take(v___y_2925_);
v_nextMacroScope_2928_ = lean_ctor_get(v___x_2927_, 1);
v_ngen_2929_ = lean_ctor_get(v___x_2927_, 2);
v_auxDeclNGen_2930_ = lean_ctor_get(v___x_2927_, 3);
v_traceState_2931_ = lean_ctor_get(v___x_2927_, 4);
v_messages_2932_ = lean_ctor_get(v___x_2927_, 6);
v_infoState_2933_ = lean_ctor_get(v___x_2927_, 7);
v_snapshotTasks_2934_ = lean_ctor_get(v___x_2927_, 8);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2960_ == 0)
{
lean_object* v_unused_2961_; lean_object* v_unused_2962_; 
v_unused_2961_ = lean_ctor_get(v___x_2927_, 5);
lean_dec(v_unused_2961_);
v_unused_2962_ = lean_ctor_get(v___x_2927_, 0);
lean_dec(v_unused_2962_);
v___x_2936_ = v___x_2927_;
v_isShared_2937_ = v_isSharedCheck_2960_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_snapshotTasks_2934_);
lean_inc(v_infoState_2933_);
lean_inc(v_messages_2932_);
lean_inc(v_traceState_2931_);
lean_inc(v_auxDeclNGen_2930_);
lean_inc(v_ngen_2929_);
lean_inc(v_nextMacroScope_2928_);
lean_dec(v___x_2927_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2960_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2938_; lean_object* v___x_2940_; 
v___x_2938_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 5, v___x_2938_);
lean_ctor_set(v___x_2936_, 0, v_env_2923_);
v___x_2940_ = v___x_2936_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_env_2923_);
lean_ctor_set(v_reuseFailAlloc_2959_, 1, v_nextMacroScope_2928_);
lean_ctor_set(v_reuseFailAlloc_2959_, 2, v_ngen_2929_);
lean_ctor_set(v_reuseFailAlloc_2959_, 3, v_auxDeclNGen_2930_);
lean_ctor_set(v_reuseFailAlloc_2959_, 4, v_traceState_2931_);
lean_ctor_set(v_reuseFailAlloc_2959_, 5, v___x_2938_);
lean_ctor_set(v_reuseFailAlloc_2959_, 6, v_messages_2932_);
lean_ctor_set(v_reuseFailAlloc_2959_, 7, v_infoState_2933_);
lean_ctor_set(v_reuseFailAlloc_2959_, 8, v_snapshotTasks_2934_);
v___x_2940_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v_mctx_2943_; lean_object* v_zetaDeltaFVarIds_2944_; lean_object* v_postponed_2945_; lean_object* v_diag_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2957_; 
v___x_2941_ = lean_st_ref_set(v___y_2925_, v___x_2940_);
v___x_2942_ = lean_st_ref_take(v___y_2924_);
v_mctx_2943_ = lean_ctor_get(v___x_2942_, 0);
v_zetaDeltaFVarIds_2944_ = lean_ctor_get(v___x_2942_, 2);
v_postponed_2945_ = lean_ctor_get(v___x_2942_, 3);
v_diag_2946_ = lean_ctor_get(v___x_2942_, 4);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2957_ == 0)
{
lean_object* v_unused_2958_; 
v_unused_2958_ = lean_ctor_get(v___x_2942_, 1);
lean_dec(v_unused_2958_);
v___x_2948_ = v___x_2942_;
v_isShared_2949_ = v_isSharedCheck_2957_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_diag_2946_);
lean_inc(v_postponed_2945_);
lean_inc(v_zetaDeltaFVarIds_2944_);
lean_inc(v_mctx_2943_);
lean_dec(v___x_2942_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2957_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2950_; lean_object* v___x_2952_; 
v___x_2950_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3);
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 1, v___x_2950_);
v___x_2952_ = v___x_2948_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_mctx_2943_);
lean_ctor_set(v_reuseFailAlloc_2956_, 1, v___x_2950_);
lean_ctor_set(v_reuseFailAlloc_2956_, 2, v_zetaDeltaFVarIds_2944_);
lean_ctor_set(v_reuseFailAlloc_2956_, 3, v_postponed_2945_);
lean_ctor_set(v_reuseFailAlloc_2956_, 4, v_diag_2946_);
v___x_2952_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2953_ = lean_st_ref_set(v___y_2924_, v___x_2952_);
v___x_2954_ = lean_box(0);
v___x_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
return v___x_2955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___boxed(lean_object* v_env_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2963_, v___y_2964_, v___y_2965_);
lean_dec(v___y_2965_);
lean_dec(v___y_2964_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(lean_object* v_env_2968_, lean_object* v_x_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v___x_2975_; lean_object* v_env_2976_; lean_object* v_a_2978_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2975_ = lean_st_ref_get(v___y_2973_);
v_env_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc_ref(v_env_2976_);
lean_dec(v___x_2975_);
v___x_2988_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2968_, v___y_2971_, v___y_2973_);
lean_dec_ref(v___x_2988_);
lean_inc(v___y_2973_);
lean_inc_ref(v___y_2972_);
lean_inc(v___y_2971_);
lean_inc_ref(v___y_2970_);
v___x_2989_ = lean_apply_5(v_x_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, lean_box(0));
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref_known(v___x_2989_, 1);
v___x_2991_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2976_, v___y_2971_, v___y_2973_);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_2998_ == 0)
{
lean_object* v_unused_2999_; 
v_unused_2999_ = lean_ctor_get(v___x_2991_, 0);
lean_dec(v_unused_2999_);
v___x_2993_ = v___x_2991_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_dec(v___x_2991_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v_a_2990_);
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2990_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
else
{
lean_object* v_a_3000_; 
v_a_3000_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_3000_);
lean_dec_ref_known(v___x_2989_, 1);
v_a_2978_ = v_a_3000_;
goto v___jp_2977_;
}
v___jp_2977_:
{
lean_object* v___x_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
v___x_2979_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2976_, v___y_2971_, v___y_2973_);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_2986_ == 0)
{
lean_object* v_unused_2987_; 
v_unused_2987_ = lean_ctor_get(v___x_2979_, 0);
lean_dec(v_unused_2987_);
v___x_2981_ = v___x_2979_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_dec(v___x_2979_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
lean_ctor_set_tag(v___x_2981_, 1);
lean_ctor_set(v___x_2981_, 0, v_a_2978_);
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2978_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___boxed(lean_object* v_env_3001_, lean_object* v_x_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
lean_object* v_res_3008_; 
v_res_3008_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_3001_, v_x_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object* v_fixedParamPerms_3009_, lean_object* v_argsPacker_3010_, lean_object* v_preDefs_3011_, lean_object* v_unaryPreDefNonRec_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_){
_start:
{
lean_object* v___x_3018_; lean_object* v_levelParams_3019_; lean_object* v_env_3020_; lean_object* v___x_3021_; lean_object* v_us_3022_; lean_object* v___f_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3018_ = lean_st_ref_get(v_a_3016_);
v_levelParams_3019_ = lean_ctor_get(v_unaryPreDefNonRec_3012_, 1);
v_env_3020_ = lean_ctor_get(v___x_3018_, 0);
lean_inc_ref(v_env_3020_);
lean_dec(v___x_3018_);
v___x_3021_ = lean_box(0);
lean_inc(v_levelParams_3019_);
v_us_3022_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_3019_, v___x_3021_);
v___f_3023_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3023_, 0, v_unaryPreDefNonRec_3012_);
lean_closure_set(v___f_3023_, 1, v_preDefs_3011_);
lean_closure_set(v___f_3023_, 2, v_fixedParamPerms_3009_);
lean_closure_set(v___f_3023_, 3, v_us_3022_);
lean_closure_set(v___f_3023_, 4, v_argsPacker_3010_);
v___x_3024_ = l_Lean_Environment_unlockAsync(v_env_3020_);
v___x_3025_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v___x_3024_, v___f_3023_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___boxed(lean_object* v_fixedParamPerms_3026_, lean_object* v_argsPacker_3027_, lean_object* v_preDefs_3028_, lean_object* v_unaryPreDefNonRec_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fixedParamPerms_3026_, v_argsPacker_3027_, v_preDefs_3028_, v_unaryPreDefNonRec_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
lean_dec(v_a_3033_);
lean_dec_ref(v_a_3032_);
lean_dec(v_a_3031_);
lean_dec_ref(v_a_3030_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(lean_object* v_fixedParamPerms_3036_, lean_object* v_unaryPreDefNonRec_3037_, lean_object* v_us_3038_, lean_object* v_argsPacker_3039_, lean_object* v_as_3040_, size_t v_sz_3041_, size_t v_i_3042_, lean_object* v_bs_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_3036_, v_unaryPreDefNonRec_3037_, v_us_3038_, v_argsPacker_3039_, v_sz_3041_, v_i_3042_, v_bs_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___boxed(lean_object* v_fixedParamPerms_3050_, lean_object* v_unaryPreDefNonRec_3051_, lean_object* v_us_3052_, lean_object* v_argsPacker_3053_, lean_object* v_as_3054_, lean_object* v_sz_3055_, lean_object* v_i_3056_, lean_object* v_bs_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
size_t v_sz_boxed_3063_; size_t v_i_boxed_3064_; lean_object* v_res_3065_; 
v_sz_boxed_3063_ = lean_unbox_usize(v_sz_3055_);
lean_dec(v_sz_3055_);
v_i_boxed_3064_ = lean_unbox_usize(v_i_3056_);
lean_dec(v_i_3056_);
v_res_3065_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(v_fixedParamPerms_3050_, v_unaryPreDefNonRec_3051_, v_us_3052_, v_argsPacker_3053_, v_as_3054_, v_sz_boxed_3063_, v_i_boxed_3064_, v_bs_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec_ref(v_as_3054_);
lean_dec_ref(v_fixedParamPerms_3050_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(lean_object* v_env_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v___x_3072_; 
v___x_3072_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3066_, v___y_3068_, v___y_3070_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___boxed(lean_object* v_env_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(v_env_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(lean_object* v_00_u03b1_3080_, lean_object* v_env_3081_, lean_object* v_x_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v___x_3088_; 
v___x_3088_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_3081_, v_x_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___boxed(lean_object* v_00_u03b1_3089_, lean_object* v_env_3090_, lean_object* v_x_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(v_00_u03b1_3089_, v_env_3090_, v_x_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
return v_res_3097_;
}
}
lean_object* runtime_initialize_Lean_Meta_ArgsPacker(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Eqns(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_PackMutual(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
