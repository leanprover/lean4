// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.JoinPoint
// Imports: public import Lean.Elab.Tactic.VCGen.Context public import Lean.Elab.Tactic.VCGen.WPApp import Lean.Meta.Sym.InferType import Lean.Meta.Sym.InstantiateMVarsS import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.AbstractS import Lean.Meta.Sym.Intro import Lean.Elab.Tactic.VCGen.Util import Lean.Elab.Tactic.VCGen.Reduce
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
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
extern lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedJump_default;
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkAndN(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_mkAnd(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_mkOr(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_betaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_dec(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkForallFVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_Pred(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_prog(lean_object*);
lean_object* l_Lean_Expr_fvarId_x3f(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Tactic_Do_isJP(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_Prog(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_getNumJoinParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEqFast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_introN(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_instAL(lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "instCompleteLatticePi"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(216, 67, 57, 247, 147, 127, 99, 32)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Assertion"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "toCompleteLattice"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(114, 159, 99, 164, 90, 177, 79, 245)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(224, 154, 70, 190, 135, 75, 167, 26)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(114, 159, 99, 164, 90, 177, 79, 245)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(178, 103, 243, 133, 246, 244, 77, 98)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__7___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__7___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3_spec__3_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3_spec__3_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "top"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "vcgen +jp: `"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__2;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` is not a type"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__2___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__12_spec__15_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__12___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(41, 174, 7, 105, 99, 77, 97, 125)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "__do_jp_spec"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(65, 4, 59, 172, 214, 16, 186, 31)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__4_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "vcgen +jp: failed to introduce the proof of"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3_spec__3_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__12_spec__15_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__7___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__0;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "vcgen +jp: the jump"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\ndoes not have "};
static const lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " states"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__7(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Exists"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 29, 48, 135, 199, 176, 149, 70)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "vcgen +jp: expected a disjunction"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inr"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__4_value),LEAN_SCALAR_PTR_LITERAL(100, 75, 208, 15, 82, 176, 164, 239)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__6;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inl"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__7_value),LEAN_SCALAR_PTR_LITERAL(115, 149, 175, 58, 225, 90, 105, 195)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PUnit"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 153, 158, 141, 176, 162, 235, 153)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__3;
static const lean_array_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__0_value;
static const lean_array_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5_spec__11(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "vcgen +jp: unexpected equations"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__4_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__6_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__4_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__8_value),LEAN_SCALAR_PTR_LITERAL(58, 46, 244, 208, 18, 71, 77, 162)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__8_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "vcgen +jp: empty path into"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "vcgen +jp: unexpected binder"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__1;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 29, 48, 135, 199, 176, 149, 70)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__8_value),LEAN_SCALAR_PTR_LITERAL(74, 55, 158, 60, 144, 34, 77, 172)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "vcgen +jp: missing local for"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0(lean_object* v_as_10_, size_t v_sz_11_, size_t v_i_12_, lean_object* v_b_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
uint8_t v___x_21_; 
v___x_21_ = lean_usize_dec_lt(v_i_12_, v_sz_11_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; 
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_b_13_);
return v___x_22_;
}
else
{
lean_object* v_snd_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_62_; 
v_snd_23_ = lean_ctor_get(v_b_13_, 1);
v_isSharedCheck_62_ = !lean_is_exclusive(v_b_13_);
if (v_isSharedCheck_62_ == 0)
{
lean_object* v_unused_63_; 
v_unused_63_ = lean_ctor_get(v_b_13_, 0);
lean_dec(v_unused_63_);
v___x_25_ = v_b_13_;
v_isShared_26_ = v_isSharedCheck_62_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_snd_23_);
lean_dec(v_b_13_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_62_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_33_; uint8_t v___x_34_; 
v___x_33_ = l_Lean_Expr_cleanupAnnotations(v_snd_23_);
v___x_34_ = l_Lean_Expr_isApp(v___x_33_);
if (v___x_34_ == 0)
{
lean_dec_ref(v___x_33_);
goto v___jp_27_;
}
else
{
lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_35_ = l_Lean_Expr_appFnCleanup___redArg(v___x_33_);
v___x_36_ = l_Lean_Expr_isApp(v___x_35_);
if (v___x_36_ == 0)
{
lean_dec_ref(v___x_35_);
lean_dec_ref(v___x_33_);
goto v___jp_27_;
}
else
{
lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_37_ = l_Lean_Expr_appFnCleanup___redArg(v___x_35_);
lean_dec_ref(v___x_35_);
v___x_38_ = l_Lean_Expr_isApp(v___x_37_);
if (v___x_38_ == 0)
{
lean_dec_ref(v___x_37_);
lean_dec_ref(v___x_33_);
goto v___jp_27_;
}
else
{
lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; 
v___x_39_ = l_Lean_Expr_appFnCleanup___redArg(v___x_37_);
lean_dec_ref(v___x_37_);
v___x_40_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__4));
v___x_41_ = l_Lean_Expr_isConstOf(v___x_39_, v___x_40_);
lean_dec_ref(v___x_39_);
if (v___x_41_ == 0)
{
lean_dec_ref(v___x_33_);
goto v___jp_27_;
}
else
{
lean_object* v_arg_42_; lean_object* v___x_43_; lean_object* v_a_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
lean_del_object(v___x_25_);
lean_dec(v_snd_23_);
v_arg_42_ = lean_ctor_get(v___x_33_, 1);
lean_inc_ref(v_arg_42_);
lean_dec_ref(v___x_33_);
v___x_43_ = lean_box(0);
v_a_44_ = lean_array_uget_borrowed(v_as_10_, v_i_12_);
v___x_45_ = lean_unsigned_to_nat(1u);
v___x_46_ = lean_mk_empty_array_with_capacity(v___x_45_);
lean_inc(v_a_44_);
v___x_47_ = lean_array_push(v___x_46_, v_a_44_);
v___x_48_ = l_Lean_Meta_Sym_betaS(v_arg_42_, v___x_47_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_object* v_a_49_; lean_object* v___x_50_; size_t v___x_51_; size_t v___x_52_; 
v_a_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc(v_a_49_);
lean_dec_ref_known(v___x_48_, 1);
v___x_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_43_);
lean_ctor_set(v___x_50_, 1, v_a_49_);
v___x_51_ = ((size_t)1ULL);
v___x_52_ = lean_usize_add(v_i_12_, v___x_51_);
v_i_12_ = v___x_52_;
v_b_13_ = v___x_50_;
goto _start;
}
else
{
lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_61_; 
v_a_54_ = lean_ctor_get(v___x_48_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_48_);
if (v_isSharedCheck_61_ == 0)
{
v___x_56_ = v___x_48_;
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_48_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_54_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
}
}
}
v___jp_27_:
{
lean_object* v___x_28_; lean_object* v___x_30_; 
v___x_28_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__0));
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 0, v___x_28_);
v___x_30_ = v___x_25_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v___x_28_);
lean_ctor_set(v_reuseFailAlloc_32_, 1, v_snd_23_);
v___x_30_ = v_reuseFailAlloc_32_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
lean_object* v___x_31_; 
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
return v___x_31_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___boxed(lean_object* v_as_64_, lean_object* v_sz_65_, lean_object* v_i_66_, lean_object* v_b_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
size_t v_sz_boxed_75_; size_t v_i_boxed_76_; lean_object* v_res_77_; 
v_sz_boxed_75_ = lean_unbox_usize(v_sz_65_);
lean_dec(v_sz_65_);
v_i_boxed_76_ = lean_unbox_usize(v_i_66_);
lean_dec(v_i_66_);
v_res_77_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0(v_as_64_, v_sz_boxed_75_, v_i_boxed_76_, v_b_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
lean_dec(v___y_69_);
lean_dec_ref(v___y_68_);
lean_dec_ref(v_as_64_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f(lean_object* v_instCL_93_, lean_object* v_ss_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; size_t v_sz_104_; size_t v___x_105_; lean_object* v___x_106_; 
v___x_102_ = lean_box(0);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v_instCL_93_);
v_sz_104_ = lean_array_size(v_ss_94_);
v___x_105_ = ((size_t)0ULL);
v___x_106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0(v_ss_94_, v_sz_104_, v___x_105_, v___x_103_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_147_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_147_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_147_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_147_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v_fst_111_; lean_object* v_snd_112_; 
v_fst_111_ = lean_ctor_get(v_a_107_, 0);
lean_inc(v_fst_111_);
v_snd_112_ = lean_ctor_get(v_a_107_, 1);
lean_inc(v_snd_112_);
lean_dec(v_a_107_);
if (lean_obj_tag(v_fst_111_) == 0)
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = l_Lean_Expr_cleanupAnnotations(v_snd_112_);
v___x_122_ = l_Lean_Expr_isApp(v___x_121_);
if (v___x_122_ == 0)
{
lean_dec_ref(v___x_121_);
lean_del_object(v___x_109_);
goto v___jp_118_;
}
else
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = l_Lean_Expr_appFnCleanup___redArg(v___x_121_);
v___x_124_ = l_Lean_Expr_isApp(v___x_123_);
if (v___x_124_ == 0)
{
lean_dec_ref(v___x_123_);
lean_dec_ref(v___x_121_);
lean_del_object(v___x_109_);
goto v___jp_118_;
}
else
{
lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_125_ = l_Lean_Expr_appFnCleanup___redArg(v___x_123_);
lean_dec_ref(v___x_123_);
v___x_126_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__4));
v___x_127_ = l_Lean_Expr_isConstOf(v___x_125_, v___x_126_);
lean_dec_ref(v___x_125_);
if (v___x_127_ == 0)
{
lean_dec_ref(v___x_121_);
lean_del_object(v___x_109_);
goto v___jp_118_;
}
else
{
lean_object* v_arg_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v_arg_128_ = lean_ctor_get(v___x_121_, 1);
lean_inc_ref(v_arg_128_);
lean_dec_ref(v___x_121_);
v___x_129_ = l_Lean_Expr_cleanupAnnotations(v_arg_128_);
lean_dec_ref(v_arg_128_);
v___x_130_ = l_Lean_Expr_isApp(v___x_129_);
if (v___x_130_ == 0)
{
lean_dec_ref(v___x_129_);
goto v___jp_113_;
}
else
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = l_Lean_Expr_appFnCleanup___redArg(v___x_129_);
v___x_132_ = l_Lean_Expr_isApp(v___x_131_);
if (v___x_132_ == 0)
{
lean_dec_ref(v___x_131_);
lean_dec_ref(v___x_129_);
goto v___jp_113_;
}
else
{
lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_133_ = l_Lean_Expr_appFnCleanup___redArg(v___x_131_);
lean_dec_ref(v___x_131_);
v___x_134_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__6));
v___x_135_ = l_Lean_Expr_isConstOf(v___x_133_, v___x_134_);
lean_dec_ref(v___x_133_);
if (v___x_135_ == 0)
{
lean_dec_ref(v___x_129_);
goto v___jp_113_;
}
else
{
lean_object* v_arg_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec(v_snd_112_);
lean_del_object(v___x_109_);
v_arg_136_ = lean_ctor_get(v___x_129_, 1);
lean_inc_ref(v_arg_136_);
lean_dec_ref(v___x_129_);
v___x_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_137_, 0, v_arg_136_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
lean_dec(v_snd_112_);
lean_del_object(v___x_109_);
v_val_139_ = lean_ctor_get(v_fst_111_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v_fst_111_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v_fst_111_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_val_139_);
lean_dec(v_fst_111_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
lean_ctor_set_tag(v___x_141_, 0);
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_val_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
v___jp_113_:
{
lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v_snd_112_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_114_);
v___x_116_ = v___x_109_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
v___jp_118_:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_119_, 0, v_snd_112_);
v___x_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
return v___x_120_;
}
}
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
v_a_148_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_106_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_106_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___boxed(lean_object* v_instCL_156_, lean_object* v_ss_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f(v_instCL_156_, v_ss_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec_ref(v_ss_157_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0___redArg(lean_object* v_fvarId_166_, lean_object* v___y_167_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = l_Lean_Expr_fvar___override(v_fvarId_166_);
v___x_170_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_169_, v___y_167_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0___redArg___boxed(lean_object* v_fvarId_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0___redArg(v_fvarId_171_, v___y_172_);
lean_dec(v___y_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0(lean_object* v_fvarId_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0___redArg(v_fvarId_175_, v___y_182_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0___boxed(lean_object* v_fvarId_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0(v_fvarId_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___redArg(lean_object* v_declName_203_, lean_object* v_us_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = l_Lean_Expr_const___override(v_declName_203_, v_us_204_);
v___x_208_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_207_, v___y_205_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___redArg___boxed(lean_object* v_declName_209_, lean_object* v_us_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___redArg(v_declName_209_, v_us_210_, v___y_211_);
lean_dec(v___y_211_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2(lean_object* v_declName_214_, lean_object* v_us_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___redArg(v_declName_214_, v_us_215_, v___y_222_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___boxed(lean_object* v_declName_229_, lean_object* v_us_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2(v_declName_229_, v_us_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4___redArg(lean_object* v_u_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = l_Lean_Expr_sort___override(v_u_244_);
v___x_248_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_247_, v___y_245_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4___redArg___boxed(lean_object* v_u_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4___redArg(v_u_249_, v___y_250_);
lean_dec(v___y_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4(lean_object* v_u_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4___redArg(v_u_253_, v___y_260_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4___boxed(lean_object* v_u_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4(v_u_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5___redArg(lean_object* v_x_281_, uint8_t v_bi_282_, lean_object* v_t_283_, lean_object* v_b_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v___y_293_; lean_object* v___x_296_; uint8_t v_debug_297_; 
v___x_296_ = lean_st_ref_get(v___y_286_);
v_debug_297_ = lean_ctor_get_uint8(v___x_296_, sizeof(void*)*13);
lean_dec(v___x_296_);
if (v_debug_297_ == 0)
{
v___y_293_ = v___y_286_;
goto v___jp_292_;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_283_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v___x_299_; 
lean_dec_ref_known(v___x_298_, 1);
v___x_299_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_dec_ref_known(v___x_299_, 1);
v___y_293_ = v___y_286_;
goto v___jp_292_;
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec_ref(v_b_284_);
lean_dec_ref(v_t_283_);
lean_dec(v_x_281_);
v_a_300_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_299_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec_ref(v_b_284_);
lean_dec_ref(v_t_283_);
lean_dec(v_x_281_);
v_a_308_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_298_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_298_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
v___jp_292_:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = l_Lean_Expr_forallE___override(v_x_281_, v_t_283_, v_b_284_, v_bi_282_);
v___x_295_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_294_, v___y_293_);
return v___x_295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5___redArg___boxed(lean_object* v_x_316_, lean_object* v_bi_317_, lean_object* v_t_318_, lean_object* v_b_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
uint8_t v_bi_boxed_327_; lean_object* v_res_328_; 
v_bi_boxed_327_ = lean_unbox(v_bi_317_);
v_res_328_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5___redArg(v_x_316_, v_bi_boxed_327_, v_t_318_, v_b_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5(lean_object* v_x_329_, uint8_t v_bi_330_, lean_object* v_t_331_, lean_object* v_b_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5___redArg(v_x_329_, v_bi_330_, v_t_331_, v_b_332_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5___boxed(lean_object* v_x_346_, lean_object* v_bi_347_, lean_object* v_t_348_, lean_object* v_b_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
uint8_t v_bi_boxed_362_; lean_object* v_res_363_; 
v_bi_boxed_362_ = lean_unbox(v_bi_347_);
v_res_363_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5(v_x_346_, v_bi_boxed_362_, v_t_348_, v_b_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__7___redArg___lam__0(lean_object* v_k_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v_b_372_, lean_object* v_c_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v___x_379_; 
lean_inc(v___y_377_);
lean_inc_ref(v___y_376_);
lean_inc(v___y_375_);
lean_inc_ref(v___y_374_);
lean_inc(v___y_371_);
lean_inc_ref(v___y_370_);
lean_inc(v___y_369_);
lean_inc_ref(v___y_368_);
lean_inc(v___y_367_);
lean_inc(v___y_366_);
lean_inc_ref(v___y_365_);
v___x_379_ = lean_apply_14(v_k_364_, v_b_372_, v_c_373_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, lean_box(0));
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__7___redArg___lam__0___boxed(lean_object* v_k_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v_b_388_, lean_object* v_c_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__7___redArg___lam__0(v_k_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v_b_388_, v_c_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__7___redArg(lean_object* v_type_396_, lean_object* v_maxFVars_x3f_397_, lean_object* v_k_398_, uint8_t v_cleanupAnnotations_399_, uint8_t v_whnfType_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v___f_413_; lean_object* v___x_414_; 
lean_inc(v___y_407_);
lean_inc_ref(v___y_406_);
lean_inc(v___y_405_);
lean_inc_ref(v___y_404_);
lean_inc(v___y_403_);
lean_inc(v___y_402_);
lean_inc_ref(v___y_401_);
v___f_413_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__7___redArg___lam__0___boxed), 15, 8);
lean_closure_set(v___f_413_, 0, v_k_398_);
lean_closure_set(v___f_413_, 1, v___y_401_);
lean_closure_set(v___f_413_, 2, v___y_402_);
lean_closure_set(v___f_413_, 3, v___y_403_);
lean_closure_set(v___f_413_, 4, v___y_404_);
lean_closure_set(v___f_413_, 5, v___y_405_);
lean_closure_set(v___f_413_, 6, v___y_406_);
lean_closure_set(v___f_413_, 7, v___y_407_);
v___x_414_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_396_, v_maxFVars_x3f_397_, v___f_413_, v_cleanupAnnotations_399_, v_whnfType_400_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
if (lean_obj_tag(v___x_414_) == 0)
{
return v___x_414_;
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__7___redArg___boxed(lean_object** _args){
lean_object* v_type_423_ = _args[0];
lean_object* v_maxFVars_x3f_424_ = _args[1];
lean_object* v_k_425_ = _args[2];
lean_object* v_cleanupAnnotations_426_ = _args[3];
lean_object* v_whnfType_427_ = _args[4];
lean_object* v___y_428_ = _args[5];
lean_object* v___y_429_ = _args[6];
lean_object* v___y_430_ = _args[7];
lean_object* v___y_431_ = _args[8];
lean_object* v___y_432_ = _args[9];
lean_object* v___y_433_ = _args[10];
lean_object* v___y_434_ = _args[11];
lean_object* v___y_435_ = _args[12];
lean_object* v___y_436_ = _args[13];
lean_object* v___y_437_ = _args[14];
lean_object* v___y_438_ = _args[15];
lean_object* v___y_439_ = _args[16];
_start:
{
uint8_t v_cleanupAnnotations_boxed_440_; uint8_t v_whnfType_boxed_441_; lean_object* v_res_442_; 
v_cleanupAnnotations_boxed_440_ = lean_unbox(v_cleanupAnnotations_426_);
v_whnfType_boxed_441_ = lean_unbox(v_whnfType_427_);
v_res_442_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__7___redArg(v_type_423_, v_maxFVars_x3f_424_, v_k_425_, v_cleanupAnnotations_boxed_440_, v_whnfType_boxed_441_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__7(lean_object* v_00_u03b1_443_, lean_object* v_type_444_, lean_object* v_maxFVars_x3f_445_, lean_object* v_k_446_, uint8_t v_cleanupAnnotations_447_, uint8_t v_whnfType_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__7___redArg(v_type_444_, v_maxFVars_x3f_445_, v_k_446_, v_cleanupAnnotations_447_, v_whnfType_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__7___boxed(lean_object** _args){
lean_object* v_00_u03b1_462_ = _args[0];
lean_object* v_type_463_ = _args[1];
lean_object* v_maxFVars_x3f_464_ = _args[2];
lean_object* v_k_465_ = _args[3];
lean_object* v_cleanupAnnotations_466_ = _args[4];
lean_object* v_whnfType_467_ = _args[5];
lean_object* v___y_468_ = _args[6];
lean_object* v___y_469_ = _args[7];
lean_object* v___y_470_ = _args[8];
lean_object* v___y_471_ = _args[9];
lean_object* v___y_472_ = _args[10];
lean_object* v___y_473_ = _args[11];
lean_object* v___y_474_ = _args[12];
lean_object* v___y_475_ = _args[13];
lean_object* v___y_476_ = _args[14];
lean_object* v___y_477_ = _args[15];
lean_object* v___y_478_ = _args[16];
lean_object* v___y_479_ = _args[17];
_start:
{
uint8_t v_cleanupAnnotations_boxed_480_; uint8_t v_whnfType_boxed_481_; lean_object* v_res_482_; 
v_cleanupAnnotations_boxed_480_ = lean_unbox(v_cleanupAnnotations_466_);
v_whnfType_boxed_481_ = lean_unbox(v_whnfType_467_);
v_res_482_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__7(v_00_u03b1_462_, v_type_463_, v_maxFVars_x3f_464_, v_k_465_, v_cleanupAnnotations_boxed_480_, v_whnfType_boxed_481_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__8___redArg(lean_object* v_x_483_, lean_object* v_t_484_, lean_object* v_v_485_, lean_object* v_b_486_, uint8_t v_nondep_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___y_496_; lean_object* v___x_499_; uint8_t v_debug_500_; 
v___x_499_ = lean_st_ref_get(v___y_489_);
v_debug_500_ = lean_ctor_get_uint8(v___x_499_, sizeof(void*)*13);
lean_dec(v___x_499_);
if (v_debug_500_ == 0)
{
v___y_496_ = v___y_489_;
goto v___jp_495_;
}
else
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_484_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v___x_502_; 
lean_dec_ref_known(v___x_501_, 1);
v___x_502_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_v_485_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v___x_503_; 
lean_dec_ref_known(v___x_502_, 1);
v___x_503_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_486_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_dec_ref_known(v___x_503_, 1);
v___y_496_ = v___y_489_;
goto v___jp_495_;
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
lean_dec_ref(v_b_486_);
lean_dec_ref(v_v_485_);
lean_dec_ref(v_t_484_);
lean_dec(v_x_483_);
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec_ref(v_b_486_);
lean_dec_ref(v_v_485_);
lean_dec_ref(v_t_484_);
lean_dec(v_x_483_);
v_a_512_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_502_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_502_);
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
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec_ref(v_b_486_);
lean_dec_ref(v_v_485_);
lean_dec_ref(v_t_484_);
lean_dec(v_x_483_);
v_a_520_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_501_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_501_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
v___jp_495_:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = l_Lean_Expr_letE___override(v_x_483_, v_t_484_, v_v_485_, v_b_486_, v_nondep_487_);
v___x_498_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_497_, v___y_496_);
return v___x_498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__8___redArg___boxed(lean_object* v_x_528_, lean_object* v_t_529_, lean_object* v_v_530_, lean_object* v_b_531_, lean_object* v_nondep_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
uint8_t v_nondep_boxed_540_; lean_object* v_res_541_; 
v_nondep_boxed_540_ = lean_unbox(v_nondep_532_);
v_res_541_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__8___redArg(v_x_528_, v_t_529_, v_v_530_, v_b_531_, v_nondep_boxed_540_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__8(lean_object* v_x_542_, lean_object* v_t_543_, lean_object* v_v_544_, lean_object* v_b_545_, uint8_t v_nondep_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__8___redArg(v_x_542_, v_t_543_, v_v_544_, v_b_545_, v_nondep_546_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__8___boxed(lean_object** _args){
lean_object* v_x_560_ = _args[0];
lean_object* v_t_561_ = _args[1];
lean_object* v_v_562_ = _args[2];
lean_object* v_b_563_ = _args[3];
lean_object* v_nondep_564_ = _args[4];
lean_object* v___y_565_ = _args[5];
lean_object* v___y_566_ = _args[6];
lean_object* v___y_567_ = _args[7];
lean_object* v___y_568_ = _args[8];
lean_object* v___y_569_ = _args[9];
lean_object* v___y_570_ = _args[10];
lean_object* v___y_571_ = _args[11];
lean_object* v___y_572_ = _args[12];
lean_object* v___y_573_ = _args[13];
lean_object* v___y_574_ = _args[14];
lean_object* v___y_575_ = _args[15];
lean_object* v___y_576_ = _args[16];
_start:
{
uint8_t v_nondep_boxed_577_; lean_object* v_res_578_; 
v_nondep_boxed_577_ = lean_unbox(v_nondep_564_);
v_res_578_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__8(v_x_560_, v_t_561_, v_v_562_, v_b_563_, v_nondep_boxed_577_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10___redArg___lam__0(lean_object* v_x_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v___x_592_; 
lean_inc(v___y_586_);
lean_inc_ref(v___y_585_);
lean_inc(v___y_584_);
lean_inc_ref(v___y_583_);
lean_inc(v___y_582_);
lean_inc(v___y_581_);
lean_inc_ref(v___y_580_);
v___x_592_ = lean_apply_12(v_x_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, lean_box(0));
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10___redArg___lam__0___boxed(lean_object* v_x_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10___redArg___lam__0(v_x_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10___redArg(lean_object* v_mvarId_607_, lean_object* v_x_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v___f_621_; lean_object* v___x_622_; 
lean_inc(v___y_615_);
lean_inc_ref(v___y_614_);
lean_inc(v___y_613_);
lean_inc_ref(v___y_612_);
lean_inc(v___y_611_);
lean_inc(v___y_610_);
lean_inc_ref(v___y_609_);
v___f_621_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_621_, 0, v_x_608_);
lean_closure_set(v___f_621_, 1, v___y_609_);
lean_closure_set(v___f_621_, 2, v___y_610_);
lean_closure_set(v___f_621_, 3, v___y_611_);
lean_closure_set(v___f_621_, 4, v___y_612_);
lean_closure_set(v___f_621_, 5, v___y_613_);
lean_closure_set(v___f_621_, 6, v___y_614_);
lean_closure_set(v___f_621_, 7, v___y_615_);
v___x_622_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_607_, v___f_621_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_622_) == 0)
{
return v___x_622_;
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10___redArg___boxed(lean_object* v_mvarId_631_, lean_object* v_x_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10___redArg(v_mvarId_631_, v_x_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10(lean_object* v_00_u03b1_646_, lean_object* v_mvarId_647_, lean_object* v_x_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10___redArg(v_mvarId_647_, v_x_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10___boxed(lean_object* v_00_u03b1_662_, lean_object* v_mvarId_663_, lean_object* v_x_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10(v_00_u03b1_662_, v_mvarId_663_, v_x_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3_spec__3_spec__9___redArg(lean_object* v_f_678_, lean_object* v_a_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___y_688_; lean_object* v___x_691_; uint8_t v_debug_692_; 
v___x_691_ = lean_st_ref_get(v___y_681_);
v_debug_692_ = lean_ctor_get_uint8(v___x_691_, sizeof(void*)*13);
lean_dec(v___x_691_);
if (v_debug_692_ == 0)
{
v___y_688_ = v___y_681_;
goto v___jp_687_;
}
else
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_678_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v___x_694_; 
lean_dec_ref_known(v___x_693_, 1);
v___x_694_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_dec_ref_known(v___x_694_, 1);
v___y_688_ = v___y_681_;
goto v___jp_687_;
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_dec_ref(v_a_679_);
lean_dec_ref(v_f_678_);
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec_ref(v_a_679_);
lean_dec_ref(v_f_678_);
v_a_703_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_693_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_693_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
v___jp_687_:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = l_Lean_Expr_app___override(v_f_678_, v_a_679_);
v___x_690_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_689_, v___y_688_);
return v___x_690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3_spec__3_spec__9___redArg___boxed(lean_object* v_f_711_, lean_object* v_a_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3_spec__3_spec__9___redArg(v_f_711_, v_a_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3_spec__3(lean_object* v_args_721_, lean_object* v_endIdx_722_, lean_object* v_b_723_, lean_object* v_i_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
uint8_t v___x_737_; 
v___x_737_ = lean_nat_dec_le(v_endIdx_722_, v_i_724_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = l_Lean_instInhabitedExpr;
v___x_739_ = lean_array_get_borrowed(v___x_738_, v_args_721_, v_i_724_);
lean_inc(v___x_739_);
v___x_740_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3_spec__3_spec__9___redArg(v_b_723_, v___x_739_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_740_, 1);
v___x_742_ = lean_unsigned_to_nat(1u);
v___x_743_ = lean_nat_add(v_i_724_, v___x_742_);
lean_dec(v_i_724_);
v_b_723_ = v_a_741_;
v_i_724_ = v___x_743_;
goto _start;
}
else
{
lean_dec(v_i_724_);
return v___x_740_;
}
}
else
{
lean_object* v___x_745_; 
lean_dec(v_i_724_);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v_b_723_);
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3_spec__3___boxed(lean_object* v_args_746_, lean_object* v_endIdx_747_, lean_object* v_b_748_, lean_object* v_i_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3_spec__3(v_args_746_, v_endIdx_747_, v_b_748_, v_i_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v_endIdx_747_);
lean_dec_ref(v_args_746_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3(lean_object* v_f_763_, lean_object* v_args_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = lean_array_get_size(v_args_764_);
v___x_779_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3_spec__3(v_args_764_, v___x_778_, v_f_763_, v___x_777_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___boxed(lean_object* v_f_780_, lean_object* v_args_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3(v_f_780_, v_args_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec_ref(v_args_781_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0(lean_object* v_args_798_, lean_object* v_head_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v___x_802_, lean_object* v_arg_803_, lean_object* v_arg_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v___x_807_, lean_object* v_prog_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = lean_unsigned_to_nat(7u);
v___x_822_ = lean_array_set(v_args_798_, v___x_821_, v_prog_808_);
v___x_823_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3(v_head_799_, v___x_822_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec_ref(v___x_822_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_825_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_823_, 1);
v___x_825_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3(v_a_824_, v_a_800_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
lean_dec_ref_known(v___x_825_, 1);
v___x_827_ = l_Lean_Expr_getAppFn(v_a_801_);
v___x_828_ = l_Lean_Expr_constLevels_x21(v___x_827_);
lean_dec_ref(v___x_827_);
v___x_829_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___redArg(v___x_802_, v___x_828_, v___y_815_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref_known(v___x_829_, 1);
v___x_831_ = lean_unsigned_to_nat(4u);
v___x_832_ = lean_mk_empty_array_with_capacity(v___x_831_);
v___x_833_ = lean_array_push(v___x_832_, v_arg_803_);
v___x_834_ = lean_array_push(v___x_833_, v_arg_804_);
v___x_835_ = lean_array_push(v___x_834_, v_a_805_);
v___x_836_ = lean_array_push(v___x_835_, v_a_826_);
v___x_837_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3(v_a_830_, v___x_836_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec_ref(v___x_836_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_839_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref_known(v___x_837_, 1);
v___x_839_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3(v_a_806_, v___x_807_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_841_; uint8_t v___x_842_; lean_object* v___x_843_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
v___x_841_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0___closed__1));
v___x_842_ = 0;
v___x_843_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5___redArg(v___x_841_, v___x_842_, v_a_840_, v_a_838_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_845_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref_known(v___x_843_, 1);
v___x_845_ = l_Lean_Meta_Sym_mkForallFVarsS(v___x_807_, v_a_844_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
return v___x_845_;
}
else
{
lean_dec_ref(v___x_807_);
return v___x_843_;
}
}
else
{
lean_dec(v_a_838_);
lean_dec_ref(v___x_807_);
return v___x_839_;
}
}
else
{
lean_dec_ref(v___x_807_);
lean_dec_ref(v_a_806_);
return v___x_837_;
}
}
else
{
lean_dec(v_a_826_);
lean_dec_ref(v___x_807_);
lean_dec_ref(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec_ref(v_arg_804_);
lean_dec_ref(v_arg_803_);
return v___x_829_;
}
}
else
{
lean_dec_ref(v___x_807_);
lean_dec_ref(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec_ref(v_arg_804_);
lean_dec_ref(v_arg_803_);
lean_dec(v___x_802_);
return v___x_825_;
}
}
else
{
lean_dec_ref(v___x_807_);
lean_dec_ref(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec_ref(v_arg_804_);
lean_dec_ref(v_arg_803_);
lean_dec(v___x_802_);
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0___boxed(lean_object** _args){
lean_object* v_args_846_ = _args[0];
lean_object* v_head_847_ = _args[1];
lean_object* v_a_848_ = _args[2];
lean_object* v_a_849_ = _args[3];
lean_object* v___x_850_ = _args[4];
lean_object* v_arg_851_ = _args[5];
lean_object* v_arg_852_ = _args[6];
lean_object* v_a_853_ = _args[7];
lean_object* v_a_854_ = _args[8];
lean_object* v___x_855_ = _args[9];
lean_object* v_prog_856_ = _args[10];
lean_object* v___y_857_ = _args[11];
lean_object* v___y_858_ = _args[12];
lean_object* v___y_859_ = _args[13];
lean_object* v___y_860_ = _args[14];
lean_object* v___y_861_ = _args[15];
lean_object* v___y_862_ = _args[16];
lean_object* v___y_863_ = _args[17];
lean_object* v___y_864_ = _args[18];
lean_object* v___y_865_ = _args[19];
lean_object* v___y_866_ = _args[20];
lean_object* v___y_867_ = _args[21];
lean_object* v___y_868_ = _args[22];
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0(v_args_846_, v_head_847_, v_a_848_, v_a_849_, v___x_850_, v_arg_851_, v_arg_852_, v_a_853_, v_a_854_, v___x_855_, v_prog_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec_ref(v_a_849_);
lean_dec_ref(v_a_848_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1___redArg(size_t v_sz_870_, size_t v_i_871_, lean_object* v_bs_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
uint8_t v___x_880_; 
v___x_880_ = lean_usize_dec_lt(v_i_871_, v_sz_870_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; 
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v_bs_872_);
return v___x_881_;
}
else
{
lean_object* v_v_882_; lean_object* v___x_883_; lean_object* v_bs_x27_884_; lean_object* v___x_885_; 
v_v_882_ = lean_array_uget(v_bs_872_, v_i_871_);
v___x_883_ = lean_unsigned_to_nat(0u);
v_bs_x27_884_ = lean_array_uset(v_bs_872_, v_i_871_, v___x_883_);
v___x_885_ = l_Lean_Meta_Sym_shareCommonInc(v_v_882_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; size_t v___x_887_; size_t v___x_888_; lean_object* v___x_889_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v___x_887_ = ((size_t)1ULL);
v___x_888_ = lean_usize_add(v_i_871_, v___x_887_);
v___x_889_ = lean_array_uset(v_bs_x27_884_, v_i_871_, v_a_886_);
v_i_871_ = v___x_888_;
v_bs_872_ = v___x_889_;
goto _start;
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec_ref(v_bs_x27_884_);
v_a_891_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_885_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_885_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1___redArg___boxed(lean_object* v_sz_899_, lean_object* v_i_900_, lean_object* v_bs_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
size_t v_sz_boxed_909_; size_t v_i_boxed_910_; lean_object* v_res_911_; 
v_sz_boxed_909_ = lean_unbox_usize(v_sz_899_);
lean_dec(v_sz_899_);
v_i_boxed_910_ = lean_unbox_usize(v_i_900_);
lean_dec(v_i_900_);
v_res_911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1___redArg(v_sz_boxed_909_, v_i_boxed_910_, v_bs_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6_spec__7(lean_object* v_msgData_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_918_; lean_object* v_env_919_; uint8_t v___x_920_; lean_object* v_env_921_; lean_object* v___x_922_; lean_object* v_toCold_923_; lean_object* v_mctx_924_; lean_object* v_lctx_925_; lean_object* v_options_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_918_ = lean_st_ref_get(v___y_916_);
v_env_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc_ref(v_env_919_);
lean_dec(v___x_918_);
v___x_920_ = 0;
v_env_921_ = l_Lean_Environment_setRecordingDeps(v_env_919_, v___x_920_);
v___x_922_ = lean_st_ref_get(v___y_914_);
v_toCold_923_ = lean_ctor_get(v___y_915_, 0);
v_mctx_924_ = lean_ctor_get(v___x_922_, 0);
lean_inc_ref(v_mctx_924_);
lean_dec(v___x_922_);
v_lctx_925_ = lean_ctor_get(v___y_913_, 2);
v_options_926_ = lean_ctor_get(v_toCold_923_, 2);
lean_inc_ref(v_options_926_);
lean_inc_ref(v_lctx_925_);
v___x_927_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_927_, 0, v_env_921_);
lean_ctor_set(v___x_927_, 1, v_mctx_924_);
lean_ctor_set(v___x_927_, 2, v_lctx_925_);
lean_ctor_set(v___x_927_, 3, v_options_926_);
v___x_928_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v_msgData_912_);
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6_spec__7___boxed(lean_object* v_msgData_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6_spec__7(v_msgData_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg(lean_object* v_msg_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_ref_943_; lean_object* v___x_944_; lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_953_; 
v_ref_943_ = lean_ctor_get(v___y_940_, 2);
v___x_944_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6_spec__7(v_msg_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
v_a_945_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_953_ == 0)
{
v___x_947_ = v___x_944_;
v_isShared_948_ = v_isSharedCheck_953_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_944_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_953_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v___x_951_; 
lean_inc(v_ref_943_);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v_ref_943_);
lean_ctor_set(v___x_949_, 1, v_a_945_);
if (v_isShared_948_ == 0)
{
lean_ctor_set_tag(v___x_947_, 1);
lean_ctor_set(v___x_947_, 0, v___x_949_);
v___x_951_ = v___x_947_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg___boxed(lean_object* v_msg_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg(v_msg_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
return v_res_960_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__2(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__1));
v___x_964_ = l_Lean_stringToMessageData(v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__4(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__3));
v___x_967_ = l_Lean_stringToMessageData(v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1(lean_object* v_xs_968_, lean_object* v_instCL_969_, lean_object* v___x_970_, lean_object* v___x_971_, lean_object* v_lctx_972_, lean_object* v_localInstances_973_, lean_object* v_args_974_, lean_object* v_head_975_, lean_object* v_a_976_, lean_object* v___x_977_, lean_object* v_arg_978_, lean_object* v_arg_979_, lean_object* v_a_980_, lean_object* v_val_981_, lean_object* v_ss_982_, lean_object* v_B_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
size_t v_sz_996_; size_t v___x_997_; lean_object* v___x_998_; 
v_sz_996_ = lean_array_size(v_xs_968_);
v___x_997_ = ((size_t)0ULL);
v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1___redArg(v_sz_996_, v___x_997_, v_xs_968_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; size_t v_sz_1000_; lean_object* v___x_1001_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 1);
v_sz_1000_ = lean_array_size(v_ss_982_);
v___x_1001_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1___redArg(v_sz_1000_, v___x_997_, v_ss_982_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = l_Lean_Meta_Sym_shareCommonInc(v_B_983_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f(v_instCL_969_, v_a_1002_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1164_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1164_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1164_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
if (lean_obj_tag(v_a_1006_) == 1)
{
lean_object* v_val_1010_; lean_object* v___x_1011_; 
lean_del_object(v___x_1008_);
v_val_1010_ = lean_ctor_get(v_a_1006_, 0);
lean_inc(v_val_1010_);
lean_dec_ref_known(v_a_1006_, 1);
lean_inc(v_a_1004_);
v___x_1011_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_1004_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1013_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1011_, 1);
v___x_1013_ = l_Lean_Level_dec(v_a_1012_);
lean_dec(v_a_1012_);
if (lean_obj_tag(v___x_1013_) == 1)
{
lean_object* v_val_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1145_; 
v_val_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1145_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_val_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1145_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1018_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__0));
v___x_1019_ = l_Lean_Name_mkStr3(v___x_970_, v___x_971_, v___x_1018_);
v___x_1020_ = lean_box(0);
v___x_1021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1021_, 0, v_val_1014_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___redArg(v___x_1019_, v___x_1021_, v___y_990_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1022_, 1);
v___x_1024_ = lean_unsigned_to_nat(2u);
v___x_1025_ = lean_mk_empty_array_with_capacity(v___x_1024_);
v___x_1026_ = lean_array_push(v___x_1025_, v_a_1004_);
v___x_1027_ = lean_array_push(v___x_1026_, v_val_1010_);
v___x_1028_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3(v_a_1023_, v___x_1027_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec_ref(v___x_1027_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v___x_1028_, 1);
v___x_1030_ = lean_box(0);
v___x_1031_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4___redArg(v___x_1030_, v___y_990_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
lean_inc(v_a_999_);
v___x_1033_ = l_Array_append___redArg(v_a_999_, v_a_1002_);
lean_inc_ref(v___x_1033_);
v___x_1034_ = l_Lean_Meta_Sym_mkForallFVarsS(v___x_1033_, v_a_1032_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; uint8_t v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v___x_1034_, 1);
v___x_1036_ = 2;
v___x_1037_ = lean_box(0);
v___x_1038_ = lean_unsigned_to_nat(0u);
v___x_1039_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_972_, v_localInstances_973_, v_a_1035_, v___x_1036_, v___x_1037_, v___x_1038_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1041_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v___x_1039_, 1);
v___x_1041_ = l_Lean_Meta_Sym_shareCommonInc(v_a_1040_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1043_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref_known(v___x_1041_, 1);
v___x_1043_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3(v_a_980_, v_a_999_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1045_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1043_, 1);
lean_inc_ref(v___x_1033_);
lean_inc(v_a_1042_);
lean_inc(v_a_1029_);
lean_inc_ref(v_arg_979_);
lean_inc_ref(v_arg_978_);
lean_inc(v___x_977_);
lean_inc_ref(v_head_975_);
lean_inc_ref(v_args_974_);
v___x_1045_ = l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0(v_args_974_, v_head_975_, v_a_1002_, v_a_976_, v___x_977_, v_arg_978_, v_arg_979_, v_a_1029_, v_a_1042_, v___x_1033_, v_a_1044_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1047_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v___x_1047_ = l_Lean_Meta_Sym_betaS(v_val_981_, v_a_999_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1049_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
lean_dec_ref_known(v___x_1047_, 1);
lean_inc(v_a_1042_);
lean_inc(v_a_1029_);
v___x_1049_ = l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0(v_args_974_, v_head_975_, v_a_1002_, v_a_976_, v___x_977_, v_arg_978_, v_arg_979_, v_a_1029_, v_a_1042_, v___x_1033_, v_a_1048_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v_a_1002_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1064_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1052_ = v___x_1049_;
v_isShared_1053_ = v_isSharedCheck_1064_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1049_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1064_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1054_ = l_Lean_Expr_mvarId_x21(v_a_1042_);
lean_dec(v_a_1042_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_a_1046_);
lean_ctor_set(v___x_1055_, 1, v_a_1050_);
v___x_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1056_, 0, v_a_1029_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1054_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1057_);
v___x_1059_ = v___x_1016_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1061_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v___x_1059_);
v___x_1061_ = v___x_1052_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec(v_a_1046_);
lean_dec(v_a_1042_);
lean_dec(v_a_1029_);
lean_del_object(v___x_1016_);
v_a_1065_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1049_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1049_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec(v_a_1046_);
lean_dec(v_a_1042_);
lean_dec_ref(v___x_1033_);
lean_dec(v_a_1029_);
lean_del_object(v___x_1016_);
lean_dec(v_a_1002_);
lean_dec_ref(v_arg_979_);
lean_dec_ref(v_arg_978_);
lean_dec(v___x_977_);
lean_dec_ref(v_head_975_);
lean_dec_ref(v_args_974_);
v_a_1073_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1047_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1047_);
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
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec(v_a_1042_);
lean_dec_ref(v___x_1033_);
lean_dec(v_a_1029_);
lean_del_object(v___x_1016_);
lean_dec(v_a_1002_);
lean_dec(v_a_999_);
lean_dec_ref(v_val_981_);
lean_dec_ref(v_arg_979_);
lean_dec_ref(v_arg_978_);
lean_dec(v___x_977_);
lean_dec_ref(v_head_975_);
lean_dec_ref(v_args_974_);
v_a_1081_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1045_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1045_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec(v_a_1042_);
lean_dec_ref(v___x_1033_);
lean_dec(v_a_1029_);
lean_del_object(v___x_1016_);
lean_dec(v_a_1002_);
lean_dec(v_a_999_);
lean_dec_ref(v_val_981_);
lean_dec_ref(v_arg_979_);
lean_dec_ref(v_arg_978_);
lean_dec(v___x_977_);
lean_dec_ref(v_head_975_);
lean_dec_ref(v_args_974_);
v_a_1089_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1043_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1043_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec_ref(v___x_1033_);
lean_dec(v_a_1029_);
lean_del_object(v___x_1016_);
lean_dec(v_a_1002_);
lean_dec(v_a_999_);
lean_dec_ref(v_val_981_);
lean_dec_ref(v_a_980_);
lean_dec_ref(v_arg_979_);
lean_dec_ref(v_arg_978_);
lean_dec(v___x_977_);
lean_dec_ref(v_head_975_);
lean_dec_ref(v_args_974_);
v_a_1097_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1041_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1041_);
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
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec_ref(v___x_1033_);
lean_dec(v_a_1029_);
lean_del_object(v___x_1016_);
lean_dec(v_a_1002_);
lean_dec(v_a_999_);
lean_dec_ref(v_val_981_);
lean_dec_ref(v_a_980_);
lean_dec_ref(v_arg_979_);
lean_dec_ref(v_arg_978_);
lean_dec(v___x_977_);
lean_dec_ref(v_head_975_);
lean_dec_ref(v_args_974_);
v_a_1105_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1039_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1039_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec_ref(v___x_1033_);
lean_dec(v_a_1029_);
lean_del_object(v___x_1016_);
lean_dec(v_a_1002_);
lean_dec(v_a_999_);
lean_dec_ref(v_val_981_);
lean_dec_ref(v_a_980_);
lean_dec_ref(v_arg_979_);
lean_dec_ref(v_arg_978_);
lean_dec(v___x_977_);
lean_dec_ref(v_head_975_);
lean_dec_ref(v_args_974_);
lean_dec_ref(v_localInstances_973_);
lean_dec_ref(v_lctx_972_);
v_a_1113_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1034_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1034_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec(v_a_1029_);
lean_del_object(v___x_1016_);
lean_dec(v_a_1002_);
lean_dec(v_a_999_);
lean_dec_ref(v_val_981_);
lean_dec_ref(v_a_980_);
lean_dec_ref(v_arg_979_);
lean_dec_ref(v_arg_978_);
lean_dec(v___x_977_);
lean_dec_ref(v_head_975_);
lean_dec_ref(v_args_974_);
lean_dec_ref(v_localInstances_973_);
lean_dec_ref(v_lctx_972_);
v_a_1121_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1031_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1031_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_del_object(v___x_1016_);
lean_dec(v_a_1002_);
lean_dec(v_a_999_);
lean_dec_ref(v_val_981_);
lean_dec_ref(v_a_980_);
lean_dec_ref(v_arg_979_);
lean_dec_ref(v_arg_978_);
lean_dec(v___x_977_);
lean_dec_ref(v_head_975_);
lean_dec_ref(v_args_974_);
lean_dec_ref(v_localInstances_973_);
lean_dec_ref(v_lctx_972_);
v_a_1129_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1028_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1028_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_del_object(v___x_1016_);
lean_dec(v_val_1010_);
lean_dec(v_a_1004_);
lean_dec(v_a_1002_);
lean_dec(v_a_999_);
lean_dec_ref(v_val_981_);
lean_dec_ref(v_a_980_);
lean_dec_ref(v_arg_979_);
lean_dec_ref(v_arg_978_);
lean_dec(v___x_977_);
lean_dec_ref(v_head_975_);
lean_dec_ref(v_args_974_);
lean_dec_ref(v_localInstances_973_);
lean_dec_ref(v_lctx_972_);
v_a_1137_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1022_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1022_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
else
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_dec(v___x_1013_);
lean_dec(v_val_1010_);
lean_dec(v_a_1002_);
lean_dec(v_a_999_);
lean_dec_ref(v_val_981_);
lean_dec_ref(v_a_980_);
lean_dec_ref(v_arg_979_);
lean_dec_ref(v_arg_978_);
lean_dec(v___x_977_);
lean_dec_ref(v_head_975_);
lean_dec_ref(v_args_974_);
lean_dec_ref(v_localInstances_973_);
lean_dec_ref(v_lctx_972_);
lean_dec_ref(v___x_971_);
lean_dec_ref(v___x_970_);
v___x_1146_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__2, &l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__2);
v___x_1147_ = l_Lean_MessageData_ofExpr(v_a_1004_);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1146_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__4, &l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__4);
v___x_1150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1148_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg(v___x_1150_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
return v___x_1151_;
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec(v_val_1010_);
lean_dec(v_a_1004_);
lean_dec(v_a_1002_);
lean_dec(v_a_999_);
lean_dec_ref(v_val_981_);
lean_dec_ref(v_a_980_);
lean_dec_ref(v_arg_979_);
lean_dec_ref(v_arg_978_);
lean_dec(v___x_977_);
lean_dec_ref(v_head_975_);
lean_dec_ref(v_args_974_);
lean_dec_ref(v_localInstances_973_);
lean_dec_ref(v_lctx_972_);
lean_dec_ref(v___x_971_);
lean_dec_ref(v___x_970_);
v_a_1152_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1011_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1011_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1162_; 
lean_dec(v_a_1006_);
lean_dec(v_a_1004_);
lean_dec(v_a_1002_);
lean_dec(v_a_999_);
lean_dec_ref(v_val_981_);
lean_dec_ref(v_a_980_);
lean_dec_ref(v_arg_979_);
lean_dec_ref(v_arg_978_);
lean_dec(v___x_977_);
lean_dec_ref(v_head_975_);
lean_dec_ref(v_args_974_);
lean_dec_ref(v_localInstances_973_);
lean_dec_ref(v_lctx_972_);
lean_dec_ref(v___x_971_);
lean_dec_ref(v___x_970_);
v___x_1160_ = lean_box(0);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1160_);
v___x_1162_ = v___x_1008_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec(v_a_1004_);
lean_dec(v_a_1002_);
lean_dec(v_a_999_);
lean_dec_ref(v_val_981_);
lean_dec_ref(v_a_980_);
lean_dec_ref(v_arg_979_);
lean_dec_ref(v_arg_978_);
lean_dec(v___x_977_);
lean_dec_ref(v_head_975_);
lean_dec_ref(v_args_974_);
lean_dec_ref(v_localInstances_973_);
lean_dec_ref(v_lctx_972_);
lean_dec_ref(v___x_971_);
lean_dec_ref(v___x_970_);
v_a_1165_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1005_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1005_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec(v_a_1002_);
lean_dec(v_a_999_);
lean_dec_ref(v_val_981_);
lean_dec_ref(v_a_980_);
lean_dec_ref(v_arg_979_);
lean_dec_ref(v_arg_978_);
lean_dec(v___x_977_);
lean_dec_ref(v_head_975_);
lean_dec_ref(v_args_974_);
lean_dec_ref(v_localInstances_973_);
lean_dec_ref(v_lctx_972_);
lean_dec_ref(v___x_971_);
lean_dec_ref(v___x_970_);
lean_dec_ref(v_instCL_969_);
v_a_1173_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1003_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1003_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec(v_a_999_);
lean_dec_ref(v_B_983_);
lean_dec_ref(v_val_981_);
lean_dec_ref(v_a_980_);
lean_dec_ref(v_arg_979_);
lean_dec_ref(v_arg_978_);
lean_dec(v___x_977_);
lean_dec_ref(v_head_975_);
lean_dec_ref(v_args_974_);
lean_dec_ref(v_localInstances_973_);
lean_dec_ref(v_lctx_972_);
lean_dec_ref(v___x_971_);
lean_dec_ref(v___x_970_);
lean_dec_ref(v_instCL_969_);
v_a_1181_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1001_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1001_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec_ref(v_B_983_);
lean_dec_ref(v_ss_982_);
lean_dec_ref(v_val_981_);
lean_dec_ref(v_a_980_);
lean_dec_ref(v_arg_979_);
lean_dec_ref(v_arg_978_);
lean_dec(v___x_977_);
lean_dec_ref(v_head_975_);
lean_dec_ref(v_args_974_);
lean_dec_ref(v_localInstances_973_);
lean_dec_ref(v_lctx_972_);
lean_dec_ref(v___x_971_);
lean_dec_ref(v___x_970_);
lean_dec_ref(v_instCL_969_);
v_a_1189_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_998_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_998_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___boxed(lean_object** _args){
lean_object* v_xs_1197_ = _args[0];
lean_object* v_instCL_1198_ = _args[1];
lean_object* v___x_1199_ = _args[2];
lean_object* v___x_1200_ = _args[3];
lean_object* v_lctx_1201_ = _args[4];
lean_object* v_localInstances_1202_ = _args[5];
lean_object* v_args_1203_ = _args[6];
lean_object* v_head_1204_ = _args[7];
lean_object* v_a_1205_ = _args[8];
lean_object* v___x_1206_ = _args[9];
lean_object* v_arg_1207_ = _args[10];
lean_object* v_arg_1208_ = _args[11];
lean_object* v_a_1209_ = _args[12];
lean_object* v_val_1210_ = _args[13];
lean_object* v_ss_1211_ = _args[14];
lean_object* v_B_1212_ = _args[15];
lean_object* v___y_1213_ = _args[16];
lean_object* v___y_1214_ = _args[17];
lean_object* v___y_1215_ = _args[18];
lean_object* v___y_1216_ = _args[19];
lean_object* v___y_1217_ = _args[20];
lean_object* v___y_1218_ = _args[21];
lean_object* v___y_1219_ = _args[22];
lean_object* v___y_1220_ = _args[23];
lean_object* v___y_1221_ = _args[24];
lean_object* v___y_1222_ = _args[25];
lean_object* v___y_1223_ = _args[26];
lean_object* v___y_1224_ = _args[27];
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1(v_xs_1197_, v_instCL_1198_, v___x_1199_, v___x_1200_, v_lctx_1201_, v_localInstances_1202_, v_args_1203_, v_head_1204_, v_a_1205_, v___x_1206_, v_arg_1207_, v_arg_1208_, v_a_1209_, v_val_1210_, v_ss_1211_, v_B_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec_ref(v_a_1205_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__2(lean_object* v_info_1226_, lean_object* v_instCL_1227_, lean_object* v___x_1228_, lean_object* v___x_1229_, lean_object* v_lctx_1230_, lean_object* v_localInstances_1231_, lean_object* v_a_1232_, lean_object* v___x_1233_, lean_object* v_arg_1234_, lean_object* v_arg_1235_, lean_object* v_a_1236_, lean_object* v_val_1237_, lean_object* v_xs_1238_, lean_object* v_x_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_head_1252_; lean_object* v_args_1253_; lean_object* v_excessArgs_1254_; lean_object* v___f_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; lean_object* v___x_1260_; 
v_head_1252_ = lean_ctor_get(v_info_1226_, 1);
v_args_1253_ = lean_ctor_get(v_info_1226_, 2);
v_excessArgs_1254_ = lean_ctor_get(v_info_1226_, 3);
lean_inc_ref(v_excessArgs_1254_);
lean_inc_ref(v_head_1252_);
lean_inc_ref(v_args_1253_);
v___f_1255_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___boxed), 28, 14);
lean_closure_set(v___f_1255_, 0, v_xs_1238_);
lean_closure_set(v___f_1255_, 1, v_instCL_1227_);
lean_closure_set(v___f_1255_, 2, v___x_1228_);
lean_closure_set(v___f_1255_, 3, v___x_1229_);
lean_closure_set(v___f_1255_, 4, v_lctx_1230_);
lean_closure_set(v___f_1255_, 5, v_localInstances_1231_);
lean_closure_set(v___f_1255_, 6, v_args_1253_);
lean_closure_set(v___f_1255_, 7, v_head_1252_);
lean_closure_set(v___f_1255_, 8, v_a_1232_);
lean_closure_set(v___f_1255_, 9, v___x_1233_);
lean_closure_set(v___f_1255_, 10, v_arg_1234_);
lean_closure_set(v___f_1255_, 11, v_arg_1235_);
lean_closure_set(v___f_1255_, 12, v_a_1236_);
lean_closure_set(v___f_1255_, 13, v_val_1237_);
v___x_1256_ = l_Lean_Elab_Tactic_VCGen_WPApp_Pred(v_info_1226_);
lean_dec_ref(v_info_1226_);
v___x_1257_ = lean_array_get_size(v_excessArgs_1254_);
lean_dec_ref(v_excessArgs_1254_);
v___x_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
v___x_1259_ = 0;
v___x_1260_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__7___redArg(v___x_1256_, v___x_1258_, v___f_1255_, v___x_1259_, v___x_1259_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__2___boxed(lean_object** _args){
lean_object* v_info_1261_ = _args[0];
lean_object* v_instCL_1262_ = _args[1];
lean_object* v___x_1263_ = _args[2];
lean_object* v___x_1264_ = _args[3];
lean_object* v_lctx_1265_ = _args[4];
lean_object* v_localInstances_1266_ = _args[5];
lean_object* v_a_1267_ = _args[6];
lean_object* v___x_1268_ = _args[7];
lean_object* v_arg_1269_ = _args[8];
lean_object* v_arg_1270_ = _args[9];
lean_object* v_a_1271_ = _args[10];
lean_object* v_val_1272_ = _args[11];
lean_object* v_xs_1273_ = _args[12];
lean_object* v_x_1274_ = _args[13];
lean_object* v___y_1275_ = _args[14];
lean_object* v___y_1276_ = _args[15];
lean_object* v___y_1277_ = _args[16];
lean_object* v___y_1278_ = _args[17];
lean_object* v___y_1279_ = _args[18];
lean_object* v___y_1280_ = _args[19];
lean_object* v___y_1281_ = _args[20];
lean_object* v___y_1282_ = _args[21];
lean_object* v___y_1283_ = _args[22];
lean_object* v___y_1284_ = _args[23];
lean_object* v___y_1285_ = _args[24];
lean_object* v___y_1286_ = _args[25];
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__2(v_info_1261_, v_instCL_1262_, v___x_1263_, v___x_1264_, v_lctx_1265_, v_localInstances_1266_, v_a_1267_, v___x_1268_, v_arg_1269_, v_arg_1270_, v_a_1271_, v_val_1272_, v_xs_1273_, v_x_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec_ref(v_x_1274_);
return v_res_1287_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__11___redArg(lean_object* v_a_1288_, lean_object* v_x_1289_){
_start:
{
if (lean_obj_tag(v_x_1289_) == 0)
{
uint8_t v___x_1290_; 
v___x_1290_ = 0;
return v___x_1290_;
}
else
{
lean_object* v_key_1291_; lean_object* v_tail_1292_; uint8_t v___x_1293_; 
v_key_1291_ = lean_ctor_get(v_x_1289_, 0);
v_tail_1292_ = lean_ctor_get(v_x_1289_, 2);
v___x_1293_ = l_Lean_instBEqMVarId_beq(v_key_1291_, v_a_1288_);
if (v___x_1293_ == 0)
{
v_x_1289_ = v_tail_1292_;
goto _start;
}
else
{
return v___x_1293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__11___redArg___boxed(lean_object* v_a_1295_, lean_object* v_x_1296_){
_start:
{
uint8_t v_res_1297_; lean_object* v_r_1298_; 
v_res_1297_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__11___redArg(v_a_1295_, v_x_1296_);
lean_dec(v_x_1296_);
lean_dec(v_a_1295_);
v_r_1298_ = lean_box(v_res_1297_);
return v_r_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__12_spec__15_spec__16___redArg(lean_object* v_x_1299_, lean_object* v_x_1300_){
_start:
{
if (lean_obj_tag(v_x_1300_) == 0)
{
return v_x_1299_;
}
else
{
lean_object* v_key_1301_; lean_object* v_value_1302_; lean_object* v_tail_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1326_; 
v_key_1301_ = lean_ctor_get(v_x_1300_, 0);
v_value_1302_ = lean_ctor_get(v_x_1300_, 1);
v_tail_1303_ = lean_ctor_get(v_x_1300_, 2);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_x_1300_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1305_ = v_x_1300_;
v_isShared_1306_ = v_isSharedCheck_1326_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_tail_1303_);
lean_inc(v_value_1302_);
lean_inc(v_key_1301_);
lean_dec(v_x_1300_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1326_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; uint64_t v___x_1308_; uint64_t v___x_1309_; uint64_t v___x_1310_; uint64_t v_fold_1311_; uint64_t v___x_1312_; uint64_t v___x_1313_; uint64_t v___x_1314_; size_t v___x_1315_; size_t v___x_1316_; size_t v___x_1317_; size_t v___x_1318_; size_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1307_ = lean_array_get_size(v_x_1299_);
v___x_1308_ = l_Lean_instHashableMVarId_hash(v_key_1301_);
v___x_1309_ = 32ULL;
v___x_1310_ = lean_uint64_shift_right(v___x_1308_, v___x_1309_);
v_fold_1311_ = lean_uint64_xor(v___x_1308_, v___x_1310_);
v___x_1312_ = 16ULL;
v___x_1313_ = lean_uint64_shift_right(v_fold_1311_, v___x_1312_);
v___x_1314_ = lean_uint64_xor(v_fold_1311_, v___x_1313_);
v___x_1315_ = lean_uint64_to_usize(v___x_1314_);
v___x_1316_ = lean_usize_of_nat(v___x_1307_);
v___x_1317_ = ((size_t)1ULL);
v___x_1318_ = lean_usize_sub(v___x_1316_, v___x_1317_);
v___x_1319_ = lean_usize_land(v___x_1315_, v___x_1318_);
v___x_1320_ = lean_array_uget_borrowed(v_x_1299_, v___x_1319_);
lean_inc(v___x_1320_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 2, v___x_1320_);
v___x_1322_ = v___x_1305_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_key_1301_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v_value_1302_);
lean_ctor_set(v_reuseFailAlloc_1325_, 2, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_array_uset(v_x_1299_, v___x_1319_, v___x_1322_);
v_x_1299_ = v___x_1323_;
v_x_1300_ = v_tail_1303_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__12_spec__15___redArg(lean_object* v_i_1327_, lean_object* v_source_1328_, lean_object* v_target_1329_){
_start:
{
lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = lean_array_get_size(v_source_1328_);
v___x_1331_ = lean_nat_dec_lt(v_i_1327_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_dec_ref(v_source_1328_);
lean_dec(v_i_1327_);
return v_target_1329_;
}
else
{
lean_object* v_es_1332_; lean_object* v___x_1333_; lean_object* v_source_1334_; lean_object* v_target_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v_es_1332_ = lean_array_fget(v_source_1328_, v_i_1327_);
v___x_1333_ = lean_box(0);
v_source_1334_ = lean_array_fset(v_source_1328_, v_i_1327_, v___x_1333_);
v_target_1335_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__12_spec__15_spec__16___redArg(v_target_1329_, v_es_1332_);
v___x_1336_ = lean_unsigned_to_nat(1u);
v___x_1337_ = lean_nat_add(v_i_1327_, v___x_1336_);
lean_dec(v_i_1327_);
v_i_1327_ = v___x_1337_;
v_source_1328_ = v_source_1334_;
v_target_1329_ = v_target_1335_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__12___redArg(lean_object* v_data_1339_){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v_nbuckets_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1340_ = lean_array_get_size(v_data_1339_);
v___x_1341_ = lean_unsigned_to_nat(2u);
v_nbuckets_1342_ = lean_nat_mul(v___x_1340_, v___x_1341_);
v___x_1343_ = lean_unsigned_to_nat(0u);
v___x_1344_ = lean_box(0);
v___x_1345_ = lean_mk_array(v_nbuckets_1342_, v___x_1344_);
v___x_1346_ = lean_array_propagate_mark(v_data_1339_, v___x_1345_);
v___x_1347_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__12_spec__15___redArg(v___x_1343_, v_data_1339_, v___x_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__13___redArg(lean_object* v_a_1348_, lean_object* v_b_1349_, lean_object* v_x_1350_){
_start:
{
if (lean_obj_tag(v_x_1350_) == 0)
{
lean_dec(v_b_1349_);
lean_dec(v_a_1348_);
return v_x_1350_;
}
else
{
lean_object* v_key_1351_; lean_object* v_value_1352_; lean_object* v_tail_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1365_; 
v_key_1351_ = lean_ctor_get(v_x_1350_, 0);
v_value_1352_ = lean_ctor_get(v_x_1350_, 1);
v_tail_1353_ = lean_ctor_get(v_x_1350_, 2);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_x_1350_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1355_ = v_x_1350_;
v_isShared_1356_ = v_isSharedCheck_1365_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_tail_1353_);
lean_inc(v_value_1352_);
lean_inc(v_key_1351_);
lean_dec(v_x_1350_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1365_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
uint8_t v___x_1357_; 
v___x_1357_ = l_Lean_instBEqMVarId_beq(v_key_1351_, v_a_1348_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1358_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__13___redArg(v_a_1348_, v_b_1349_, v_tail_1353_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 2, v___x_1358_);
v___x_1360_ = v___x_1355_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_key_1351_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_value_1352_);
lean_ctor_set(v_reuseFailAlloc_1361_, 2, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
else
{
lean_object* v___x_1363_; 
lean_dec(v_value_1352_);
lean_dec(v_key_1351_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 1, v_b_1349_);
lean_ctor_set(v___x_1355_, 0, v_a_1348_);
v___x_1363_ = v___x_1355_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1348_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_b_1349_);
lean_ctor_set(v_reuseFailAlloc_1364_, 2, v_tail_1353_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9___redArg(lean_object* v_m_1366_, lean_object* v_a_1367_, lean_object* v_b_1368_){
_start:
{
lean_object* v_size_1369_; lean_object* v_buckets_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1413_; 
v_size_1369_ = lean_ctor_get(v_m_1366_, 0);
v_buckets_1370_ = lean_ctor_get(v_m_1366_, 1);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_m_1366_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1372_ = v_m_1366_;
v_isShared_1373_ = v_isSharedCheck_1413_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_buckets_1370_);
lean_inc(v_size_1369_);
lean_dec(v_m_1366_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1413_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; uint64_t v___x_1375_; uint64_t v___x_1376_; uint64_t v___x_1377_; uint64_t v_fold_1378_; uint64_t v___x_1379_; uint64_t v___x_1380_; uint64_t v___x_1381_; size_t v___x_1382_; size_t v___x_1383_; size_t v___x_1384_; size_t v___x_1385_; size_t v___x_1386_; lean_object* v_bkt_1387_; uint8_t v___x_1388_; 
v___x_1374_ = lean_array_get_size(v_buckets_1370_);
v___x_1375_ = l_Lean_instHashableMVarId_hash(v_a_1367_);
v___x_1376_ = 32ULL;
v___x_1377_ = lean_uint64_shift_right(v___x_1375_, v___x_1376_);
v_fold_1378_ = lean_uint64_xor(v___x_1375_, v___x_1377_);
v___x_1379_ = 16ULL;
v___x_1380_ = lean_uint64_shift_right(v_fold_1378_, v___x_1379_);
v___x_1381_ = lean_uint64_xor(v_fold_1378_, v___x_1380_);
v___x_1382_ = lean_uint64_to_usize(v___x_1381_);
v___x_1383_ = lean_usize_of_nat(v___x_1374_);
v___x_1384_ = ((size_t)1ULL);
v___x_1385_ = lean_usize_sub(v___x_1383_, v___x_1384_);
v___x_1386_ = lean_usize_land(v___x_1382_, v___x_1385_);
v_bkt_1387_ = lean_array_uget_borrowed(v_buckets_1370_, v___x_1386_);
v___x_1388_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__11___redArg(v_a_1367_, v_bkt_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v_size_x27_1390_; lean_object* v___x_1391_; lean_object* v_buckets_x27_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1389_ = lean_unsigned_to_nat(1u);
v_size_x27_1390_ = lean_nat_add(v_size_1369_, v___x_1389_);
lean_dec(v_size_1369_);
lean_inc(v_bkt_1387_);
v___x_1391_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1391_, 0, v_a_1367_);
lean_ctor_set(v___x_1391_, 1, v_b_1368_);
lean_ctor_set(v___x_1391_, 2, v_bkt_1387_);
v_buckets_x27_1392_ = lean_array_uset(v_buckets_1370_, v___x_1386_, v___x_1391_);
v___x_1393_ = lean_unsigned_to_nat(4u);
v___x_1394_ = lean_nat_mul(v_size_x27_1390_, v___x_1393_);
v___x_1395_ = lean_unsigned_to_nat(3u);
v___x_1396_ = lean_nat_div(v___x_1394_, v___x_1395_);
lean_dec(v___x_1394_);
v___x_1397_ = lean_array_get_size(v_buckets_x27_1392_);
v___x_1398_ = lean_nat_dec_le(v___x_1396_, v___x_1397_);
lean_dec(v___x_1396_);
if (v___x_1398_ == 0)
{
lean_object* v_val_1399_; lean_object* v___x_1401_; 
v_val_1399_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__12___redArg(v_buckets_x27_1392_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 1, v_val_1399_);
lean_ctor_set(v___x_1372_, 0, v_size_x27_1390_);
v___x_1401_ = v___x_1372_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_size_x27_1390_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_val_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
else
{
lean_object* v___x_1404_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 1, v_buckets_x27_1392_);
lean_ctor_set(v___x_1372_, 0, v_size_x27_1390_);
v___x_1404_ = v___x_1372_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_size_x27_1390_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_buckets_x27_1392_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
else
{
lean_object* v___x_1406_; lean_object* v_buckets_x27_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1411_; 
lean_inc(v_bkt_1387_);
v___x_1406_ = lean_box(0);
v_buckets_x27_1407_ = lean_array_uset(v_buckets_1370_, v___x_1386_, v___x_1406_);
v___x_1408_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__13___redArg(v_a_1367_, v_b_1368_, v_bkt_1387_);
v___x_1409_ = lean_array_uset(v_buckets_x27_1407_, v___x_1386_, v___x_1408_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 1, v___x_1409_);
v___x_1411_ = v___x_1372_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_size_1369_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__7(void){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__6));
v___x_1428_ = l_Lean_stringToMessageData(v___x_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3(lean_object* v_jp_1429_, lean_object* v_val_1430_, lean_object* v_goal_1431_, lean_object* v_info_1432_, lean_object* v___x_1433_, lean_object* v_scope_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v___x_1450_; 
lean_inc(v_jp_1429_);
v___x_1450_ = l_Lean_FVarId_getUserName___redArg(v_jp_1429_, v___y_1442_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1797_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1797_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1797_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
uint8_t v_useJP_1460_; 
v_useJP_1460_ = lean_ctor_get_uint8(v___y_1435_, sizeof(void*)*6);
if (v_useJP_1460_ == 0)
{
lean_dec(v_a_1451_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec_ref(v_val_1430_);
lean_dec(v_jp_1429_);
goto v___jp_1455_;
}
else
{
uint8_t v___x_1461_; 
v___x_1461_ = l_Lean_Elab_Tactic_Do_isJP(v_a_1451_);
lean_dec(v_a_1451_);
if (v___x_1461_ == 0)
{
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec_ref(v_val_1430_);
lean_dec(v_jp_1429_);
goto v___jp_1455_;
}
else
{
uint8_t v___x_1462_; 
v___x_1462_ = l_Lean_Expr_isLambda(v_val_1430_);
if (v___x_1462_ == 0)
{
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec_ref(v_val_1430_);
lean_dec(v_jp_1429_);
goto v___jp_1455_;
}
else
{
lean_object* v___x_1463_; 
lean_del_object(v___x_1453_);
lean_inc(v_goal_1431_);
v___x_1463_ = l_Lean_MVarId_getType(v_goal_1431_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 1);
v___x_1465_ = l_Lean_Expr_cleanupAnnotations(v_a_1464_);
v___x_1466_ = l_Lean_Expr_isApp(v___x_1465_);
if (v___x_1466_ == 0)
{
lean_dec_ref(v___x_1465_);
lean_dec(v_a_1464_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec_ref(v_val_1430_);
lean_dec(v_jp_1429_);
goto v___jp_1447_;
}
else
{
lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1467_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1465_);
lean_dec_ref(v___x_1465_);
v___x_1468_ = l_Lean_Expr_isApp(v___x_1467_);
if (v___x_1468_ == 0)
{
lean_dec_ref(v___x_1467_);
lean_dec(v_a_1464_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec_ref(v_val_1430_);
lean_dec(v_jp_1429_);
goto v___jp_1447_;
}
else
{
lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1469_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1467_);
lean_dec_ref(v___x_1467_);
v___x_1470_ = l_Lean_Expr_isApp(v___x_1469_);
if (v___x_1470_ == 0)
{
lean_dec_ref(v___x_1469_);
lean_dec(v_a_1464_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec_ref(v_val_1430_);
lean_dec(v_jp_1429_);
goto v___jp_1447_;
}
else
{
lean_object* v___x_1471_; uint8_t v___x_1472_; 
v___x_1471_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1469_);
v___x_1472_ = l_Lean_Expr_isApp(v___x_1471_);
if (v___x_1472_ == 0)
{
lean_dec_ref(v___x_1471_);
lean_dec_ref(v___x_1469_);
lean_dec(v_a_1464_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec_ref(v_val_1430_);
lean_dec(v_jp_1429_);
goto v___jp_1447_;
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
v___x_1473_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1471_);
v___x_1474_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__1));
v___x_1475_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__2));
v___x_1476_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__2));
v___x_1477_ = l_Lean_Expr_isConstOf(v___x_1473_, v___x_1476_);
lean_dec_ref(v___x_1473_);
if (v___x_1477_ == 0)
{
lean_dec_ref(v___x_1471_);
lean_dec_ref(v___x_1469_);
lean_dec(v_a_1464_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec_ref(v_val_1430_);
lean_dec(v_jp_1429_);
goto v___jp_1447_;
}
else
{
lean_object* v_arg_1478_; lean_object* v_arg_1479_; lean_object* v___x_1480_; 
v_arg_1478_ = lean_ctor_get(v___x_1469_, 1);
lean_inc_ref(v_arg_1478_);
lean_dec_ref(v___x_1469_);
v_arg_1479_ = lean_ctor_get(v___x_1471_, 1);
lean_inc_ref(v_arg_1479_);
lean_dec_ref(v___x_1471_);
lean_inc(v_jp_1429_);
v___x_1480_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0___redArg(v_jp_1429_, v___y_1441_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1482_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc_n(v_a_1481_, 2);
lean_dec_ref_known(v___x_1480_, 1);
v___x_1482_ = l_Lean_Meta_Sym_inferType(v_a_1481_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc_n(v_a_1483_, 2);
lean_dec_ref_known(v___x_1482_, 1);
v___x_1484_ = l_Lean_Elab_Tactic_VCGen_WPApp_Prog(v_info_1432_);
v___x_1485_ = l_Lean_Elab_Tactic_Do_getNumJoinParams(v_a_1483_, v___x_1484_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec_ref(v___x_1484_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v_instCL_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___x_1696_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___x_1747_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1486_);
lean_dec_ref_known(v___x_1485_, 1);
v___x_1696_ = l_Lean_Elab_Tactic_VCGen_WPApp_instAL(v_info_1432_);
lean_inc_ref(v___x_1696_);
v___x_1747_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_1696_, v___y_1443_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref_known(v___x_1747_, 1);
v___x_1749_ = l_Lean_Expr_cleanupAnnotations(v_a_1748_);
lean_dec(v_a_1748_);
v___x_1750_ = l_Lean_Expr_isApp(v___x_1749_);
if (v___x_1750_ == 0)
{
lean_dec_ref(v___x_1749_);
v___y_1698_ = v___y_1435_;
v___y_1699_ = v___y_1436_;
v___y_1700_ = v___y_1437_;
v___y_1701_ = v___y_1438_;
v___y_1702_ = v___y_1439_;
v___y_1703_ = v___y_1440_;
v___y_1704_ = v___y_1441_;
v___y_1705_ = v___y_1442_;
v___y_1706_ = v___y_1443_;
v___y_1707_ = v___y_1444_;
v___y_1708_ = v___y_1445_;
goto v___jp_1697_;
}
else
{
lean_object* v___x_1751_; uint8_t v___x_1752_; 
v___x_1751_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1749_);
v___x_1752_ = l_Lean_Expr_isApp(v___x_1751_);
if (v___x_1752_ == 0)
{
lean_dec_ref(v___x_1751_);
lean_dec_ref(v___x_1749_);
v___y_1698_ = v___y_1435_;
v___y_1699_ = v___y_1436_;
v___y_1700_ = v___y_1437_;
v___y_1701_ = v___y_1438_;
v___y_1702_ = v___y_1439_;
v___y_1703_ = v___y_1440_;
v___y_1704_ = v___y_1441_;
v___y_1705_ = v___y_1442_;
v___y_1706_ = v___y_1443_;
v___y_1707_ = v___y_1444_;
v___y_1708_ = v___y_1445_;
goto v___jp_1697_;
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1753_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1751_);
lean_dec_ref(v___x_1751_);
v___x_1754_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__6));
v___x_1755_ = l_Lean_Expr_isConstOf(v___x_1753_, v___x_1754_);
lean_dec_ref(v___x_1753_);
if (v___x_1755_ == 0)
{
lean_dec_ref(v___x_1749_);
v___y_1698_ = v___y_1435_;
v___y_1699_ = v___y_1436_;
v___y_1700_ = v___y_1437_;
v___y_1701_ = v___y_1438_;
v___y_1702_ = v___y_1439_;
v___y_1703_ = v___y_1440_;
v___y_1704_ = v___y_1441_;
v___y_1705_ = v___y_1442_;
v___y_1706_ = v___y_1443_;
v___y_1707_ = v___y_1444_;
v___y_1708_ = v___y_1445_;
goto v___jp_1697_;
}
else
{
lean_object* v_arg_1756_; 
lean_dec_ref(v___x_1696_);
v_arg_1756_ = lean_ctor_get(v___x_1749_, 1);
lean_inc_ref(v_arg_1756_);
lean_dec_ref(v___x_1749_);
v_instCL_1488_ = v_arg_1756_;
v___y_1489_ = v___y_1435_;
v___y_1490_ = v___y_1436_;
v___y_1491_ = v___y_1437_;
v___y_1492_ = v___y_1438_;
v___y_1493_ = v___y_1439_;
v___y_1494_ = v___y_1440_;
v___y_1495_ = v___y_1441_;
v___y_1496_ = v___y_1442_;
v___y_1497_ = v___y_1443_;
v___y_1498_ = v___y_1444_;
v___y_1499_ = v___y_1445_;
goto v___jp_1487_;
}
}
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec_ref(v___x_1696_);
lean_dec(v_a_1486_);
lean_dec(v_a_1483_);
lean_dec(v_a_1481_);
lean_dec_ref(v_arg_1479_);
lean_dec_ref(v_arg_1478_);
lean_dec(v_a_1464_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec_ref(v_val_1430_);
lean_dec(v_jp_1429_);
v_a_1757_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1747_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1747_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
v___jp_1487_:
{
lean_object* v_lctx_1500_; lean_object* v_localInstances_1501_; lean_object* v___f_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; lean_object* v___x_1505_; 
v_lctx_1500_ = lean_ctor_get(v___y_1496_, 2);
v_localInstances_1501_ = lean_ctor_get(v___y_1496_, 3);
lean_inc(v_a_1464_);
lean_inc_ref(v_localInstances_1501_);
lean_inc_ref(v_lctx_1500_);
lean_inc_ref(v_info_1432_);
v___f_1502_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__2___boxed), 26, 12);
lean_closure_set(v___f_1502_, 0, v_info_1432_);
lean_closure_set(v___f_1502_, 1, v_instCL_1488_);
lean_closure_set(v___f_1502_, 2, v___x_1474_);
lean_closure_set(v___f_1502_, 3, v___x_1475_);
lean_closure_set(v___f_1502_, 4, v_lctx_1500_);
lean_closure_set(v___f_1502_, 5, v_localInstances_1501_);
lean_closure_set(v___f_1502_, 6, v_a_1464_);
lean_closure_set(v___f_1502_, 7, v___x_1476_);
lean_closure_set(v___f_1502_, 8, v_arg_1479_);
lean_closure_set(v___f_1502_, 9, v_arg_1478_);
lean_closure_set(v___f_1502_, 10, v_a_1481_);
lean_closure_set(v___f_1502_, 11, v_val_1430_);
v___x_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1503_, 0, v_a_1486_);
v___x_1504_ = 0;
v___x_1505_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__7___redArg(v_a_1483_, v___x_1503_, v___f_1502_, v___x_1504_, v___x_1504_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1687_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1687_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1687_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
if (lean_obj_tag(v_a_1506_) == 1)
{
lean_object* v_val_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1682_; 
lean_del_object(v___x_1508_);
v_val_1510_ = lean_ctor_get(v_a_1506_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_a_1506_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1512_ = v_a_1506_;
v_isShared_1513_ = v_isSharedCheck_1682_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_val_1510_);
lean_dec(v_a_1506_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1682_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v_snd_1514_; lean_object* v_snd_1515_; lean_object* v_fst_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1680_; 
v_snd_1514_ = lean_ctor_get(v_val_1510_, 1);
lean_inc(v_snd_1514_);
v_snd_1515_ = lean_ctor_get(v_snd_1514_, 1);
lean_inc(v_snd_1515_);
v_fst_1516_ = lean_ctor_get(v_val_1510_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_val_1510_);
if (v_isSharedCheck_1680_ == 0)
{
lean_object* v_unused_1681_; 
v_unused_1681_ = lean_ctor_get(v_val_1510_, 1);
lean_dec(v_unused_1681_);
v___x_1518_ = v_val_1510_;
v_isShared_1519_ = v_isSharedCheck_1680_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_fst_1516_);
lean_dec(v_val_1510_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1680_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v_fst_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1678_; 
v_fst_1520_ = lean_ctor_get(v_snd_1514_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_snd_1514_);
if (v_isSharedCheck_1678_ == 0)
{
lean_object* v_unused_1679_; 
v_unused_1679_ = lean_ctor_get(v_snd_1514_, 1);
lean_dec(v_unused_1679_);
v___x_1522_ = v_snd_1514_;
v_isShared_1523_ = v_isSharedCheck_1678_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_fst_1520_);
lean_dec(v_snd_1514_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1678_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v_fst_1524_; lean_object* v_snd_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1677_; 
v_fst_1524_ = lean_ctor_get(v_snd_1515_, 0);
v_snd_1525_ = lean_ctor_get(v_snd_1515_, 1);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_snd_1515_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1527_ = v_snd_1515_;
v_isShared_1528_ = v_isSharedCheck_1677_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_snd_1525_);
lean_inc(v_fst_1524_);
lean_dec(v_snd_1515_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1677_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; 
lean_inc(v_goal_1431_);
v___x_1529_ = l_Lean_MVarId_getTag(v_goal_1431_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1531_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
v___x_1531_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_snd_1525_, v_a_1530_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v___x_1533_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1531_, 1);
v___x_1533_ = l_Lean_Meta_Sym_shareCommonInc(v_a_1532_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc_n(v_a_1534_, 2);
lean_dec_ref_known(v___x_1533_, 1);
v___x_1535_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__4));
lean_inc(v_fst_1524_);
v___x_1536_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__8___redArg(v___x_1535_, v_fst_1524_, v_a_1534_, v_a_1464_, v___x_1504_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1538_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1536_, 1);
v___x_1538_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_1431_, v_a_1537_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___x_1538_, 1);
v___x_1540_ = lean_unsigned_to_nat(1u);
v___x_1541_ = l_Lean_Meta_Sym_introN(v_a_1539_, v___x_1540_, v___x_1461_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v___x_1541_, 1);
if (lean_obj_tag(v_a_1542_) == 1)
{
lean_object* v_newDecls_1543_; lean_object* v_mvarId_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1622_; 
lean_dec(v_fst_1524_);
v_newDecls_1543_ = lean_ctor_get(v_a_1542_, 0);
v_mvarId_1544_ = lean_ctor_get(v_a_1542_, 1);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_a_1542_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1546_ = v_a_1542_;
v_isShared_1547_ = v_isSharedCheck_1622_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_mvarId_1544_);
lean_inc(v_newDecls_1543_);
lean_dec(v_a_1542_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1622_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = lean_unsigned_to_nat(0u);
v___x_1549_ = lean_array_get(v___x_1433_, v_newDecls_1543_, v___x_1548_);
lean_dec_ref(v_newDecls_1543_);
v___x_1550_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0___redArg(v___x_1549_, v___y_1495_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1613_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1553_ = v___x_1550_;
v_isShared_1554_ = v_isSharedCheck_1613_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1613_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v_excessArgs_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v_specBackwardRuleCache_1560_; lean_object* v_splitBackwardRuleCache_1561_; lean_object* v_latticeBackwardRuleCache_1562_; lean_object* v_frameBackwardRuleCache_1563_; lean_object* v_rintroBackwardRuleCache_1564_; lean_object* v_frameDB_1565_; lean_object* v_invariants_1566_; lean_object* v_vcs_1567_; lean_object* v_simpState_1568_; lean_object* v_fuel_1569_; lean_object* v_inlineHandledInvariants_1570_; lean_object* v_pendingJoinPoints_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1612_; 
v_excessArgs_1555_ = lean_ctor_get(v_info_1432_, 3);
lean_inc_ref(v_excessArgs_1555_);
lean_dec_ref(v_info_1432_);
v___x_1556_ = l_Lean_Expr_mvarId_x21(v_a_1534_);
lean_dec(v_a_1534_);
v___x_1557_ = lean_array_get_size(v_excessArgs_1555_);
lean_dec_ref(v_excessArgs_1555_);
lean_inc(v___x_1556_);
v___x_1558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1558_, 0, v_a_1551_);
lean_ctor_set(v___x_1558_, 1, v_fst_1520_);
lean_ctor_set(v___x_1558_, 2, v_fst_1516_);
lean_ctor_set(v___x_1558_, 3, v___x_1556_);
lean_ctor_set(v___x_1558_, 4, v___x_1557_);
v___x_1559_ = lean_st_ref_take(v___y_1490_);
v_specBackwardRuleCache_1560_ = lean_ctor_get(v___x_1559_, 0);
v_splitBackwardRuleCache_1561_ = lean_ctor_get(v___x_1559_, 1);
v_latticeBackwardRuleCache_1562_ = lean_ctor_get(v___x_1559_, 2);
v_frameBackwardRuleCache_1563_ = lean_ctor_get(v___x_1559_, 3);
v_rintroBackwardRuleCache_1564_ = lean_ctor_get(v___x_1559_, 4);
v_frameDB_1565_ = lean_ctor_get(v___x_1559_, 5);
v_invariants_1566_ = lean_ctor_get(v___x_1559_, 6);
v_vcs_1567_ = lean_ctor_get(v___x_1559_, 7);
v_simpState_1568_ = lean_ctor_get(v___x_1559_, 8);
v_fuel_1569_ = lean_ctor_get(v___x_1559_, 9);
v_inlineHandledInvariants_1570_ = lean_ctor_get(v___x_1559_, 10);
v_pendingJoinPoints_1571_ = lean_ctor_get(v___x_1559_, 11);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1573_ = v___x_1559_;
v_isShared_1574_ = v_isSharedCheck_1612_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_pendingJoinPoints_1571_);
lean_inc(v_inlineHandledInvariants_1570_);
lean_inc(v_fuel_1569_);
lean_inc(v_simpState_1568_);
lean_inc(v_vcs_1567_);
lean_inc(v_invariants_1566_);
lean_inc(v_frameDB_1565_);
lean_inc(v_rintroBackwardRuleCache_1564_);
lean_inc(v_frameBackwardRuleCache_1563_);
lean_inc(v_latticeBackwardRuleCache_1562_);
lean_inc(v_splitBackwardRuleCache_1561_);
lean_inc(v_specBackwardRuleCache_1560_);
lean_dec(v___x_1559_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1612_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1575_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__5));
lean_inc_ref(v___x_1558_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 1, v___x_1575_);
lean_ctor_set(v___x_1527_, 0, v___x_1558_);
v___x_1577_ = v___x_1527_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
lean_object* v___x_1578_; lean_object* v___x_1580_; 
lean_inc(v___x_1556_);
v___x_1578_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9___redArg(v_pendingJoinPoints_1571_, v___x_1556_, v___x_1577_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 11, v___x_1578_);
v___x_1580_ = v___x_1573_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_specBackwardRuleCache_1560_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_splitBackwardRuleCache_1561_);
lean_ctor_set(v_reuseFailAlloc_1610_, 2, v_latticeBackwardRuleCache_1562_);
lean_ctor_set(v_reuseFailAlloc_1610_, 3, v_frameBackwardRuleCache_1563_);
lean_ctor_set(v_reuseFailAlloc_1610_, 4, v_rintroBackwardRuleCache_1564_);
lean_ctor_set(v_reuseFailAlloc_1610_, 5, v_frameDB_1565_);
lean_ctor_set(v_reuseFailAlloc_1610_, 6, v_invariants_1566_);
lean_ctor_set(v_reuseFailAlloc_1610_, 7, v_vcs_1567_);
lean_ctor_set(v_reuseFailAlloc_1610_, 8, v_simpState_1568_);
lean_ctor_set(v_reuseFailAlloc_1610_, 9, v_fuel_1569_);
lean_ctor_set(v_reuseFailAlloc_1610_, 10, v_inlineHandledInvariants_1570_);
lean_ctor_set(v_reuseFailAlloc_1610_, 11, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1581_; lean_object* v_specs_1582_; lean_object* v_lastLiftedPre_x3f_1583_; lean_object* v_nextDeclIdx_1584_; lean_object* v_joinPoints_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1609_; 
v___x_1581_ = lean_st_ref_put(v___y_1490_, v___x_1580_);
v_specs_1582_ = lean_ctor_get(v_scope_1434_, 0);
v_lastLiftedPre_x3f_1583_ = lean_ctor_get(v_scope_1434_, 1);
v_nextDeclIdx_1584_ = lean_ctor_get(v_scope_1434_, 2);
v_joinPoints_1585_ = lean_ctor_get(v_scope_1434_, 3);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_scope_1434_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1587_ = v_scope_1434_;
v_isShared_1588_ = v_isSharedCheck_1609_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_joinPoints_1585_);
lean_inc(v_nextDeclIdx_1584_);
lean_inc(v_lastLiftedPre_x3f_1583_);
lean_inc(v_specs_1582_);
lean_dec(v_scope_1434_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1609_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1589_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_jp_1429_, v___x_1558_, v_joinPoints_1585_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 3, v___x_1589_);
v___x_1591_ = v___x_1587_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_specs_1582_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_lastLiftedPre_x3f_1583_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_nextDeclIdx_1584_);
lean_ctor_set(v_reuseFailAlloc_1608_, 3, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1592_; lean_object* v___x_1594_; 
v___x_1592_ = lean_box(0);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 1, v___x_1592_);
lean_ctor_set(v___x_1546_, 0, v___x_1556_);
v___x_1594_ = v___x_1546_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1596_; 
if (v_isShared_1519_ == 0)
{
lean_ctor_set_tag(v___x_1518_, 1);
lean_ctor_set(v___x_1518_, 1, v___x_1594_);
lean_ctor_set(v___x_1518_, 0, v_mvarId_1544_);
v___x_1596_ = v___x_1518_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_mvarId_1544_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1598_; 
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 1, v___x_1596_);
lean_ctor_set(v___x_1522_, 0, v___x_1591_);
v___x_1598_ = v___x_1522_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1600_; 
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v___x_1598_);
v___x_1600_ = v___x_1512_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1602_; 
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1600_);
v___x_1602_ = v___x_1553_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
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
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_del_object(v___x_1546_);
lean_dec(v_mvarId_1544_);
lean_dec(v_a_1534_);
lean_del_object(v___x_1527_);
lean_del_object(v___x_1522_);
lean_dec(v_fst_1520_);
lean_del_object(v___x_1518_);
lean_dec(v_fst_1516_);
lean_del_object(v___x_1512_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_jp_1429_);
v_a_1614_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1550_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1550_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; 
lean_dec(v_a_1542_);
lean_dec(v_a_1534_);
lean_del_object(v___x_1527_);
lean_del_object(v___x_1522_);
lean_dec(v_fst_1520_);
lean_dec(v_fst_1516_);
lean_del_object(v___x_1512_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_jp_1429_);
v___x_1623_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__7, &l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__7);
v___x_1624_ = l_Lean_indentExpr(v_fst_1524_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set_tag(v___x_1518_, 7);
lean_ctor_set(v___x_1518_, 1, v___x_1624_);
lean_ctor_set(v___x_1518_, 0, v___x_1623_);
v___x_1626_ = v___x_1518_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg(v___x_1626_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
return v___x_1627_;
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec(v_a_1534_);
lean_del_object(v___x_1527_);
lean_dec(v_fst_1524_);
lean_del_object(v___x_1522_);
lean_dec(v_fst_1520_);
lean_del_object(v___x_1518_);
lean_dec(v_fst_1516_);
lean_del_object(v___x_1512_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_jp_1429_);
v_a_1629_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1541_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1541_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec(v_a_1534_);
lean_del_object(v___x_1527_);
lean_dec(v_fst_1524_);
lean_del_object(v___x_1522_);
lean_dec(v_fst_1520_);
lean_del_object(v___x_1518_);
lean_dec(v_fst_1516_);
lean_del_object(v___x_1512_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_jp_1429_);
v_a_1637_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1538_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1538_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_dec(v_a_1534_);
lean_del_object(v___x_1527_);
lean_dec(v_fst_1524_);
lean_del_object(v___x_1522_);
lean_dec(v_fst_1520_);
lean_del_object(v___x_1518_);
lean_dec(v_fst_1516_);
lean_del_object(v___x_1512_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec(v_jp_1429_);
v_a_1645_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1536_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1536_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_del_object(v___x_1527_);
lean_dec(v_fst_1524_);
lean_del_object(v___x_1522_);
lean_dec(v_fst_1520_);
lean_del_object(v___x_1518_);
lean_dec(v_fst_1516_);
lean_del_object(v___x_1512_);
lean_dec(v_a_1464_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec(v_jp_1429_);
v_a_1653_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1533_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1533_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_del_object(v___x_1527_);
lean_dec(v_fst_1524_);
lean_del_object(v___x_1522_);
lean_dec(v_fst_1520_);
lean_del_object(v___x_1518_);
lean_dec(v_fst_1516_);
lean_del_object(v___x_1512_);
lean_dec(v_a_1464_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec(v_jp_1429_);
v_a_1661_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1531_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1531_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_del_object(v___x_1527_);
lean_dec(v_snd_1525_);
lean_dec(v_fst_1524_);
lean_del_object(v___x_1522_);
lean_dec(v_fst_1520_);
lean_del_object(v___x_1518_);
lean_dec(v_fst_1516_);
lean_del_object(v___x_1512_);
lean_dec(v_a_1464_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec(v_jp_1429_);
v_a_1669_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1529_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1529_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
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
lean_object* v___x_1683_; lean_object* v___x_1685_; 
lean_dec(v_a_1506_);
lean_dec(v_a_1464_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec(v_jp_1429_);
v___x_1683_ = lean_box(0);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v___x_1683_);
v___x_1685_ = v___x_1508_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_dec(v_a_1464_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec(v_jp_1429_);
v_a_1688_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1505_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1505_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
v___jp_1697_:
{
lean_object* v___x_1709_; 
lean_inc_ref(v___x_1696_);
v___x_1709_ = l_Lean_Meta_Sym_inferType(v___x_1696_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1709_, 1);
v___x_1711_ = l_Lean_Expr_getAppFn(v_a_1710_);
lean_dec(v_a_1710_);
v___x_1712_ = l_Lean_Expr_constLevels_x21(v___x_1711_);
lean_dec_ref(v___x_1711_);
v___x_1713_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__4));
v___x_1714_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___redArg(v___x_1713_, v___x_1712_, v___y_1704_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
lean_dec_ref_known(v___x_1714_, 1);
v___x_1716_ = l_Lean_Elab_Tactic_VCGen_WPApp_Pred(v_info_1432_);
v___x_1717_ = lean_unsigned_to_nat(2u);
v___x_1718_ = lean_mk_empty_array_with_capacity(v___x_1717_);
v___x_1719_ = lean_array_push(v___x_1718_, v___x_1716_);
v___x_1720_ = lean_array_push(v___x_1719_, v___x_1696_);
v___x_1721_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3(v_a_1715_, v___x_1720_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec_ref(v___x_1720_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1721_, 1);
v_instCL_1488_ = v_a_1722_;
v___y_1489_ = v___y_1698_;
v___y_1490_ = v___y_1699_;
v___y_1491_ = v___y_1700_;
v___y_1492_ = v___y_1701_;
v___y_1493_ = v___y_1702_;
v___y_1494_ = v___y_1703_;
v___y_1495_ = v___y_1704_;
v___y_1496_ = v___y_1705_;
v___y_1497_ = v___y_1706_;
v___y_1498_ = v___y_1707_;
v___y_1499_ = v___y_1708_;
goto v___jp_1487_;
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec(v_a_1486_);
lean_dec(v_a_1483_);
lean_dec(v_a_1481_);
lean_dec_ref(v_arg_1479_);
lean_dec_ref(v_arg_1478_);
lean_dec(v_a_1464_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec_ref(v_val_1430_);
lean_dec(v_jp_1429_);
v_a_1723_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1721_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1721_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_dec_ref(v___x_1696_);
lean_dec(v_a_1486_);
lean_dec(v_a_1483_);
lean_dec(v_a_1481_);
lean_dec_ref(v_arg_1479_);
lean_dec_ref(v_arg_1478_);
lean_dec(v_a_1464_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec_ref(v_val_1430_);
lean_dec(v_jp_1429_);
v_a_1731_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1714_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1714_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec_ref(v___x_1696_);
lean_dec(v_a_1486_);
lean_dec(v_a_1483_);
lean_dec(v_a_1481_);
lean_dec_ref(v_arg_1479_);
lean_dec_ref(v_arg_1478_);
lean_dec(v_a_1464_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec_ref(v_val_1430_);
lean_dec(v_jp_1429_);
v_a_1739_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1709_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1709_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec(v_a_1483_);
lean_dec(v_a_1481_);
lean_dec_ref(v_arg_1479_);
lean_dec_ref(v_arg_1478_);
lean_dec(v_a_1464_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec_ref(v_val_1430_);
lean_dec(v_jp_1429_);
v_a_1765_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1485_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1485_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec(v_a_1481_);
lean_dec_ref(v_arg_1479_);
lean_dec_ref(v_arg_1478_);
lean_dec(v_a_1464_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec_ref(v_val_1430_);
lean_dec(v_jp_1429_);
v_a_1773_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1482_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1482_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec_ref(v_arg_1479_);
lean_dec_ref(v_arg_1478_);
lean_dec(v_a_1464_);
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec_ref(v_val_1430_);
lean_dec(v_jp_1429_);
v_a_1781_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1480_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1480_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
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
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec_ref(v_val_1430_);
lean_dec(v_jp_1429_);
v_a_1789_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1463_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1463_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
}
v___jp_1455_:
{
lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1456_ = lean_box(0);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1456_);
v___x_1458_ = v___x_1453_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec_ref(v_scope_1434_);
lean_dec_ref(v_info_1432_);
lean_dec(v_goal_1431_);
lean_dec_ref(v_val_1430_);
lean_dec(v_jp_1429_);
v_a_1798_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1450_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1450_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
v___jp_1447_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_box(0);
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
return v___x_1449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___boxed(lean_object** _args){
lean_object* v_jp_1806_ = _args[0];
lean_object* v_val_1807_ = _args[1];
lean_object* v_goal_1808_ = _args[2];
lean_object* v_info_1809_ = _args[3];
lean_object* v___x_1810_ = _args[4];
lean_object* v_scope_1811_ = _args[5];
lean_object* v___y_1812_ = _args[6];
lean_object* v___y_1813_ = _args[7];
lean_object* v___y_1814_ = _args[8];
lean_object* v___y_1815_ = _args[9];
lean_object* v___y_1816_ = _args[10];
lean_object* v___y_1817_ = _args[11];
lean_object* v___y_1818_ = _args[12];
lean_object* v___y_1819_ = _args[13];
lean_object* v___y_1820_ = _args[14];
lean_object* v___y_1821_ = _args[15];
lean_object* v___y_1822_ = _args[16];
lean_object* v___y_1823_ = _args[17];
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3(v_jp_1806_, v_val_1807_, v_goal_1808_, v_info_1809_, v___x_1810_, v_scope_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___x_1810_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint(lean_object* v_scope_1825_, lean_object* v_goal_1826_, lean_object* v_jp_1827_, lean_object* v_val_1828_, lean_object* v_info_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_){
_start:
{
lean_object* v___x_1842_; lean_object* v___f_1843_; lean_object* v___x_1844_; 
v___x_1842_ = lean_box(0);
lean_inc(v_goal_1826_);
v___f_1843_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___boxed), 18, 6);
lean_closure_set(v___f_1843_, 0, v_jp_1827_);
lean_closure_set(v___f_1843_, 1, v_val_1828_);
lean_closure_set(v___f_1843_, 2, v_goal_1826_);
lean_closure_set(v___f_1843_, 3, v_info_1829_);
lean_closure_set(v___f_1843_, 4, v___x_1842_);
lean_closure_set(v___f_1843_, 5, v_scope_1825_);
v___x_1844_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10___redArg(v_goal_1826_, v___f_1843_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___boxed(lean_object** _args){
lean_object* v_scope_1845_ = _args[0];
lean_object* v_goal_1846_ = _args[1];
lean_object* v_jp_1847_ = _args[2];
lean_object* v_val_1848_ = _args[3];
lean_object* v_info_1849_ = _args[4];
lean_object* v_a_1850_ = _args[5];
lean_object* v_a_1851_ = _args[6];
lean_object* v_a_1852_ = _args[7];
lean_object* v_a_1853_ = _args[8];
lean_object* v_a_1854_ = _args[9];
lean_object* v_a_1855_ = _args[10];
lean_object* v_a_1856_ = _args[11];
lean_object* v_a_1857_ = _args[12];
lean_object* v_a_1858_ = _args[13];
lean_object* v_a_1859_ = _args[14];
lean_object* v_a_1860_ = _args[15];
lean_object* v_a_1861_ = _args[16];
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_Elab_Tactic_VCGen_registerJoinPoint(v_scope_1845_, v_goal_1846_, v_jp_1847_, v_val_1848_, v_info_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
lean_dec(v_a_1856_);
lean_dec_ref(v_a_1855_);
lean_dec(v_a_1854_);
lean_dec_ref(v_a_1853_);
lean_dec(v_a_1852_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1(size_t v_sz_1863_, size_t v_i_1864_, lean_object* v_bs_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1___redArg(v_sz_1863_, v_i_1864_, v_bs_1865_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1___boxed(lean_object* v_sz_1879_, lean_object* v_i_1880_, lean_object* v_bs_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
size_t v_sz_boxed_1894_; size_t v_i_boxed_1895_; lean_object* v_res_1896_; 
v_sz_boxed_1894_ = lean_unbox_usize(v_sz_1879_);
lean_dec(v_sz_1879_);
v_i_boxed_1895_ = lean_unbox_usize(v_i_1880_);
lean_dec(v_i_1880_);
v_res_1896_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1(v_sz_boxed_1894_, v_i_boxed_1895_, v_bs_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6(lean_object* v_00_u03b1_1897_, lean_object* v_msg_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg(v_msg_1898_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___boxed(lean_object* v_00_u03b1_1912_, lean_object* v_msg_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6(v_00_u03b1_1912_, v_msg_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9(lean_object* v_00_u03b2_1927_, lean_object* v_m_1928_, lean_object* v_a_1929_, lean_object* v_b_1930_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9___redArg(v_m_1928_, v_a_1929_, v_b_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3_spec__3_spec__9(lean_object* v_f_1932_, lean_object* v_a_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3_spec__3_spec__9___redArg(v_f_1932_, v_a_1933_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3_spec__3_spec__9___boxed(lean_object* v_f_1947_, lean_object* v_a_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3_spec__3_spec__9(v_f_1947_, v_a_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
return v_res_1961_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__11(lean_object* v_00_u03b2_1962_, lean_object* v_a_1963_, lean_object* v_x_1964_){
_start:
{
uint8_t v___x_1965_; 
v___x_1965_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__11___redArg(v_a_1963_, v_x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__11___boxed(lean_object* v_00_u03b2_1966_, lean_object* v_a_1967_, lean_object* v_x_1968_){
_start:
{
uint8_t v_res_1969_; lean_object* v_r_1970_; 
v_res_1969_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__11(v_00_u03b2_1966_, v_a_1967_, v_x_1968_);
lean_dec(v_x_1968_);
lean_dec(v_a_1967_);
v_r_1970_ = lean_box(v_res_1969_);
return v_r_1970_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__12(lean_object* v_00_u03b2_1971_, lean_object* v_data_1972_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__12___redArg(v_data_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__13(lean_object* v_00_u03b2_1974_, lean_object* v_a_1975_, lean_object* v_b_1976_, lean_object* v_x_1977_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__13___redArg(v_a_1975_, v_b_1976_, v_x_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__12_spec__15(lean_object* v_00_u03b2_1979_, lean_object* v_i_1980_, lean_object* v_source_1981_, lean_object* v_target_1982_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__12_spec__15___redArg(v_i_1980_, v_source_1981_, v_target_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__12_spec__15_spec__16(lean_object* v_00_u03b2_1984_, lean_object* v_x_1985_, lean_object* v_x_1986_){
_start:
{
lean_object* v___x_1987_; 
v___x_1987_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__12_spec__15_spec__16___redArg(v_x_1985_, v_x_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg(lean_object* v_mvarId_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = l_Lean_Expr_mvar___override(v_mvarId_1988_);
v___x_1992_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1991_, v___y_1989_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg___boxed(lean_object* v_mvarId_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_Meta_Sym_Internal_mkMVarS___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg(v_mvarId_1993_, v___y_1994_);
lean_dec(v___y_1994_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2(lean_object* v_mvarId_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_Meta_Sym_Internal_mkMVarS___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg(v_mvarId_1997_, v___y_2004_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___boxed(lean_object* v_mvarId_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_Lean_Meta_Sym_Internal_mkMVarS___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2(v_mvarId_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__6_spec__8___redArg(lean_object* v_x_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_, lean_object* v_x_2028_){
_start:
{
lean_object* v_ks_2029_; lean_object* v_vs_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2054_; 
v_ks_2029_ = lean_ctor_get(v_x_2025_, 0);
v_vs_2030_ = lean_ctor_get(v_x_2025_, 1);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_x_2025_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2032_ = v_x_2025_;
v_isShared_2033_ = v_isSharedCheck_2054_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_vs_2030_);
lean_inc(v_ks_2029_);
lean_dec(v_x_2025_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2054_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2034_ = lean_array_get_size(v_ks_2029_);
v___x_2035_ = lean_nat_dec_lt(v_x_2026_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2039_; 
lean_dec(v_x_2026_);
v___x_2036_ = lean_array_push(v_ks_2029_, v_x_2027_);
v___x_2037_ = lean_array_push(v_vs_2030_, v_x_2028_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 1, v___x_2037_);
lean_ctor_set(v___x_2032_, 0, v___x_2036_);
v___x_2039_ = v___x_2032_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
else
{
lean_object* v_k_x27_2041_; uint8_t v___x_2042_; 
v_k_x27_2041_ = lean_array_fget_borrowed(v_ks_2029_, v_x_2026_);
v___x_2042_ = l_Lean_instBEqMVarId_beq(v_x_2027_, v_k_x27_2041_);
if (v___x_2042_ == 0)
{
lean_object* v___x_2044_; 
if (v_isShared_2033_ == 0)
{
v___x_2044_ = v___x_2032_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_ks_2029_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_vs_2030_);
v___x_2044_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = lean_unsigned_to_nat(1u);
v___x_2046_ = lean_nat_add(v_x_2026_, v___x_2045_);
lean_dec(v_x_2026_);
v_x_2025_ = v___x_2044_;
v_x_2026_ = v___x_2046_;
goto _start;
}
}
else
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2049_ = lean_array_fset(v_ks_2029_, v_x_2026_, v_x_2027_);
v___x_2050_ = lean_array_fset(v_vs_2030_, v_x_2026_, v_x_2028_);
lean_dec(v_x_2026_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 1, v___x_2050_);
lean_ctor_set(v___x_2032_, 0, v___x_2049_);
v___x_2052_ = v___x_2032_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__6___redArg(lean_object* v_n_2055_, lean_object* v_k_2056_, lean_object* v_v_2057_){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = lean_unsigned_to_nat(0u);
v___x_2059_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__6_spec__8___redArg(v_n_2055_, v___x_2058_, v_k_2056_, v_v_2057_);
return v___x_2059_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4___redArg(lean_object* v_x_2061_, size_t v_x_2062_, size_t v_x_2063_, lean_object* v_x_2064_, lean_object* v_x_2065_){
_start:
{
if (lean_obj_tag(v_x_2061_) == 0)
{
lean_object* v_es_2066_; size_t v___x_2067_; size_t v___x_2068_; lean_object* v_j_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v_es_2066_ = lean_ctor_get(v_x_2061_, 0);
v___x_2067_ = ((size_t)31ULL);
v___x_2068_ = lean_usize_land(v_x_2062_, v___x_2067_);
v_j_2069_ = lean_usize_to_nat(v___x_2068_);
v___x_2070_ = lean_array_get_size(v_es_2066_);
v___x_2071_ = lean_nat_dec_lt(v_j_2069_, v___x_2070_);
if (v___x_2071_ == 0)
{
lean_dec(v_j_2069_);
lean_dec(v_x_2065_);
lean_dec(v_x_2064_);
return v_x_2061_;
}
else
{
lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2110_; 
lean_inc_ref(v_es_2066_);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_x_2061_);
if (v_isSharedCheck_2110_ == 0)
{
lean_object* v_unused_2111_; 
v_unused_2111_ = lean_ctor_get(v_x_2061_, 0);
lean_dec(v_unused_2111_);
v___x_2073_ = v_x_2061_;
v_isShared_2074_ = v_isSharedCheck_2110_;
goto v_resetjp_2072_;
}
else
{
lean_dec(v_x_2061_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2110_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v_v_2075_; lean_object* v___x_2076_; lean_object* v_xs_x27_2077_; lean_object* v___y_2079_; 
v_v_2075_ = lean_array_fget(v_es_2066_, v_j_2069_);
v___x_2076_ = lean_box(0);
v_xs_x27_2077_ = lean_array_fset(v_es_2066_, v_j_2069_, v___x_2076_);
switch(lean_obj_tag(v_v_2075_))
{
case 0:
{
lean_object* v_key_2084_; lean_object* v_val_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2095_; 
v_key_2084_ = lean_ctor_get(v_v_2075_, 0);
v_val_2085_ = lean_ctor_get(v_v_2075_, 1);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_v_2075_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2087_ = v_v_2075_;
v_isShared_2088_ = v_isSharedCheck_2095_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_val_2085_);
lean_inc(v_key_2084_);
lean_dec(v_v_2075_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2095_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
uint8_t v___x_2089_; 
v___x_2089_ = l_Lean_instBEqMVarId_beq(v_x_2064_, v_key_2084_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
lean_del_object(v___x_2087_);
v___x_2090_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2084_, v_val_2085_, v_x_2064_, v_x_2065_);
v___x_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
v___y_2079_ = v___x_2091_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2093_; 
lean_dec(v_val_2085_);
lean_dec(v_key_2084_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 1, v_x_2065_);
lean_ctor_set(v___x_2087_, 0, v_x_2064_);
v___x_2093_ = v___x_2087_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_x_2064_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_x_2065_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
v___y_2079_ = v___x_2093_;
goto v___jp_2078_;
}
}
}
}
case 1:
{
lean_object* v_node_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2108_; 
v_node_2096_ = lean_ctor_get(v_v_2075_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_v_2075_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2098_ = v_v_2075_;
v_isShared_2099_ = v_isSharedCheck_2108_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_node_2096_);
lean_dec(v_v_2075_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2108_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
size_t v___x_2100_; size_t v___x_2101_; size_t v___x_2102_; size_t v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2100_ = ((size_t)5ULL);
v___x_2101_ = lean_usize_shift_right(v_x_2062_, v___x_2100_);
v___x_2102_ = ((size_t)1ULL);
v___x_2103_ = lean_usize_add(v_x_2063_, v___x_2102_);
v___x_2104_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4___redArg(v_node_2096_, v___x_2101_, v___x_2103_, v_x_2064_, v_x_2065_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2104_);
v___x_2106_ = v___x_2098_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
v___y_2079_ = v___x_2106_;
goto v___jp_2078_;
}
}
}
default: 
{
lean_object* v___x_2109_; 
v___x_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2109_, 0, v_x_2064_);
lean_ctor_set(v___x_2109_, 1, v_x_2065_);
v___y_2079_ = v___x_2109_;
goto v___jp_2078_;
}
}
v___jp_2078_:
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2080_ = lean_array_fset(v_xs_x27_2077_, v_j_2069_, v___y_2079_);
lean_dec(v_j_2069_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2080_);
v___x_2082_ = v___x_2073_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
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
else
{
lean_object* v_ks_2112_; lean_object* v_vs_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2131_; 
v_ks_2112_ = lean_ctor_get(v_x_2061_, 0);
v_vs_2113_ = lean_ctor_get(v_x_2061_, 1);
v_isSharedCheck_2131_ = !lean_is_exclusive(v_x_2061_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2115_ = v_x_2061_;
v_isShared_2116_ = v_isSharedCheck_2131_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_vs_2113_);
lean_inc(v_ks_2112_);
lean_dec(v_x_2061_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2131_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_ks_2112_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_vs_2113_);
v___x_2118_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v_newNode_2119_; size_t v___x_2120_; uint8_t v___x_2121_; 
v_newNode_2119_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__6___redArg(v___x_2118_, v_x_2064_, v_x_2065_);
v___x_2120_ = ((size_t)7ULL);
v___x_2121_ = lean_usize_dec_le(v___x_2120_, v_x_2063_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2122_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2119_);
v___x_2123_ = lean_unsigned_to_nat(4u);
v___x_2124_ = lean_nat_dec_lt(v___x_2122_, v___x_2123_);
lean_dec(v___x_2122_);
if (v___x_2124_ == 0)
{
lean_object* v_ks_2125_; lean_object* v_vs_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v_ks_2125_ = lean_ctor_get(v_newNode_2119_, 0);
lean_inc_ref(v_ks_2125_);
v_vs_2126_ = lean_ctor_get(v_newNode_2119_, 1);
lean_inc_ref(v_vs_2126_);
lean_dec_ref(v_newNode_2119_);
v___x_2127_ = lean_unsigned_to_nat(0u);
v___x_2128_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4___redArg___closed__0);
v___x_2129_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__7___redArg(v_x_2063_, v_ks_2125_, v_vs_2126_, v___x_2127_, v___x_2128_);
lean_dec_ref(v_vs_2126_);
lean_dec_ref(v_ks_2125_);
return v___x_2129_;
}
else
{
return v_newNode_2119_;
}
}
else
{
return v_newNode_2119_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__7___redArg(size_t v_depth_2132_, lean_object* v_keys_2133_, lean_object* v_vals_2134_, lean_object* v_i_2135_, lean_object* v_entries_2136_){
_start:
{
lean_object* v___x_2137_; uint8_t v___x_2138_; 
v___x_2137_ = lean_array_get_size(v_keys_2133_);
v___x_2138_ = lean_nat_dec_lt(v_i_2135_, v___x_2137_);
if (v___x_2138_ == 0)
{
lean_dec(v_i_2135_);
return v_entries_2136_;
}
else
{
lean_object* v_k_2139_; lean_object* v_v_2140_; uint64_t v___x_2141_; size_t v_h_2142_; size_t v___x_2143_; lean_object* v___x_2144_; size_t v___x_2145_; size_t v___x_2146_; size_t v___x_2147_; size_t v_h_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v_k_2139_ = lean_array_fget_borrowed(v_keys_2133_, v_i_2135_);
v_v_2140_ = lean_array_fget_borrowed(v_vals_2134_, v_i_2135_);
v___x_2141_ = l_Lean_instHashableMVarId_hash(v_k_2139_);
v_h_2142_ = lean_uint64_to_usize(v___x_2141_);
v___x_2143_ = ((size_t)5ULL);
v___x_2144_ = lean_unsigned_to_nat(1u);
v___x_2145_ = ((size_t)1ULL);
v___x_2146_ = lean_usize_sub(v_depth_2132_, v___x_2145_);
v___x_2147_ = lean_usize_mul(v___x_2143_, v___x_2146_);
v_h_2148_ = lean_usize_shift_right(v_h_2142_, v___x_2147_);
v___x_2149_ = lean_nat_add(v_i_2135_, v___x_2144_);
lean_dec(v_i_2135_);
lean_inc(v_v_2140_);
lean_inc(v_k_2139_);
v___x_2150_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4___redArg(v_entries_2136_, v_h_2148_, v_depth_2132_, v_k_2139_, v_v_2140_);
v_i_2135_ = v___x_2149_;
v_entries_2136_ = v___x_2150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_depth_2152_, lean_object* v_keys_2153_, lean_object* v_vals_2154_, lean_object* v_i_2155_, lean_object* v_entries_2156_){
_start:
{
size_t v_depth_boxed_2157_; lean_object* v_res_2158_; 
v_depth_boxed_2157_ = lean_unbox_usize(v_depth_2152_);
lean_dec(v_depth_2152_);
v_res_2158_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__7___redArg(v_depth_boxed_2157_, v_keys_2153_, v_vals_2154_, v_i_2155_, v_entries_2156_);
lean_dec_ref(v_vals_2154_);
lean_dec_ref(v_keys_2153_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_x_2159_, lean_object* v_x_2160_, lean_object* v_x_2161_, lean_object* v_x_2162_, lean_object* v_x_2163_){
_start:
{
size_t v_x_25577__boxed_2164_; size_t v_x_25578__boxed_2165_; lean_object* v_res_2166_; 
v_x_25577__boxed_2164_ = lean_unbox_usize(v_x_2160_);
lean_dec(v_x_2160_);
v_x_25578__boxed_2165_ = lean_unbox_usize(v_x_2161_);
lean_dec(v_x_2161_);
v_res_2166_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4___redArg(v_x_2159_, v_x_25577__boxed_2164_, v_x_25578__boxed_2165_, v_x_2162_, v_x_2163_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3___redArg(lean_object* v_x_2167_, lean_object* v_x_2168_, lean_object* v_x_2169_){
_start:
{
uint64_t v___x_2170_; size_t v___x_2171_; size_t v___x_2172_; lean_object* v___x_2173_; 
v___x_2170_ = l_Lean_instHashableMVarId_hash(v_x_2168_);
v___x_2171_ = lean_uint64_to_usize(v___x_2170_);
v___x_2172_ = ((size_t)1ULL);
v___x_2173_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4___redArg(v_x_2167_, v___x_2171_, v___x_2172_, v_x_2168_, v_x_2169_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3___redArg(lean_object* v_mvarId_2174_, lean_object* v_val_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; lean_object* v_mctx_2179_; lean_object* v_cache_2180_; lean_object* v_zetaDeltaFVarIds_2181_; lean_object* v_postponed_2182_; lean_object* v_diag_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2212_; 
v___x_2178_ = lean_st_ref_take(v___y_2176_);
v_mctx_2179_ = lean_ctor_get(v___x_2178_, 0);
v_cache_2180_ = lean_ctor_get(v___x_2178_, 1);
v_zetaDeltaFVarIds_2181_ = lean_ctor_get(v___x_2178_, 2);
v_postponed_2182_ = lean_ctor_get(v___x_2178_, 3);
v_diag_2183_ = lean_ctor_get(v___x_2178_, 4);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2185_ = v___x_2178_;
v_isShared_2186_ = v_isSharedCheck_2212_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_diag_2183_);
lean_inc(v_postponed_2182_);
lean_inc(v_zetaDeltaFVarIds_2181_);
lean_inc(v_cache_2180_);
lean_inc(v_mctx_2179_);
lean_dec(v___x_2178_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2212_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v_depth_2187_; lean_object* v_levelAssignDepth_2188_; lean_object* v_lmvarCounter_2189_; lean_object* v_mvarCounter_2190_; lean_object* v_lDecls_2191_; lean_object* v_decls_2192_; lean_object* v_userNames_2193_; lean_object* v_lAssignment_2194_; lean_object* v_eAssignment_2195_; lean_object* v_dAssignment_2196_; lean_object* v_instanceTypedMVars_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2211_; 
v_depth_2187_ = lean_ctor_get(v_mctx_2179_, 0);
v_levelAssignDepth_2188_ = lean_ctor_get(v_mctx_2179_, 1);
v_lmvarCounter_2189_ = lean_ctor_get(v_mctx_2179_, 2);
v_mvarCounter_2190_ = lean_ctor_get(v_mctx_2179_, 3);
v_lDecls_2191_ = lean_ctor_get(v_mctx_2179_, 4);
v_decls_2192_ = lean_ctor_get(v_mctx_2179_, 5);
v_userNames_2193_ = lean_ctor_get(v_mctx_2179_, 6);
v_lAssignment_2194_ = lean_ctor_get(v_mctx_2179_, 7);
v_eAssignment_2195_ = lean_ctor_get(v_mctx_2179_, 8);
v_dAssignment_2196_ = lean_ctor_get(v_mctx_2179_, 9);
v_instanceTypedMVars_2197_ = lean_ctor_get(v_mctx_2179_, 10);
v_isSharedCheck_2211_ = !lean_is_exclusive(v_mctx_2179_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2199_ = v_mctx_2179_;
v_isShared_2200_ = v_isSharedCheck_2211_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_instanceTypedMVars_2197_);
lean_inc(v_dAssignment_2196_);
lean_inc(v_eAssignment_2195_);
lean_inc(v_lAssignment_2194_);
lean_inc(v_userNames_2193_);
lean_inc(v_decls_2192_);
lean_inc(v_lDecls_2191_);
lean_inc(v_mvarCounter_2190_);
lean_inc(v_lmvarCounter_2189_);
lean_inc(v_levelAssignDepth_2188_);
lean_inc(v_depth_2187_);
lean_dec(v_mctx_2179_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2211_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2204_; 
v___x_2201_ = lean_box(0);
v___x_2202_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3___redArg(v_eAssignment_2195_, v_mvarId_2174_, v_val_2175_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 8, v___x_2202_);
v___x_2204_ = v___x_2199_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_depth_2187_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_levelAssignDepth_2188_);
lean_ctor_set(v_reuseFailAlloc_2210_, 2, v_lmvarCounter_2189_);
lean_ctor_set(v_reuseFailAlloc_2210_, 3, v_mvarCounter_2190_);
lean_ctor_set(v_reuseFailAlloc_2210_, 4, v_lDecls_2191_);
lean_ctor_set(v_reuseFailAlloc_2210_, 5, v_decls_2192_);
lean_ctor_set(v_reuseFailAlloc_2210_, 6, v_userNames_2193_);
lean_ctor_set(v_reuseFailAlloc_2210_, 7, v_lAssignment_2194_);
lean_ctor_set(v_reuseFailAlloc_2210_, 8, v___x_2202_);
lean_ctor_set(v_reuseFailAlloc_2210_, 9, v_dAssignment_2196_);
lean_ctor_set(v_reuseFailAlloc_2210_, 10, v_instanceTypedMVars_2197_);
v___x_2204_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
lean_object* v___x_2206_; 
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 0, v___x_2204_);
v___x_2206_ = v___x_2185_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2204_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_cache_2180_);
lean_ctor_set(v_reuseFailAlloc_2209_, 2, v_zetaDeltaFVarIds_2181_);
lean_ctor_set(v_reuseFailAlloc_2209_, 3, v_postponed_2182_);
lean_ctor_set(v_reuseFailAlloc_2209_, 4, v_diag_2183_);
v___x_2206_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = lean_st_ref_put(v___y_2176_, v___x_2206_);
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2201_);
return v___x_2208_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3___redArg___boxed(lean_object* v_mvarId_2213_, lean_object* v_val_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3___redArg(v_mvarId_2213_, v_val_2214_, v___y_2215_);
lean_dec(v___y_2215_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__4_spec__5(lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_x_2221_){
_start:
{
if (lean_obj_tag(v_x_2221_) == 0)
{
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
return v_x_2221_;
}
else
{
lean_object* v_key_2222_; lean_object* v_value_2223_; lean_object* v_tail_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2248_; 
v_key_2222_ = lean_ctor_get(v_x_2221_, 0);
v_value_2223_ = lean_ctor_get(v_x_2221_, 1);
v_tail_2224_ = lean_ctor_get(v_x_2221_, 2);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_x_2221_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2226_ = v_x_2221_;
v_isShared_2227_ = v_isSharedCheck_2248_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_tail_2224_);
lean_inc(v_value_2223_);
lean_inc(v_key_2222_);
lean_dec(v_x_2221_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2248_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
uint8_t v___x_2228_; 
v___x_2228_ = l_Lean_instBEqMVarId_beq(v_key_2222_, v_a_2220_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__4_spec__5(v_a_2218_, v_a_2219_, v_a_2220_, v_tail_2224_);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 2, v___x_2229_);
v___x_2231_ = v___x_2226_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_key_2222_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v_value_2223_);
lean_ctor_set(v_reuseFailAlloc_2232_, 2, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
else
{
lean_object* v_fst_2233_; lean_object* v_snd_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v_key_2222_);
v_fst_2233_ = lean_ctor_get(v_value_2223_, 0);
v_snd_2234_ = lean_ctor_get(v_value_2223_, 1);
v_isSharedCheck_2247_ = !lean_is_exclusive(v_value_2223_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2236_ = v_value_2223_;
v_isShared_2237_ = v_isSharedCheck_2247_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_snd_2234_);
lean_inc(v_fst_2233_);
lean_dec(v_value_2223_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2247_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2238_ = l_Lean_Expr_mvarId_x21(v_a_2218_);
v___x_2239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
lean_ctor_set(v___x_2239_, 1, v_a_2219_);
v___x_2240_ = lean_array_push(v_snd_2234_, v___x_2239_);
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 1, v___x_2240_);
v___x_2242_ = v___x_2236_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_fst_2233_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
lean_object* v___x_2244_; 
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 1, v___x_2242_);
lean_ctor_set(v___x_2226_, 0, v_a_2220_);
v___x_2244_ = v___x_2226_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2220_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v___x_2242_);
lean_ctor_set(v_reuseFailAlloc_2245_, 2, v_tail_2224_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__4_spec__5___boxed(lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_x_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__4_spec__5(v_a_2249_, v_a_2250_, v_a_2251_, v_x_2252_);
lean_dec_ref(v_a_2249_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__4(lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_m_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v_size_2258_; lean_object* v_buckets_2259_; lean_object* v___x_2260_; uint64_t v___x_2261_; uint64_t v___x_2262_; uint64_t v___x_2263_; uint64_t v_fold_2264_; uint64_t v___x_2265_; uint64_t v___x_2266_; uint64_t v___x_2267_; size_t v___x_2268_; size_t v___x_2269_; size_t v___x_2270_; size_t v___x_2271_; size_t v___x_2272_; lean_object* v_bucket_2273_; uint8_t v___x_2274_; 
v_size_2258_ = lean_ctor_get(v_m_2256_, 0);
v_buckets_2259_ = lean_ctor_get(v_m_2256_, 1);
v___x_2260_ = lean_array_get_size(v_buckets_2259_);
v___x_2261_ = l_Lean_instHashableMVarId_hash(v_a_2257_);
v___x_2262_ = 32ULL;
v___x_2263_ = lean_uint64_shift_right(v___x_2261_, v___x_2262_);
v_fold_2264_ = lean_uint64_xor(v___x_2261_, v___x_2263_);
v___x_2265_ = 16ULL;
v___x_2266_ = lean_uint64_shift_right(v_fold_2264_, v___x_2265_);
v___x_2267_ = lean_uint64_xor(v_fold_2264_, v___x_2266_);
v___x_2268_ = lean_uint64_to_usize(v___x_2267_);
v___x_2269_ = lean_usize_of_nat(v___x_2260_);
v___x_2270_ = ((size_t)1ULL);
v___x_2271_ = lean_usize_sub(v___x_2269_, v___x_2270_);
v___x_2272_ = lean_usize_land(v___x_2268_, v___x_2271_);
v_bucket_2273_ = lean_array_uget_borrowed(v_buckets_2259_, v___x_2272_);
v___x_2274_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__9_spec__11___redArg(v_a_2257_, v_bucket_2273_);
if (v___x_2274_ == 0)
{
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2255_);
return v_m_2256_;
}
else
{
lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2285_; 
lean_inc(v_bucket_2273_);
lean_inc_ref(v_buckets_2259_);
lean_inc(v_size_2258_);
v_isSharedCheck_2285_ = !lean_is_exclusive(v_m_2256_);
if (v_isSharedCheck_2285_ == 0)
{
lean_object* v_unused_2286_; lean_object* v_unused_2287_; 
v_unused_2286_ = lean_ctor_get(v_m_2256_, 1);
lean_dec(v_unused_2286_);
v_unused_2287_ = lean_ctor_get(v_m_2256_, 0);
lean_dec(v_unused_2287_);
v___x_2276_ = v_m_2256_;
v_isShared_2277_ = v_isSharedCheck_2285_;
goto v_resetjp_2275_;
}
else
{
lean_dec(v_m_2256_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2285_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; lean_object* v_buckets_2279_; lean_object* v_bucket_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2278_ = lean_box(0);
v_buckets_2279_ = lean_array_uset(v_buckets_2259_, v___x_2272_, v___x_2278_);
v_bucket_2280_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__4_spec__5(v_a_2254_, v_a_2255_, v_a_2257_, v_bucket_2273_);
v___x_2281_ = lean_array_uset(v_buckets_2279_, v___x_2272_, v_bucket_2280_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 1, v___x_2281_);
v___x_2283_ = v___x_2276_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_size_2258_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v___x_2281_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__4___boxed(lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_m_2290_, lean_object* v_a_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__4(v_a_2288_, v_a_2289_, v_m_2290_, v_a_2291_);
lean_dec_ref(v_a_2288_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg(size_t v_sz_2293_, size_t v_i_2294_, lean_object* v_bs_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
uint8_t v___x_2303_; 
v___x_2303_ = lean_usize_dec_lt(v_i_2294_, v_sz_2293_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; 
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v_bs_2295_);
return v___x_2304_;
}
else
{
lean_object* v_v_2305_; lean_object* v___x_2306_; lean_object* v_bs_x27_2307_; lean_object* v___x_2308_; 
v_v_2305_ = lean_array_uget(v_bs_2295_, v_i_2294_);
v___x_2306_ = lean_unsigned_to_nat(0u);
v_bs_x27_2307_ = lean_array_uset(v_bs_2295_, v_i_2294_, v___x_2306_);
v___x_2308_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v_v_2305_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; size_t v___x_2310_; size_t v___x_2311_; lean_object* v___x_2312_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2308_, 1);
v___x_2310_ = ((size_t)1ULL);
v___x_2311_ = lean_usize_add(v_i_2294_, v___x_2310_);
v___x_2312_ = lean_array_uset(v_bs_x27_2307_, v_i_2294_, v_a_2309_);
v_i_2294_ = v___x_2311_;
v_bs_2295_ = v___x_2312_;
goto _start;
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec_ref(v_bs_x27_2307_);
v_a_2314_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2308_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2308_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg___boxed(lean_object* v_sz_2322_, lean_object* v_i_2323_, lean_object* v_bs_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
size_t v_sz_boxed_2332_; size_t v_i_boxed_2333_; lean_object* v_res_2334_; 
v_sz_boxed_2332_ = lean_unbox_usize(v_sz_2322_);
lean_dec(v_sz_2322_);
v_i_boxed_2333_ = lean_unbox_usize(v_i_2323_);
lean_dec(v_i_2323_);
v_res_2334_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg(v_sz_boxed_2332_, v_i_boxed_2333_, v_bs_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
return v_res_2334_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2335_; lean_object* v_dummy_2336_; 
v___x_2335_ = lean_box(0);
v_dummy_2336_ = l_Lean_Expr_sort___override(v___x_2335_);
return v_dummy_2336_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__2));
v___x_2341_ = l_Lean_stringToMessageData(v___x_2340_);
return v___x_2341_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__4));
v___x_2344_ = l_Lean_stringToMessageData(v___x_2343_);
return v___x_2344_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__6));
v___x_2347_ = l_Lean_stringToMessageData(v___x_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0(lean_object* v_info_2348_, lean_object* v___x_2349_, lean_object* v_val_2350_, lean_object* v_goal_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v___x_2475_; 
lean_inc(v_goal_2351_);
v___x_2475_ = l_Lean_MVarId_getType(v_goal_2351_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2522_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2478_ = v___x_2475_;
v_isShared_2479_ = v_isSharedCheck_2522_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2475_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2522_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2480_; uint8_t v___x_2481_; 
v___x_2480_ = l_Lean_Expr_cleanupAnnotations(v_a_2476_);
lean_dec(v_a_2476_);
v___x_2481_ = l_Lean_Expr_isApp(v___x_2480_);
if (v___x_2481_ == 0)
{
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2478_);
lean_dec(v_goal_2351_);
lean_dec_ref(v_val_2350_);
lean_dec_ref(v___x_2349_);
goto v___jp_2364_;
}
else
{
lean_object* v___x_2482_; uint8_t v___x_2483_; 
v___x_2482_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2480_);
lean_dec_ref(v___x_2480_);
v___x_2483_ = l_Lean_Expr_isApp(v___x_2482_);
if (v___x_2483_ == 0)
{
lean_dec_ref(v___x_2482_);
lean_del_object(v___x_2478_);
lean_dec(v_goal_2351_);
lean_dec_ref(v_val_2350_);
lean_dec_ref(v___x_2349_);
goto v___jp_2364_;
}
else
{
lean_object* v___x_2484_; uint8_t v___x_2485_; 
v___x_2484_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2482_);
v___x_2485_ = l_Lean_Expr_isApp(v___x_2484_);
if (v___x_2485_ == 0)
{
lean_dec_ref(v___x_2484_);
lean_dec_ref(v___x_2482_);
lean_del_object(v___x_2478_);
lean_dec(v_goal_2351_);
lean_dec_ref(v_val_2350_);
lean_dec_ref(v___x_2349_);
goto v___jp_2364_;
}
else
{
lean_object* v___x_2486_; uint8_t v___x_2487_; 
v___x_2486_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2484_);
lean_dec_ref(v___x_2484_);
v___x_2487_ = l_Lean_Expr_isApp(v___x_2486_);
if (v___x_2487_ == 0)
{
lean_dec_ref(v___x_2486_);
lean_dec_ref(v___x_2482_);
lean_del_object(v___x_2478_);
lean_dec(v_goal_2351_);
lean_dec_ref(v_val_2350_);
lean_dec_ref(v___x_2349_);
goto v___jp_2364_;
}
else
{
lean_object* v___x_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; 
v___x_2488_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2486_);
lean_dec_ref(v___x_2486_);
v___x_2489_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__2));
v___x_2490_ = l_Lean_Expr_isConstOf(v___x_2488_, v___x_2489_);
lean_dec_ref(v___x_2488_);
if (v___x_2490_ == 0)
{
lean_dec_ref(v___x_2482_);
lean_del_object(v___x_2478_);
lean_dec(v_goal_2351_);
lean_dec_ref(v_val_2350_);
lean_dec_ref(v___x_2349_);
goto v___jp_2364_;
}
else
{
lean_object* v_arg_2491_; lean_object* v_top_2492_; lean_object* v_numStates_2493_; uint8_t v___x_2494_; 
v_arg_2491_ = lean_ctor_get(v___x_2482_, 1);
lean_inc_ref(v_arg_2491_);
lean_dec_ref(v___x_2482_);
v_top_2492_ = lean_ctor_get(v_val_2350_, 1);
v_numStates_2493_ = lean_ctor_get(v_val_2350_, 4);
v___x_2494_ = lean_expr_eqv(v_arg_2491_, v_top_2492_);
lean_dec_ref(v_arg_2491_);
if (v___x_2494_ == 0)
{
lean_object* v___x_2495_; lean_object* v___x_2497_; 
lean_dec(v_goal_2351_);
lean_dec_ref(v_val_2350_);
lean_dec_ref(v___x_2349_);
v___x_2495_ = lean_box(0);
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 0, v___x_2495_);
v___x_2497_ = v___x_2478_;
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
else
{
lean_object* v_excessArgs_2499_; lean_object* v___x_2500_; uint8_t v___x_2501_; 
lean_del_object(v___x_2478_);
v_excessArgs_2499_ = lean_ctor_get(v_info_2348_, 3);
v___x_2500_ = lean_array_get_size(v_excessArgs_2499_);
v___x_2501_ = lean_nat_dec_eq(v___x_2500_, v_numStates_2493_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_inc(v_numStates_2493_);
lean_dec(v_goal_2351_);
lean_dec_ref(v_val_2350_);
v___x_2502_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__3, &l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__3);
v___x_2503_ = l_Lean_indentExpr(v___x_2349_);
v___x_2504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2502_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
v___x_2505_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__5, &l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__5);
v___x_2506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2504_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
v___x_2507_ = l_Nat_reprFast(v_numStates_2493_);
v___x_2508_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
v___x_2509_ = l_Lean_MessageData_ofFormat(v___x_2508_);
v___x_2510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2506_);
lean_ctor_set(v___x_2510_, 1, v___x_2509_);
v___x_2511_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__7, &l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__7);
v___x_2512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2510_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
v___x_2513_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg(v___x_2512_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2513_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2513_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
else
{
goto v___jp_2367_;
}
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
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec(v_goal_2351_);
lean_dec_ref(v_val_2350_);
lean_dec_ref(v___x_2349_);
v_a_2523_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2475_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2475_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
v___jp_2364_:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = lean_box(0);
v___x_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
return v___x_2366_;
}
v___jp_2367_:
{
lean_object* v_excessArgs_2368_; lean_object* v_nargs_2369_; lean_object* v_dummy_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; size_t v_sz_2376_; size_t v___x_2377_; lean_object* v___x_2378_; 
v_excessArgs_2368_ = lean_ctor_get(v_info_2348_, 3);
v_nargs_2369_ = l_Lean_Expr_getAppNumArgs(v___x_2349_);
v_dummy_2370_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__0, &l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__0);
lean_inc(v_nargs_2369_);
v___x_2371_ = lean_mk_array(v_nargs_2369_, v_dummy_2370_);
v___x_2372_ = lean_unsigned_to_nat(1u);
v___x_2373_ = lean_nat_sub(v_nargs_2369_, v___x_2372_);
lean_dec(v_nargs_2369_);
v___x_2374_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_2349_, v___x_2371_, v___x_2373_);
v___x_2375_ = l_Array_append___redArg(v___x_2374_, v_excessArgs_2368_);
v_sz_2376_ = lean_array_size(v___x_2375_);
v___x_2377_ = ((size_t)0ULL);
v___x_2378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg(v_sz_2376_, v___x_2377_, v___x_2375_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v_spec_2380_; lean_object* v_hyp_2381_; lean_object* v_rhsGoal_2382_; lean_object* v___x_2383_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref_known(v___x_2378_, 1);
v_spec_2380_ = lean_ctor_get(v_val_2350_, 0);
lean_inc_ref(v_spec_2380_);
v_hyp_2381_ = lean_ctor_get(v_val_2350_, 2);
lean_inc(v_hyp_2381_);
v_rhsGoal_2382_ = lean_ctor_get(v_val_2350_, 3);
lean_inc(v_rhsGoal_2382_);
lean_dec_ref(v_val_2350_);
v___x_2383_ = l_Lean_Meta_Sym_Internal_mkMVarS___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg(v_hyp_2381_, v___y_2358_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; lean_object* v___x_2385_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref_known(v___x_2383_, 1);
v___x_2385_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3(v_a_2384_, v_a_2379_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_a_2386_);
lean_dec_ref_known(v___x_2385_, 1);
v___x_2387_ = lean_box(0);
v___x_2388_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2386_, v___x_2387_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___x_2390_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2388_, 1);
v___x_2390_ = l_Lean_Meta_Sym_shareCommonInc(v_a_2389_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc_n(v_a_2391_, 2);
lean_dec_ref_known(v___x_2390_, 1);
lean_inc(v_a_2379_);
v___x_2392_ = lean_array_push(v_a_2379_, v_a_2391_);
v___x_2393_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3(v_spec_2380_, v___x_2392_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
lean_dec_ref(v___x_2392_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2425_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2393_, 1);
v___x_2395_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3___redArg(v_goal_2351_, v_a_2394_, v___y_2360_);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2425_ == 0)
{
lean_object* v_unused_2426_; 
v_unused_2426_ = lean_ctor_get(v___x_2395_, 0);
lean_dec(v_unused_2426_);
v___x_2397_ = v___x_2395_;
v_isShared_2398_ = v_isSharedCheck_2425_;
goto v_resetjp_2396_;
}
else
{
lean_dec(v___x_2395_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2425_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; lean_object* v_specBackwardRuleCache_2400_; lean_object* v_splitBackwardRuleCache_2401_; lean_object* v_latticeBackwardRuleCache_2402_; lean_object* v_frameBackwardRuleCache_2403_; lean_object* v_rintroBackwardRuleCache_2404_; lean_object* v_frameDB_2405_; lean_object* v_invariants_2406_; lean_object* v_vcs_2407_; lean_object* v_simpState_2408_; lean_object* v_fuel_2409_; lean_object* v_inlineHandledInvariants_2410_; lean_object* v_pendingJoinPoints_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2424_; 
v___x_2399_ = lean_st_ref_take(v___y_2353_);
v_specBackwardRuleCache_2400_ = lean_ctor_get(v___x_2399_, 0);
v_splitBackwardRuleCache_2401_ = lean_ctor_get(v___x_2399_, 1);
v_latticeBackwardRuleCache_2402_ = lean_ctor_get(v___x_2399_, 2);
v_frameBackwardRuleCache_2403_ = lean_ctor_get(v___x_2399_, 3);
v_rintroBackwardRuleCache_2404_ = lean_ctor_get(v___x_2399_, 4);
v_frameDB_2405_ = lean_ctor_get(v___x_2399_, 5);
v_invariants_2406_ = lean_ctor_get(v___x_2399_, 6);
v_vcs_2407_ = lean_ctor_get(v___x_2399_, 7);
v_simpState_2408_ = lean_ctor_get(v___x_2399_, 8);
v_fuel_2409_ = lean_ctor_get(v___x_2399_, 9);
v_inlineHandledInvariants_2410_ = lean_ctor_get(v___x_2399_, 10);
v_pendingJoinPoints_2411_ = lean_ctor_get(v___x_2399_, 11);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2413_ = v___x_2399_;
v_isShared_2414_ = v_isSharedCheck_2424_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_pendingJoinPoints_2411_);
lean_inc(v_inlineHandledInvariants_2410_);
lean_inc(v_fuel_2409_);
lean_inc(v_simpState_2408_);
lean_inc(v_vcs_2407_);
lean_inc(v_invariants_2406_);
lean_inc(v_frameDB_2405_);
lean_inc(v_rintroBackwardRuleCache_2404_);
lean_inc(v_frameBackwardRuleCache_2403_);
lean_inc(v_latticeBackwardRuleCache_2402_);
lean_inc(v_splitBackwardRuleCache_2401_);
lean_inc(v_specBackwardRuleCache_2400_);
lean_dec(v___x_2399_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2424_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v___x_2417_; 
v___x_2415_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__4(v_a_2391_, v_a_2379_, v_pendingJoinPoints_2411_, v_rhsGoal_2382_);
lean_dec(v_a_2391_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 11, v___x_2415_);
v___x_2417_ = v___x_2413_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_specBackwardRuleCache_2400_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_splitBackwardRuleCache_2401_);
lean_ctor_set(v_reuseFailAlloc_2423_, 2, v_latticeBackwardRuleCache_2402_);
lean_ctor_set(v_reuseFailAlloc_2423_, 3, v_frameBackwardRuleCache_2403_);
lean_ctor_set(v_reuseFailAlloc_2423_, 4, v_rintroBackwardRuleCache_2404_);
lean_ctor_set(v_reuseFailAlloc_2423_, 5, v_frameDB_2405_);
lean_ctor_set(v_reuseFailAlloc_2423_, 6, v_invariants_2406_);
lean_ctor_set(v_reuseFailAlloc_2423_, 7, v_vcs_2407_);
lean_ctor_set(v_reuseFailAlloc_2423_, 8, v_simpState_2408_);
lean_ctor_set(v_reuseFailAlloc_2423_, 9, v_fuel_2409_);
lean_ctor_set(v_reuseFailAlloc_2423_, 10, v_inlineHandledInvariants_2410_);
lean_ctor_set(v_reuseFailAlloc_2423_, 11, v___x_2415_);
v___x_2417_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2421_; 
v___x_2418_ = lean_st_ref_put(v___y_2353_, v___x_2417_);
v___x_2419_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__1));
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2419_);
v___x_2421_ = v___x_2397_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2419_);
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
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_dec(v_a_2391_);
lean_dec(v_rhsGoal_2382_);
lean_dec(v_a_2379_);
lean_dec(v_goal_2351_);
v_a_2427_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2393_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2393_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_dec(v_rhsGoal_2382_);
lean_dec_ref(v_spec_2380_);
lean_dec(v_a_2379_);
lean_dec(v_goal_2351_);
v_a_2435_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2390_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2390_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_dec(v_rhsGoal_2382_);
lean_dec_ref(v_spec_2380_);
lean_dec(v_a_2379_);
lean_dec(v_goal_2351_);
v_a_2443_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2388_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2388_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec(v_rhsGoal_2382_);
lean_dec_ref(v_spec_2380_);
lean_dec(v_a_2379_);
lean_dec(v_goal_2351_);
v_a_2451_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2385_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2385_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec(v_rhsGoal_2382_);
lean_dec_ref(v_spec_2380_);
lean_dec(v_a_2379_);
lean_dec(v_goal_2351_);
v_a_2459_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2383_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2383_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec(v_goal_2351_);
lean_dec_ref(v_val_2350_);
v_a_2467_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2378_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2378_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___boxed(lean_object* v_info_2531_, lean_object* v___x_2532_, lean_object* v_val_2533_, lean_object* v_goal_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0(v_info_2531_, v___x_2532_, v_val_2533_, v_goal_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec_ref(v_info_2531_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg(lean_object* v_t_2548_, lean_object* v_k_2549_){
_start:
{
if (lean_obj_tag(v_t_2548_) == 0)
{
lean_object* v_k_2550_; lean_object* v_v_2551_; lean_object* v_l_2552_; lean_object* v_r_2553_; uint8_t v___x_2554_; 
v_k_2550_ = lean_ctor_get(v_t_2548_, 1);
v_v_2551_ = lean_ctor_get(v_t_2548_, 2);
v_l_2552_ = lean_ctor_get(v_t_2548_, 3);
v_r_2553_ = lean_ctor_get(v_t_2548_, 4);
v___x_2554_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2549_, v_k_2550_);
switch(v___x_2554_)
{
case 0:
{
v_t_2548_ = v_l_2552_;
goto _start;
}
case 1:
{
lean_object* v___x_2556_; 
lean_inc(v_v_2551_);
v___x_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2556_, 0, v_v_2551_);
return v___x_2556_;
}
default: 
{
v_t_2548_ = v_r_2553_;
goto _start;
}
}
}
else
{
lean_object* v___x_2558_; 
v___x_2558_ = lean_box(0);
return v___x_2558_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg___boxed(lean_object* v_t_2559_, lean_object* v_k_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg(v_t_2559_, v_k_2560_);
lean_dec(v_k_2560_);
lean_dec(v_t_2559_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f(lean_object* v_scope_2562_, lean_object* v_goal_2563_, lean_object* v_info_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2577_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_2564_);
v___x_2578_ = l_Lean_Expr_getAppFn(v___x_2577_);
v___x_2579_ = l_Lean_Expr_fvarId_x3f(v___x_2578_);
lean_dec_ref(v___x_2578_);
if (lean_obj_tag(v___x_2579_) == 1)
{
lean_object* v_val_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2593_; 
v_val_2580_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2582_ = v___x_2579_;
v_isShared_2583_ = v_isSharedCheck_2593_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_val_2580_);
lean_dec(v___x_2579_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2593_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v_joinPoints_2584_; lean_object* v___x_2585_; 
v_joinPoints_2584_ = lean_ctor_get(v_scope_2562_, 3);
v___x_2585_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg(v_joinPoints_2584_, v_val_2580_);
lean_dec(v_val_2580_);
if (lean_obj_tag(v___x_2585_) == 1)
{
lean_object* v_val_2586_; lean_object* v___f_2587_; lean_object* v___x_2588_; 
lean_del_object(v___x_2582_);
v_val_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_val_2586_);
lean_dec_ref_known(v___x_2585_, 1);
lean_inc(v_goal_2563_);
v___f_2587_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___boxed), 16, 4);
lean_closure_set(v___f_2587_, 0, v_info_2564_);
lean_closure_set(v___f_2587_, 1, v___x_2577_);
lean_closure_set(v___f_2587_, 2, v_val_2586_);
lean_closure_set(v___f_2587_, 3, v_goal_2563_);
v___x_2588_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10___redArg(v_goal_2563_, v___f_2587_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
return v___x_2588_;
}
else
{
lean_object* v___x_2589_; lean_object* v___x_2591_; 
lean_dec(v___x_2585_);
lean_dec_ref(v___x_2577_);
lean_dec_ref(v_info_2564_);
lean_dec(v_goal_2563_);
v___x_2589_ = lean_box(0);
if (v_isShared_2583_ == 0)
{
lean_ctor_set_tag(v___x_2582_, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2589_);
v___x_2591_ = v___x_2582_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
else
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
lean_dec(v___x_2579_);
lean_dec_ref(v___x_2577_);
lean_dec_ref(v_info_2564_);
lean_dec(v_goal_2563_);
v___x_2594_ = lean_box(0);
v___x_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
return v___x_2595_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___boxed(lean_object* v_scope_2596_, lean_object* v_goal_2597_, lean_object* v_info_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_Elab_Tactic_VCGen_wpJump_x3f(v_scope_2596_, v_goal_2597_, v_info_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_);
lean_dec(v_a_2609_);
lean_dec_ref(v_a_2608_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_a_2601_);
lean_dec(v_a_2600_);
lean_dec_ref(v_a_2599_);
lean_dec_ref(v_scope_2596_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0(lean_object* v_00_u03b4_2612_, lean_object* v_t_2613_, lean_object* v_k_2614_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg(v_t_2613_, v_k_2614_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___boxed(lean_object* v_00_u03b4_2616_, lean_object* v_t_2617_, lean_object* v_k_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0(v_00_u03b4_2616_, v_t_2617_, v_k_2618_);
lean_dec(v_k_2618_);
lean_dec(v_t_2617_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1(size_t v_sz_2620_, size_t v_i_2621_, lean_object* v_bs_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg(v_sz_2620_, v_i_2621_, v_bs_2622_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___boxed(lean_object* v_sz_2636_, lean_object* v_i_2637_, lean_object* v_bs_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
size_t v_sz_boxed_2651_; size_t v_i_boxed_2652_; lean_object* v_res_2653_; 
v_sz_boxed_2651_ = lean_unbox_usize(v_sz_2636_);
lean_dec(v_sz_2636_);
v_i_boxed_2652_ = lean_unbox_usize(v_i_2637_);
lean_dec(v_i_2637_);
v_res_2653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1(v_sz_boxed_2651_, v_i_boxed_2652_, v_bs_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3(lean_object* v_mvarId_2654_, lean_object* v_val_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3___redArg(v_mvarId_2654_, v_val_2655_, v___y_2664_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3___boxed(lean_object* v_mvarId_2669_, lean_object* v_val_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3(v_mvarId_2669_, v_val_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3(lean_object* v_00_u03b2_2684_, lean_object* v_x_2685_, lean_object* v_x_2686_, lean_object* v_x_2687_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3___redArg(v_x_2685_, v_x_2686_, v_x_2687_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_2689_, lean_object* v_x_2690_, size_t v_x_2691_, size_t v_x_2692_, lean_object* v_x_2693_, lean_object* v_x_2694_){
_start:
{
lean_object* v___x_2695_; 
v___x_2695_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4___redArg(v_x_2690_, v_x_2691_, v_x_2692_, v_x_2693_, v_x_2694_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2696_, lean_object* v_x_2697_, lean_object* v_x_2698_, lean_object* v_x_2699_, lean_object* v_x_2700_, lean_object* v_x_2701_){
_start:
{
size_t v_x_26487__boxed_2702_; size_t v_x_26488__boxed_2703_; lean_object* v_res_2704_; 
v_x_26487__boxed_2702_ = lean_unbox_usize(v_x_2698_);
lean_dec(v_x_2698_);
v_x_26488__boxed_2703_ = lean_unbox_usize(v_x_2699_);
lean_dec(v_x_2699_);
v_res_2704_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4(v_00_u03b2_2696_, v_x_2697_, v_x_26487__boxed_2702_, v_x_26488__boxed_2703_, v_x_2700_, v_x_2701_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_2705_, lean_object* v_n_2706_, lean_object* v_k_2707_, lean_object* v_v_2708_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__6___redArg(v_n_2706_, v_k_2707_, v_v_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_2710_, size_t v_depth_2711_, lean_object* v_keys_2712_, lean_object* v_vals_2713_, lean_object* v_heq_2714_, lean_object* v_i_2715_, lean_object* v_entries_2716_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__7___redArg(v_depth_2711_, v_keys_2712_, v_vals_2713_, v_i_2715_, v_entries_2716_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_2718_, lean_object* v_depth_2719_, lean_object* v_keys_2720_, lean_object* v_vals_2721_, lean_object* v_heq_2722_, lean_object* v_i_2723_, lean_object* v_entries_2724_){
_start:
{
size_t v_depth_boxed_2725_; lean_object* v_res_2726_; 
v_depth_boxed_2725_ = lean_unbox_usize(v_depth_2719_);
lean_dec(v_depth_2719_);
v_res_2726_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__7(v_00_u03b2_2718_, v_depth_boxed_2725_, v_keys_2720_, v_vals_2721_, v_heq_2722_, v_i_2723_, v_entries_2724_);
lean_dec_ref(v_vals_2721_);
lean_dec_ref(v_keys_2720_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__6_spec__8(lean_object* v_00_u03b2_2727_, lean_object* v_x_2728_, lean_object* v_x_2729_, lean_object* v_x_2730_, lean_object* v_x_2731_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__3_spec__4_spec__6_spec__8___redArg(v_x_2728_, v_x_2729_, v_x_2730_, v_x_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(lean_object* v_as_2733_, size_t v_i_2734_, size_t v_stop_2735_, lean_object* v_b_2736_){
_start:
{
lean_object* v___y_2738_; uint8_t v___x_2742_; 
v___x_2742_ = lean_usize_dec_eq(v_i_2734_, v_stop_2735_);
if (v___x_2742_ == 0)
{
lean_object* v___x_2743_; 
v___x_2743_ = lean_array_uget_borrowed(v_as_2733_, v_i_2734_);
if (lean_obj_tag(v___x_2743_) == 0)
{
v___y_2738_ = v_b_2736_;
goto v___jp_2737_;
}
else
{
lean_object* v_val_2744_; uint8_t v___x_2745_; 
v_val_2744_ = lean_ctor_get(v___x_2743_, 0);
v___x_2745_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2744_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2746_; 
lean_inc(v_val_2744_);
v___x_2746_ = lean_array_push(v_b_2736_, v_val_2744_);
v___y_2738_ = v___x_2746_;
goto v___jp_2737_;
}
else
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Lean_LocalDecl_value_x3f(v_val_2744_, v___x_2742_);
if (lean_obj_tag(v___x_2747_) == 0)
{
v___y_2738_ = v_b_2736_;
goto v___jp_2737_;
}
else
{
lean_object* v___x_2748_; 
lean_dec_ref_known(v___x_2747_, 1);
lean_inc(v_val_2744_);
v___x_2748_ = lean_array_push(v_b_2736_, v_val_2744_);
v___y_2738_ = v___x_2748_;
goto v___jp_2737_;
}
}
}
}
else
{
return v_b_2736_;
}
v___jp_2737_:
{
size_t v___x_2739_; size_t v___x_2740_; 
v___x_2739_ = ((size_t)1ULL);
v___x_2740_ = lean_usize_add(v_i_2734_, v___x_2739_);
v_i_2734_ = v___x_2740_;
v_b_2736_ = v___y_2738_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2___boxed(lean_object* v_as_2749_, lean_object* v_i_2750_, lean_object* v_stop_2751_, lean_object* v_b_2752_){
_start:
{
size_t v_i_boxed_2753_; size_t v_stop_boxed_2754_; lean_object* v_res_2755_; 
v_i_boxed_2753_ = lean_unbox_usize(v_i_2750_);
lean_dec(v_i_2750_);
v_stop_boxed_2754_ = lean_unbox_usize(v_stop_2751_);
lean_dec(v_stop_2751_);
v_res_2755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_as_2749_, v_i_boxed_2753_, v_stop_boxed_2754_, v_b_2752_);
lean_dec_ref(v_as_2749_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3(lean_object* v_x_2756_, lean_object* v_x_2757_){
_start:
{
if (lean_obj_tag(v_x_2756_) == 0)
{
lean_object* v_cs_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; uint8_t v___x_2761_; 
v_cs_2758_ = lean_ctor_get(v_x_2756_, 0);
v___x_2759_ = lean_unsigned_to_nat(0u);
v___x_2760_ = lean_array_get_size(v_cs_2758_);
v___x_2761_ = lean_nat_dec_lt(v___x_2759_, v___x_2760_);
if (v___x_2761_ == 0)
{
return v_x_2757_;
}
else
{
size_t v___x_2762_; size_t v___x_2763_; lean_object* v___x_2764_; 
v___x_2762_ = ((size_t)0ULL);
v___x_2763_ = lean_usize_of_nat(v___x_2760_);
v___x_2764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2(v_cs_2758_, v___x_2762_, v___x_2763_, v_x_2757_);
return v___x_2764_;
}
}
else
{
lean_object* v_vs_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
v_vs_2765_ = lean_ctor_get(v_x_2756_, 0);
v___x_2766_ = lean_unsigned_to_nat(0u);
v___x_2767_ = lean_array_get_size(v_vs_2765_);
v___x_2768_ = lean_nat_dec_lt(v___x_2766_, v___x_2767_);
if (v___x_2768_ == 0)
{
return v_x_2757_;
}
else
{
size_t v___x_2769_; size_t v___x_2770_; lean_object* v___x_2771_; 
v___x_2769_ = ((size_t)0ULL);
v___x_2770_ = lean_usize_of_nat(v___x_2767_);
v___x_2771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_vs_2765_, v___x_2769_, v___x_2770_, v_x_2757_);
return v___x_2771_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_2772_, size_t v_i_2773_, size_t v_stop_2774_, lean_object* v_b_2775_){
_start:
{
uint8_t v___x_2776_; 
v___x_2776_ = lean_usize_dec_eq(v_i_2773_, v_stop_2774_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2777_; lean_object* v___x_2778_; size_t v___x_2779_; size_t v___x_2780_; 
v___x_2777_ = lean_array_uget_borrowed(v_as_2772_, v_i_2773_);
v___x_2778_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3(v___x_2777_, v_b_2775_);
v___x_2779_ = ((size_t)1ULL);
v___x_2780_ = lean_usize_add(v_i_2773_, v___x_2779_);
v_i_2773_ = v___x_2780_;
v_b_2775_ = v___x_2778_;
goto _start;
}
else
{
return v_b_2775_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_2782_, lean_object* v_i_2783_, lean_object* v_stop_2784_, lean_object* v_b_2785_){
_start:
{
size_t v_i_boxed_2786_; size_t v_stop_boxed_2787_; lean_object* v_res_2788_; 
v_i_boxed_2786_ = lean_unbox_usize(v_i_2783_);
lean_dec(v_i_2783_);
v_stop_boxed_2787_ = lean_unbox_usize(v_stop_2784_);
lean_dec(v_stop_2784_);
v_res_2788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2(v_as_2782_, v_i_boxed_2786_, v_stop_boxed_2787_, v_b_2785_);
lean_dec_ref(v_as_2782_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3___boxed(lean_object* v_x_2789_, lean_object* v_x_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3(v_x_2789_, v_x_2790_);
lean_dec_ref(v_x_2789_);
return v_res_2791_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1(lean_object* v_x_2793_, size_t v_x_2794_, size_t v_x_2795_, lean_object* v_x_2796_){
_start:
{
if (lean_obj_tag(v_x_2793_) == 0)
{
lean_object* v_cs_2797_; lean_object* v___x_2798_; size_t v___x_2799_; lean_object* v_j_2800_; lean_object* v___x_2801_; size_t v___x_2802_; size_t v___x_2803_; size_t v___x_2804_; size_t v___x_2805_; size_t v___x_2806_; size_t v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; 
v_cs_2797_ = lean_ctor_get(v_x_2793_, 0);
v___x_2798_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___closed__0);
v___x_2799_ = lean_usize_shift_right(v_x_2794_, v_x_2795_);
v_j_2800_ = lean_usize_to_nat(v___x_2799_);
v___x_2801_ = lean_array_get_borrowed(v___x_2798_, v_cs_2797_, v_j_2800_);
v___x_2802_ = ((size_t)1ULL);
v___x_2803_ = lean_usize_shift_left(v___x_2802_, v_x_2795_);
v___x_2804_ = lean_usize_sub(v___x_2803_, v___x_2802_);
v___x_2805_ = lean_usize_land(v_x_2794_, v___x_2804_);
v___x_2806_ = ((size_t)5ULL);
v___x_2807_ = lean_usize_sub(v_x_2795_, v___x_2806_);
v___x_2808_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1(v___x_2801_, v___x_2805_, v___x_2807_, v_x_2796_);
v___x_2809_ = lean_unsigned_to_nat(1u);
v___x_2810_ = lean_nat_add(v_j_2800_, v___x_2809_);
lean_dec(v_j_2800_);
v___x_2811_ = lean_array_get_size(v_cs_2797_);
v___x_2812_ = lean_nat_dec_lt(v___x_2810_, v___x_2811_);
if (v___x_2812_ == 0)
{
lean_dec(v___x_2810_);
return v___x_2808_;
}
else
{
size_t v___x_2813_; size_t v___x_2814_; lean_object* v___x_2815_; 
v___x_2813_ = lean_usize_of_nat(v___x_2810_);
lean_dec(v___x_2810_);
v___x_2814_ = lean_usize_of_nat(v___x_2811_);
v___x_2815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2(v_cs_2797_, v___x_2813_, v___x_2814_, v___x_2808_);
return v___x_2815_;
}
}
else
{
lean_object* v_vs_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; uint8_t v___x_2819_; 
v_vs_2816_ = lean_ctor_get(v_x_2793_, 0);
v___x_2817_ = lean_usize_to_nat(v_x_2794_);
v___x_2818_ = lean_array_get_size(v_vs_2816_);
v___x_2819_ = lean_nat_dec_lt(v___x_2817_, v___x_2818_);
if (v___x_2819_ == 0)
{
lean_dec(v___x_2817_);
return v_x_2796_;
}
else
{
size_t v___x_2820_; size_t v___x_2821_; lean_object* v___x_2822_; 
v___x_2820_ = lean_usize_of_nat(v___x_2817_);
lean_dec(v___x_2817_);
v___x_2821_ = lean_usize_of_nat(v___x_2818_);
v___x_2822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_vs_2816_, v___x_2820_, v___x_2821_, v_x_2796_);
return v___x_2822_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___boxed(lean_object* v_x_2823_, lean_object* v_x_2824_, lean_object* v_x_2825_, lean_object* v_x_2826_){
_start:
{
size_t v_x_1498__boxed_2827_; size_t v_x_1499__boxed_2828_; lean_object* v_res_2829_; 
v_x_1498__boxed_2827_ = lean_unbox_usize(v_x_2824_);
lean_dec(v_x_2824_);
v_x_1499__boxed_2828_ = lean_unbox_usize(v_x_2825_);
lean_dec(v_x_2825_);
v_res_2829_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1(v_x_2823_, v_x_1498__boxed_2827_, v_x_1499__boxed_2828_, v_x_2826_);
lean_dec_ref(v_x_2823_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0(lean_object* v_t_2830_, lean_object* v_init_2831_, lean_object* v_start_2832_){
_start:
{
lean_object* v___x_2833_; uint8_t v___x_2834_; 
v___x_2833_ = lean_unsigned_to_nat(0u);
v___x_2834_ = lean_nat_dec_eq(v_start_2832_, v___x_2833_);
if (v___x_2834_ == 0)
{
lean_object* v_root_2835_; lean_object* v_tail_2836_; size_t v_shift_2837_; lean_object* v_tailOff_2838_; uint8_t v___x_2839_; 
v_root_2835_ = lean_ctor_get(v_t_2830_, 0);
v_tail_2836_ = lean_ctor_get(v_t_2830_, 1);
v_shift_2837_ = lean_ctor_get_usize(v_t_2830_, 4);
v_tailOff_2838_ = lean_ctor_get(v_t_2830_, 3);
v___x_2839_ = lean_nat_dec_le(v_tailOff_2838_, v_start_2832_);
if (v___x_2839_ == 0)
{
size_t v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
v___x_2840_ = lean_usize_of_nat(v_start_2832_);
v___x_2841_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1(v_root_2835_, v___x_2840_, v_shift_2837_, v_init_2831_);
v___x_2842_ = lean_array_get_size(v_tail_2836_);
v___x_2843_ = lean_nat_dec_lt(v___x_2833_, v___x_2842_);
if (v___x_2843_ == 0)
{
return v___x_2841_;
}
else
{
size_t v___x_2844_; size_t v___x_2845_; lean_object* v___x_2846_; 
v___x_2844_ = ((size_t)0ULL);
v___x_2845_ = lean_usize_of_nat(v___x_2842_);
v___x_2846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_tail_2836_, v___x_2844_, v___x_2845_, v___x_2841_);
return v___x_2846_;
}
}
else
{
lean_object* v___x_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; 
v___x_2847_ = lean_nat_sub(v_start_2832_, v_tailOff_2838_);
v___x_2848_ = lean_array_get_size(v_tail_2836_);
v___x_2849_ = lean_nat_dec_lt(v___x_2847_, v___x_2848_);
if (v___x_2849_ == 0)
{
lean_dec(v___x_2847_);
return v_init_2831_;
}
else
{
size_t v___x_2850_; size_t v___x_2851_; lean_object* v___x_2852_; 
v___x_2850_ = lean_usize_of_nat(v___x_2847_);
lean_dec(v___x_2847_);
v___x_2851_ = lean_usize_of_nat(v___x_2848_);
v___x_2852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_tail_2836_, v___x_2850_, v___x_2851_, v_init_2831_);
return v___x_2852_;
}
}
}
else
{
lean_object* v_root_2853_; lean_object* v_tail_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; uint8_t v___x_2857_; 
v_root_2853_ = lean_ctor_get(v_t_2830_, 0);
v_tail_2854_ = lean_ctor_get(v_t_2830_, 1);
v___x_2855_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3(v_root_2853_, v_init_2831_);
v___x_2856_ = lean_array_get_size(v_tail_2854_);
v___x_2857_ = lean_nat_dec_lt(v___x_2833_, v___x_2856_);
if (v___x_2857_ == 0)
{
return v___x_2855_;
}
else
{
size_t v___x_2858_; size_t v___x_2859_; lean_object* v___x_2860_; 
v___x_2858_ = ((size_t)0ULL);
v___x_2859_ = lean_usize_of_nat(v___x_2856_);
v___x_2860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_tail_2854_, v___x_2858_, v___x_2859_, v___x_2855_);
return v___x_2860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0___boxed(lean_object* v_t_2861_, lean_object* v_init_2862_, lean_object* v_start_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0(v_t_2861_, v_init_2862_, v_start_2863_);
lean_dec(v_start_2863_);
lean_dec_ref(v_t_2861_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0(lean_object* v_lctx_2865_, lean_object* v_init_2866_, lean_object* v_start_2867_){
_start:
{
lean_object* v_decls_2868_; lean_object* v___x_2869_; 
v_decls_2868_ = lean_ctor_get(v_lctx_2865_, 1);
v___x_2869_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0(v_decls_2868_, v_init_2866_, v_start_2867_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0___boxed(lean_object* v_lctx_2870_, lean_object* v_init_2871_, lean_object* v_start_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0(v_lctx_2870_, v_init_2871_, v_start_2872_);
lean_dec(v_start_2872_);
lean_dec_ref(v_lctx_2870_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals(lean_object* v_jp_2876_, lean_object* v_jump_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v_proof_2883_; lean_object* v___x_2884_; 
v_proof_2883_ = lean_ctor_get(v_jump_2877_, 0);
lean_inc(v_proof_2883_);
lean_dec_ref(v_jump_2877_);
v___x_2884_ = l_Lean_MVarId_getDecl(v_proof_2883_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2901_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2887_ = v___x_2884_;
v_isShared_2888_ = v_isSharedCheck_2901_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2884_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2901_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v_lctx_2889_; lean_object* v_spec_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2899_; 
v_lctx_2889_ = lean_ctor_get(v_a_2885_, 1);
lean_inc_ref_n(v_lctx_2889_, 2);
lean_dec(v_a_2885_);
v_spec_2890_ = lean_ctor_get(v_jp_2876_, 0);
v___x_2891_ = l_Lean_Expr_fvarId_x21(v_spec_2890_);
v___x_2892_ = l_Lean_LocalContext_get_x21(v_lctx_2889_, v___x_2891_);
v___x_2893_ = l_Lean_LocalDecl_index(v___x_2892_);
lean_dec_ref(v___x_2892_);
v___x_2894_ = lean_unsigned_to_nat(1u);
v___x_2895_ = lean_nat_add(v___x_2893_, v___x_2894_);
lean_dec(v___x_2893_);
v___x_2896_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals___closed__0));
v___x_2897_ = l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0(v_lctx_2889_, v___x_2896_, v___x_2895_);
lean_dec(v___x_2895_);
lean_dec_ref(v_lctx_2889_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v___x_2897_);
v___x_2899_ = v___x_2887_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2897_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
else
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
v_a_2902_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2884_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2884_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals___boxed(lean_object* v_jp_2910_, lean_object* v_jump_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals(v_jp_2910_, v_jump_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_);
lean_dec(v_a_2915_);
lean_dec_ref(v_a_2914_);
lean_dec(v_a_2913_);
lean_dec_ref(v_a_2912_);
lean_dec_ref(v_jp_2910_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg(lean_object* v_d_2921_, lean_object* v_00_u03c6_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_){
_start:
{
uint8_t v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = 0;
v___x_2931_ = l_Lean_LocalDecl_value_x3f(v_d_2921_, v___x_2930_);
if (lean_obj_tag(v___x_2931_) == 0)
{
uint8_t v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; uint8_t v___x_2937_; lean_object* v___x_2938_; 
v___x_2932_ = 1;
lean_inc_ref(v_d_2921_);
v___x_2933_ = l_Lean_LocalDecl_toExpr(v_d_2921_);
v___x_2934_ = lean_unsigned_to_nat(1u);
v___x_2935_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___x_2936_ = lean_array_push(v___x_2935_, v___x_2933_);
v___x_2937_ = 1;
v___x_2938_ = l_Lean_Meta_mkLambdaFVars(v___x_2936_, v_00_u03c6_2922_, v___x_2930_, v___x_2932_, v___x_2930_, v___x_2932_, v___x_2937_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
lean_dec_ref(v___x_2936_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref_known(v___x_2938_, 1);
v___x_2940_ = l_Lean_LocalDecl_type(v_d_2921_);
lean_dec_ref(v_d_2921_);
lean_inc_ref(v___x_2940_);
v___x_2941_ = l_Lean_Meta_Sym_inferType(v___x_2940_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2976_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2944_ = v___x_2941_;
v_isShared_2945_ = v_isSharedCheck_2976_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2941_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2976_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
uint8_t v___x_2969_; 
v___x_2969_ = l_Lean_Expr_isProp(v_a_2942_);
lean_dec(v_a_2942_);
if (v___x_2969_ == 0)
{
lean_del_object(v___x_2944_);
goto v___jp_2946_;
}
else
{
lean_object* v___x_2970_; uint8_t v___x_2971_; 
v___x_2970_ = l_Lean_Expr_bindingBody_x21(v_a_2939_);
v___x_2971_ = l_Lean_Expr_hasLooseBVars(v___x_2970_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2972_; lean_object* v___x_2974_; 
lean_dec(v_a_2939_);
v___x_2972_ = l_Lean_mkAnd(v___x_2940_, v___x_2970_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 0, v___x_2972_);
v___x_2974_ = v___x_2944_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
else
{
lean_dec_ref(v___x_2970_);
lean_del_object(v___x_2944_);
goto v___jp_2946_;
}
}
v___jp_2946_:
{
lean_object* v___x_2947_; 
lean_inc_ref(v___x_2940_);
v___x_2947_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_2940_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2960_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2950_ = v___x_2947_;
v_isShared_2951_ = v_isSharedCheck_2960_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2947_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2960_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2958_; 
v___x_2952_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___closed__1));
v___x_2953_ = lean_box(0);
v___x_2954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2954_, 0, v_a_2948_);
lean_ctor_set(v___x_2954_, 1, v___x_2953_);
v___x_2955_ = l_Lean_mkConst(v___x_2952_, v___x_2954_);
v___x_2956_ = l_Lean_mkAppB(v___x_2955_, v___x_2940_, v_a_2939_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 0, v___x_2956_);
v___x_2958_ = v___x_2950_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v___x_2956_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_dec_ref(v___x_2940_);
lean_dec(v_a_2939_);
v_a_2961_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2947_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2947_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
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
}
}
else
{
lean_dec_ref(v___x_2940_);
lean_dec(v_a_2939_);
return v___x_2941_;
}
}
else
{
lean_dec_ref(v_d_2921_);
return v___x_2938_;
}
}
else
{
uint8_t v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; uint8_t v___x_2982_; lean_object* v___x_2983_; 
lean_dec_ref_known(v___x_2931_, 1);
v___x_2977_ = 1;
v___x_2978_ = l_Lean_LocalDecl_toExpr(v_d_2921_);
v___x_2979_ = lean_unsigned_to_nat(1u);
v___x_2980_ = lean_mk_empty_array_with_capacity(v___x_2979_);
v___x_2981_ = lean_array_push(v___x_2980_, v___x_2978_);
v___x_2982_ = 1;
v___x_2983_ = l_Lean_Meta_mkLetFVars(v___x_2981_, v_00_u03c6_2922_, v___x_2977_, v___x_2930_, v___x_2982_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
lean_dec_ref(v___x_2981_);
return v___x_2983_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___boxed(lean_object* v_d_2984_, lean_object* v_00_u03c6_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg(v_d_2984_, v_00_u03c6_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_);
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
lean_dec(v_a_2989_);
lean_dec_ref(v_a_2988_);
lean_dec(v_a_2987_);
lean_dec_ref(v_a_2986_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal(lean_object* v_d_2994_, lean_object* v_00_u03c6_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg(v_d_2994_, v_00_u03c6_2995_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___boxed(lean_object* v_d_3009_, lean_object* v_00_u03c6_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal(v_d_3009_, v_00_u03c6_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
lean_dec(v_a_3019_);
lean_dec_ref(v_a_3018_);
lean_dec(v_a_3017_);
lean_dec_ref(v_a_3016_);
lean_dec(v_a_3015_);
lean_dec_ref(v_a_3014_);
lean_dec(v_a_3013_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
return v_res_3023_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__2(void){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3027_ = lean_box(0);
v___x_3028_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__1));
v___x_3029_ = l_Lean_mkConst(v___x_3028_, v___x_3027_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(lean_object* v_ps_3030_, lean_object* v_lo_3031_, lean_object* v_hi_3032_){
_start:
{
uint8_t v___x_3033_; 
v___x_3033_ = lean_nat_dec_eq(v_hi_3032_, v_lo_3031_);
if (v___x_3033_ == 0)
{
lean_object* v___x_3034_; lean_object* v___x_3035_; uint8_t v___x_3036_; 
v___x_3034_ = lean_unsigned_to_nat(1u);
v___x_3035_ = lean_nat_add(v_lo_3031_, v___x_3034_);
v___x_3036_ = lean_nat_dec_eq(v_hi_3032_, v___x_3035_);
lean_dec(v___x_3035_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; lean_object* v_mid_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3037_ = lean_nat_add(v_lo_3031_, v_hi_3032_);
v_mid_3038_ = lean_nat_shiftr(v___x_3037_, v___x_3034_);
lean_dec(v___x_3037_);
v___x_3039_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(v_ps_3030_, v_lo_3031_, v_mid_3038_);
v___x_3040_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(v_ps_3030_, v_mid_3038_, v_hi_3032_);
lean_dec(v_mid_3038_);
v___x_3041_ = l_Lean_mkOr(v___x_3039_, v___x_3040_);
return v___x_3041_;
}
else
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = l_Lean_instInhabitedExpr;
v___x_3043_ = lean_array_get_borrowed(v___x_3042_, v_ps_3030_, v_lo_3031_);
lean_inc(v___x_3043_);
return v___x_3043_;
}
}
else
{
lean_object* v___x_3044_; 
v___x_3044_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__2, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__2_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__2);
return v___x_3044_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___boxed(lean_object* v_ps_3045_, lean_object* v_lo_3046_, lean_object* v_hi_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(v_ps_3045_, v_lo_3046_, v_hi_3047_);
lean_dec(v_hi_3047_);
lean_dec(v_lo_3046_);
lean_dec_ref(v_ps_3045_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(lean_object* v_msg_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v_ref_3055_; lean_object* v___x_3056_; lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3065_; 
v_ref_3055_ = lean_ctor_get(v___y_3052_, 2);
v___x_3056_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6_spec__7(v_msg_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3059_ = v___x_3056_;
v_isShared_3060_ = v_isSharedCheck_3065_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3056_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3065_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3061_; lean_object* v___x_3063_; 
lean_inc(v_ref_3055_);
v___x_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3061_, 0, v_ref_3055_);
lean_ctor_set(v___x_3061_, 1, v_a_3057_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set_tag(v___x_3059_, 1);
lean_ctor_set(v___x_3059_, 0, v___x_3061_);
v___x_3063_ = v___x_3059_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3061_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg___boxed(lean_object* v_msg_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v_msg_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
return v_res_3072_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__1(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__0));
v___x_3075_ = l_Lean_stringToMessageData(v___x_3074_);
return v___x_3075_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__6(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3083_ = lean_box(0);
v___x_3084_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__5));
v___x_3085_ = l_Lean_mkConst(v___x_3084_, v___x_3083_);
return v___x_3085_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__9(void){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3090_ = lean_box(0);
v___x_3091_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__8));
v___x_3092_ = l_Lean_mkConst(v___x_3091_, v___x_3090_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(lean_object* v_00_u03c6_3093_, lean_object* v_i_3094_, lean_object* v_lo_3095_, lean_object* v_hi_3096_, lean_object* v_k_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___x_3112_; lean_object* v___x_3113_; uint8_t v___x_3114_; 
v___x_3112_ = lean_unsigned_to_nat(1u);
v___x_3113_ = lean_nat_add(v_lo_3095_, v___x_3112_);
v___x_3114_ = lean_nat_dec_eq(v_hi_3096_, v___x_3113_);
lean_dec(v___x_3113_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3115_; uint8_t v___x_3116_; 
v___x_3115_ = l_Lean_Expr_cleanupAnnotations(v_00_u03c6_3093_);
v___x_3116_ = l_Lean_Expr_isApp(v___x_3115_);
if (v___x_3116_ == 0)
{
lean_dec_ref(v___x_3115_);
lean_dec_ref(v_k_3097_);
v___y_3104_ = v_a_3098_;
v___y_3105_ = v_a_3099_;
v___y_3106_ = v_a_3100_;
v___y_3107_ = v_a_3101_;
goto v___jp_3103_;
}
else
{
lean_object* v___x_3117_; uint8_t v___x_3118_; 
v___x_3117_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3115_);
v___x_3118_ = l_Lean_Expr_isApp(v___x_3117_);
if (v___x_3118_ == 0)
{
lean_dec_ref(v___x_3117_);
lean_dec_ref(v___x_3115_);
lean_dec_ref(v_k_3097_);
v___y_3104_ = v_a_3098_;
v___y_3105_ = v_a_3099_;
v___y_3106_ = v_a_3100_;
v___y_3107_ = v_a_3101_;
goto v___jp_3103_;
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3120_; uint8_t v___x_3121_; 
v___x_3119_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3117_);
v___x_3120_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__3));
v___x_3121_ = l_Lean_Expr_isConstOf(v___x_3119_, v___x_3120_);
lean_dec_ref(v___x_3119_);
if (v___x_3121_ == 0)
{
lean_dec_ref(v___x_3117_);
lean_dec_ref(v___x_3115_);
lean_dec_ref(v_k_3097_);
v___y_3104_ = v_a_3098_;
v___y_3105_ = v_a_3099_;
v___y_3106_ = v_a_3100_;
v___y_3107_ = v_a_3101_;
goto v___jp_3103_;
}
else
{
lean_object* v_arg_3122_; lean_object* v_arg_3123_; lean_object* v___x_3124_; lean_object* v_mid_3125_; uint8_t v___x_3126_; 
lean_dec_ref(v_00_u03c6_3093_);
v_arg_3122_ = lean_ctor_get(v___x_3115_, 1);
lean_inc_ref(v_arg_3122_);
lean_dec_ref(v___x_3115_);
v_arg_3123_ = lean_ctor_get(v___x_3117_, 1);
lean_inc_ref(v_arg_3123_);
lean_dec_ref(v___x_3117_);
v___x_3124_ = lean_nat_add(v_lo_3095_, v_hi_3096_);
v_mid_3125_ = lean_nat_shiftr(v___x_3124_, v___x_3112_);
lean_dec(v___x_3124_);
v___x_3126_ = lean_nat_dec_lt(v_i_3094_, v_mid_3125_);
if (v___x_3126_ == 0)
{
lean_object* v___x_3127_; 
lean_inc_ref(v_arg_3122_);
v___x_3127_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(v_arg_3122_, v_i_3094_, v_mid_3125_, v_hi_3096_, v_k_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_);
lean_dec(v_mid_3125_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3137_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3137_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3137_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3135_; 
v___x_3132_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__6, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__6_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__6);
v___x_3133_ = l_Lean_mkApp3(v___x_3132_, v_arg_3123_, v_arg_3122_, v_a_3128_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v___x_3133_);
v___x_3135_ = v___x_3130_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3133_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
else
{
lean_dec_ref(v_arg_3123_);
lean_dec_ref(v_arg_3122_);
return v___x_3127_;
}
}
else
{
lean_object* v___x_3138_; 
lean_inc_ref(v_arg_3123_);
v___x_3138_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(v_arg_3123_, v_i_3094_, v_lo_3095_, v_mid_3125_, v_k_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_);
lean_dec(v_mid_3125_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3148_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3141_ = v___x_3138_;
v_isShared_3142_ = v_isSharedCheck_3148_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3138_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3148_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3146_; 
v___x_3143_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__9, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__9);
v___x_3144_ = l_Lean_mkApp3(v___x_3143_, v_arg_3123_, v_arg_3122_, v_a_3139_);
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 0, v___x_3144_);
v___x_3146_ = v___x_3141_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3144_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
else
{
lean_dec_ref(v_arg_3123_);
lean_dec_ref(v_arg_3122_);
return v___x_3138_;
}
}
}
}
}
}
else
{
lean_object* v___x_3149_; 
lean_inc(v_a_3101_);
lean_inc_ref(v_a_3100_);
lean_inc(v_a_3099_);
lean_inc_ref(v_a_3098_);
v___x_3149_ = lean_apply_6(v_k_3097_, v_00_u03c6_3093_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, lean_box(0));
return v___x_3149_;
}
v___jp_3103_:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3108_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__1, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__1);
v___x_3109_ = l_Lean_indentExpr(v_00_u03c6_3093_);
v___x_3110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3108_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
v___x_3111_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v___x_3110_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
return v___x_3111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___boxed(lean_object* v_00_u03c6_3150_, lean_object* v_i_3151_, lean_object* v_lo_3152_, lean_object* v_hi_3153_, lean_object* v_k_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(v_00_u03c6_3150_, v_i_3151_, v_lo_3152_, v_hi_3153_, v_k_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
lean_dec(v_hi_3153_);
lean_dec(v_lo_3152_);
lean_dec(v_i_3151_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0(lean_object* v_00_u03b1_3161_, lean_object* v_msg_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
lean_object* v___x_3168_; 
v___x_3168_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v_msg_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___boxed(lean_object* v_00_u03b1_3169_, lean_object* v_msg_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0(v_00_u03b1_3169_, v_msg_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(lean_object* v_lctx_3177_, lean_object* v_localInsts_3178_, lean_object* v_x_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v___f_3192_; lean_object* v___x_3193_; 
lean_inc(v___y_3186_);
lean_inc_ref(v___y_3185_);
lean_inc(v___y_3184_);
lean_inc_ref(v___y_3183_);
lean_inc(v___y_3182_);
lean_inc(v___y_3181_);
lean_inc_ref(v___y_3180_);
v___f_3192_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_3192_, 0, v_x_3179_);
lean_closure_set(v___f_3192_, 1, v___y_3180_);
lean_closure_set(v___f_3192_, 2, v___y_3181_);
lean_closure_set(v___f_3192_, 3, v___y_3182_);
lean_closure_set(v___f_3192_, 4, v___y_3183_);
lean_closure_set(v___f_3192_, 5, v___y_3184_);
lean_closure_set(v___f_3192_, 6, v___y_3185_);
lean_closure_set(v___f_3192_, 7, v___y_3186_);
v___x_3193_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_3177_, v_localInsts_3178_, v___f_3192_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
if (lean_obj_tag(v___x_3193_) == 0)
{
return v___x_3193_;
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3193_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3193_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg___boxed(lean_object* v_lctx_3202_, lean_object* v_localInsts_3203_, lean_object* v_x_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(v_lctx_3202_, v_localInsts_3203_, v_x_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6(lean_object* v_00_u03b1_3218_, lean_object* v_lctx_3219_, lean_object* v_localInsts_3220_, lean_object* v_x_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(v_lctx_3219_, v_localInsts_3220_, v_x_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___boxed(lean_object* v_00_u03b1_3235_, lean_object* v_lctx_3236_, lean_object* v_localInsts_3237_, lean_object* v_x_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6(v_00_u03b1_3235_, v_lctx_3236_, v_localInsts_3237_, v_x_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg(lean_object* v_a_3252_, lean_object* v_x_3253_){
_start:
{
if (lean_obj_tag(v_x_3253_) == 0)
{
lean_object* v___x_3254_; 
v___x_3254_ = lean_box(0);
return v___x_3254_;
}
else
{
lean_object* v_key_3255_; lean_object* v_value_3256_; lean_object* v_tail_3257_; uint8_t v___x_3258_; 
v_key_3255_ = lean_ctor_get(v_x_3253_, 0);
v_value_3256_ = lean_ctor_get(v_x_3253_, 1);
v_tail_3257_ = lean_ctor_get(v_x_3253_, 2);
v___x_3258_ = l_Lean_instBEqFVarId_beq(v_key_3255_, v_a_3252_);
if (v___x_3258_ == 0)
{
v_x_3253_ = v_tail_3257_;
goto _start;
}
else
{
lean_object* v___x_3260_; 
lean_inc(v_value_3256_);
v___x_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3260_, 0, v_value_3256_);
return v___x_3260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg___boxed(lean_object* v_a_3261_, lean_object* v_x_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg(v_a_3261_, v_x_3262_);
lean_dec(v_x_3262_);
lean_dec(v_a_3261_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg(lean_object* v_m_3264_, lean_object* v_a_3265_){
_start:
{
lean_object* v_buckets_3266_; lean_object* v___x_3267_; uint64_t v___x_3268_; uint64_t v___x_3269_; uint64_t v___x_3270_; uint64_t v_fold_3271_; uint64_t v___x_3272_; uint64_t v___x_3273_; uint64_t v___x_3274_; size_t v___x_3275_; size_t v___x_3276_; size_t v___x_3277_; size_t v___x_3278_; size_t v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v_buckets_3266_ = lean_ctor_get(v_m_3264_, 1);
v___x_3267_ = lean_array_get_size(v_buckets_3266_);
v___x_3268_ = l_Lean_instHashableFVarId_hash(v_a_3265_);
v___x_3269_ = 32ULL;
v___x_3270_ = lean_uint64_shift_right(v___x_3268_, v___x_3269_);
v_fold_3271_ = lean_uint64_xor(v___x_3268_, v___x_3270_);
v___x_3272_ = 16ULL;
v___x_3273_ = lean_uint64_shift_right(v_fold_3271_, v___x_3272_);
v___x_3274_ = lean_uint64_xor(v_fold_3271_, v___x_3273_);
v___x_3275_ = lean_uint64_to_usize(v___x_3274_);
v___x_3276_ = lean_usize_of_nat(v___x_3267_);
v___x_3277_ = ((size_t)1ULL);
v___x_3278_ = lean_usize_sub(v___x_3276_, v___x_3277_);
v___x_3279_ = lean_usize_land(v___x_3275_, v___x_3278_);
v___x_3280_ = lean_array_uget_borrowed(v_buckets_3266_, v___x_3279_);
v___x_3281_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg(v_a_3265_, v___x_3280_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg___boxed(lean_object* v_m_3282_, lean_object* v_a_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg(v_m_3282_, v_a_3283_);
lean_dec(v_a_3283_);
lean_dec_ref(v_m_3282_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4___redArg(lean_object* v_a_3285_, lean_object* v_b_3286_, lean_object* v_x_3287_){
_start:
{
if (lean_obj_tag(v_x_3287_) == 0)
{
lean_dec(v_b_3286_);
lean_dec(v_a_3285_);
return v_x_3287_;
}
else
{
lean_object* v_key_3288_; lean_object* v_value_3289_; lean_object* v_tail_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3302_; 
v_key_3288_ = lean_ctor_get(v_x_3287_, 0);
v_value_3289_ = lean_ctor_get(v_x_3287_, 1);
v_tail_3290_ = lean_ctor_get(v_x_3287_, 2);
v_isSharedCheck_3302_ = !lean_is_exclusive(v_x_3287_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3292_ = v_x_3287_;
v_isShared_3293_ = v_isSharedCheck_3302_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_tail_3290_);
lean_inc(v_value_3289_);
lean_inc(v_key_3288_);
lean_dec(v_x_3287_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3302_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
uint8_t v___x_3294_; 
v___x_3294_ = l_Lean_instBEqFVarId_beq(v_key_3288_, v_a_3285_);
if (v___x_3294_ == 0)
{
lean_object* v___x_3295_; lean_object* v___x_3297_; 
v___x_3295_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4___redArg(v_a_3285_, v_b_3286_, v_tail_3290_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 2, v___x_3295_);
v___x_3297_ = v___x_3292_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_key_3288_);
lean_ctor_set(v_reuseFailAlloc_3298_, 1, v_value_3289_);
lean_ctor_set(v_reuseFailAlloc_3298_, 2, v___x_3295_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
else
{
lean_object* v___x_3300_; 
lean_dec(v_value_3289_);
lean_dec(v_key_3288_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 1, v_b_3286_);
lean_ctor_set(v___x_3292_, 0, v_a_3285_);
v___x_3300_ = v___x_3292_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3285_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v_b_3286_);
lean_ctor_set(v_reuseFailAlloc_3301_, 2, v_tail_3290_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg(lean_object* v_a_3303_, lean_object* v_x_3304_){
_start:
{
if (lean_obj_tag(v_x_3304_) == 0)
{
uint8_t v___x_3305_; 
v___x_3305_ = 0;
return v___x_3305_;
}
else
{
lean_object* v_key_3306_; lean_object* v_tail_3307_; uint8_t v___x_3308_; 
v_key_3306_ = lean_ctor_get(v_x_3304_, 0);
v_tail_3307_ = lean_ctor_get(v_x_3304_, 2);
v___x_3308_ = l_Lean_instBEqFVarId_beq(v_key_3306_, v_a_3303_);
if (v___x_3308_ == 0)
{
v_x_3304_ = v_tail_3307_;
goto _start;
}
else
{
return v___x_3308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg___boxed(lean_object* v_a_3310_, lean_object* v_x_3311_){
_start:
{
uint8_t v_res_3312_; lean_object* v_r_3313_; 
v_res_3312_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg(v_a_3310_, v_x_3311_);
lean_dec(v_x_3311_);
lean_dec(v_a_3310_);
v_r_3313_ = lean_box(v_res_3312_);
return v_r_3313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5_spec__11___redArg(lean_object* v_x_3314_, lean_object* v_x_3315_){
_start:
{
if (lean_obj_tag(v_x_3315_) == 0)
{
return v_x_3314_;
}
else
{
lean_object* v_key_3316_; lean_object* v_value_3317_; lean_object* v_tail_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3341_; 
v_key_3316_ = lean_ctor_get(v_x_3315_, 0);
v_value_3317_ = lean_ctor_get(v_x_3315_, 1);
v_tail_3318_ = lean_ctor_get(v_x_3315_, 2);
v_isSharedCheck_3341_ = !lean_is_exclusive(v_x_3315_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3320_ = v_x_3315_;
v_isShared_3321_ = v_isSharedCheck_3341_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_tail_3318_);
lean_inc(v_value_3317_);
lean_inc(v_key_3316_);
lean_dec(v_x_3315_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3341_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3322_; uint64_t v___x_3323_; uint64_t v___x_3324_; uint64_t v___x_3325_; uint64_t v_fold_3326_; uint64_t v___x_3327_; uint64_t v___x_3328_; uint64_t v___x_3329_; size_t v___x_3330_; size_t v___x_3331_; size_t v___x_3332_; size_t v___x_3333_; size_t v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3337_; 
v___x_3322_ = lean_array_get_size(v_x_3314_);
v___x_3323_ = l_Lean_instHashableFVarId_hash(v_key_3316_);
v___x_3324_ = 32ULL;
v___x_3325_ = lean_uint64_shift_right(v___x_3323_, v___x_3324_);
v_fold_3326_ = lean_uint64_xor(v___x_3323_, v___x_3325_);
v___x_3327_ = 16ULL;
v___x_3328_ = lean_uint64_shift_right(v_fold_3326_, v___x_3327_);
v___x_3329_ = lean_uint64_xor(v_fold_3326_, v___x_3328_);
v___x_3330_ = lean_uint64_to_usize(v___x_3329_);
v___x_3331_ = lean_usize_of_nat(v___x_3322_);
v___x_3332_ = ((size_t)1ULL);
v___x_3333_ = lean_usize_sub(v___x_3331_, v___x_3332_);
v___x_3334_ = lean_usize_land(v___x_3330_, v___x_3333_);
v___x_3335_ = lean_array_uget_borrowed(v_x_3314_, v___x_3334_);
lean_inc(v___x_3335_);
if (v_isShared_3321_ == 0)
{
lean_ctor_set(v___x_3320_, 2, v___x_3335_);
v___x_3337_ = v___x_3320_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_key_3316_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v_value_3317_);
lean_ctor_set(v_reuseFailAlloc_3340_, 2, v___x_3335_);
v___x_3337_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
lean_object* v___x_3338_; 
v___x_3338_ = lean_array_uset(v_x_3314_, v___x_3334_, v___x_3337_);
v_x_3314_ = v___x_3338_;
v_x_3315_ = v_tail_3318_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5___redArg(lean_object* v_i_3342_, lean_object* v_source_3343_, lean_object* v_target_3344_){
_start:
{
lean_object* v___x_3345_; uint8_t v___x_3346_; 
v___x_3345_ = lean_array_get_size(v_source_3343_);
v___x_3346_ = lean_nat_dec_lt(v_i_3342_, v___x_3345_);
if (v___x_3346_ == 0)
{
lean_dec_ref(v_source_3343_);
lean_dec(v_i_3342_);
return v_target_3344_;
}
else
{
lean_object* v_es_3347_; lean_object* v___x_3348_; lean_object* v_source_3349_; lean_object* v_target_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v_es_3347_ = lean_array_fget(v_source_3343_, v_i_3342_);
v___x_3348_ = lean_box(0);
v_source_3349_ = lean_array_fset(v_source_3343_, v_i_3342_, v___x_3348_);
v_target_3350_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5_spec__11___redArg(v_target_3344_, v_es_3347_);
v___x_3351_ = lean_unsigned_to_nat(1u);
v___x_3352_ = lean_nat_add(v_i_3342_, v___x_3351_);
lean_dec(v_i_3342_);
v_i_3342_ = v___x_3352_;
v_source_3343_ = v_source_3349_;
v_target_3344_ = v_target_3350_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3___redArg(lean_object* v_data_3354_){
_start:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v_nbuckets_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3355_ = lean_array_get_size(v_data_3354_);
v___x_3356_ = lean_unsigned_to_nat(2u);
v_nbuckets_3357_ = lean_nat_mul(v___x_3355_, v___x_3356_);
v___x_3358_ = lean_unsigned_to_nat(0u);
v___x_3359_ = lean_box(0);
v___x_3360_ = lean_mk_array(v_nbuckets_3357_, v___x_3359_);
v___x_3361_ = lean_array_propagate_mark(v_data_3354_, v___x_3360_);
v___x_3362_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5___redArg(v___x_3358_, v_data_3354_, v___x_3361_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1___redArg(lean_object* v_m_3363_, lean_object* v_a_3364_, lean_object* v_b_3365_){
_start:
{
lean_object* v_size_3366_; lean_object* v_buckets_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3410_; 
v_size_3366_ = lean_ctor_get(v_m_3363_, 0);
v_buckets_3367_ = lean_ctor_get(v_m_3363_, 1);
v_isSharedCheck_3410_ = !lean_is_exclusive(v_m_3363_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3369_ = v_m_3363_;
v_isShared_3370_ = v_isSharedCheck_3410_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_buckets_3367_);
lean_inc(v_size_3366_);
lean_dec(v_m_3363_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3410_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3371_; uint64_t v___x_3372_; uint64_t v___x_3373_; uint64_t v___x_3374_; uint64_t v_fold_3375_; uint64_t v___x_3376_; uint64_t v___x_3377_; uint64_t v___x_3378_; size_t v___x_3379_; size_t v___x_3380_; size_t v___x_3381_; size_t v___x_3382_; size_t v___x_3383_; lean_object* v_bkt_3384_; uint8_t v___x_3385_; 
v___x_3371_ = lean_array_get_size(v_buckets_3367_);
v___x_3372_ = l_Lean_instHashableFVarId_hash(v_a_3364_);
v___x_3373_ = 32ULL;
v___x_3374_ = lean_uint64_shift_right(v___x_3372_, v___x_3373_);
v_fold_3375_ = lean_uint64_xor(v___x_3372_, v___x_3374_);
v___x_3376_ = 16ULL;
v___x_3377_ = lean_uint64_shift_right(v_fold_3375_, v___x_3376_);
v___x_3378_ = lean_uint64_xor(v_fold_3375_, v___x_3377_);
v___x_3379_ = lean_uint64_to_usize(v___x_3378_);
v___x_3380_ = lean_usize_of_nat(v___x_3371_);
v___x_3381_ = ((size_t)1ULL);
v___x_3382_ = lean_usize_sub(v___x_3380_, v___x_3381_);
v___x_3383_ = lean_usize_land(v___x_3379_, v___x_3382_);
v_bkt_3384_ = lean_array_uget_borrowed(v_buckets_3367_, v___x_3383_);
v___x_3385_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg(v_a_3364_, v_bkt_3384_);
if (v___x_3385_ == 0)
{
lean_object* v___x_3386_; lean_object* v_size_x27_3387_; lean_object* v___x_3388_; lean_object* v_buckets_x27_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; uint8_t v___x_3395_; 
v___x_3386_ = lean_unsigned_to_nat(1u);
v_size_x27_3387_ = lean_nat_add(v_size_3366_, v___x_3386_);
lean_dec(v_size_3366_);
lean_inc(v_bkt_3384_);
v___x_3388_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3388_, 0, v_a_3364_);
lean_ctor_set(v___x_3388_, 1, v_b_3365_);
lean_ctor_set(v___x_3388_, 2, v_bkt_3384_);
v_buckets_x27_3389_ = lean_array_uset(v_buckets_3367_, v___x_3383_, v___x_3388_);
v___x_3390_ = lean_unsigned_to_nat(4u);
v___x_3391_ = lean_nat_mul(v_size_x27_3387_, v___x_3390_);
v___x_3392_ = lean_unsigned_to_nat(3u);
v___x_3393_ = lean_nat_div(v___x_3391_, v___x_3392_);
lean_dec(v___x_3391_);
v___x_3394_ = lean_array_get_size(v_buckets_x27_3389_);
v___x_3395_ = lean_nat_dec_le(v___x_3393_, v___x_3394_);
lean_dec(v___x_3393_);
if (v___x_3395_ == 0)
{
lean_object* v_val_3396_; lean_object* v___x_3398_; 
v_val_3396_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3___redArg(v_buckets_x27_3389_);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 1, v_val_3396_);
lean_ctor_set(v___x_3369_, 0, v_size_x27_3387_);
v___x_3398_ = v___x_3369_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_size_x27_3387_);
lean_ctor_set(v_reuseFailAlloc_3399_, 1, v_val_3396_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
else
{
lean_object* v___x_3401_; 
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 1, v_buckets_x27_3389_);
lean_ctor_set(v___x_3369_, 0, v_size_x27_3387_);
v___x_3401_ = v___x_3369_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_size_x27_3387_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v_buckets_x27_3389_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
else
{
lean_object* v___x_3403_; lean_object* v_buckets_x27_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3408_; 
lean_inc(v_bkt_3384_);
v___x_3403_ = lean_box(0);
v_buckets_x27_3404_ = lean_array_uset(v_buckets_3367_, v___x_3383_, v___x_3403_);
v___x_3405_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4___redArg(v_a_3364_, v_b_3365_, v_bkt_3384_);
v___x_3406_ = lean_array_uset(v_buckets_x27_3404_, v___x_3383_, v___x_3405_);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 1, v___x_3406_);
v___x_3408_ = v___x_3369_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_size_3366_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v___x_3406_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg(lean_object* v_jumps_3411_, lean_object* v_i_3412_, lean_object* v_range_3413_, lean_object* v_b_3414_, lean_object* v_i_3415_){
_start:
{
lean_object* v_stop_3417_; lean_object* v_step_3418_; lean_object* v_a_3420_; lean_object* v_groups_3424_; lean_object* v_byLocal_3425_; uint8_t v___x_3431_; 
v_stop_3417_ = lean_ctor_get(v_range_3413_, 1);
v_step_3418_ = lean_ctor_get(v_range_3413_, 2);
v___x_3431_ = lean_nat_dec_lt(v_i_3415_, v_stop_3417_);
if (v___x_3431_ == 0)
{
lean_object* v___x_3432_; 
lean_dec(v_i_3415_);
v___x_3432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3432_, 0, v_b_3414_);
return v___x_3432_;
}
else
{
lean_object* v_fst_3433_; lean_object* v_snd_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3460_; 
v_fst_3433_ = lean_ctor_get(v_b_3414_, 0);
v_snd_3434_ = lean_ctor_get(v_b_3414_, 1);
v_isSharedCheck_3460_ = !lean_is_exclusive(v_b_3414_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3436_ = v_b_3414_;
v_isShared_3437_ = v_isSharedCheck_3460_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_snd_3434_);
lean_inc(v_fst_3433_);
lean_dec(v_b_3414_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3460_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___y_3439_; lean_object* v___x_3443_; lean_object* v_snd_3444_; lean_object* v___x_3445_; uint8_t v___x_3446_; 
v___x_3443_ = lean_array_fget_borrowed(v_jumps_3411_, v_i_3415_);
v_snd_3444_ = lean_ctor_get(v___x_3443_, 1);
v___x_3445_ = lean_array_get_size(v_snd_3444_);
v___x_3446_ = lean_nat_dec_lt(v_i_3412_, v___x_3445_);
if (v___x_3446_ == 0)
{
lean_del_object(v___x_3436_);
v_groups_3424_ = v_fst_3433_;
v_byLocal_3425_ = v_snd_3434_;
goto v___jp_3423_;
}
else
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3447_ = lean_array_fget_borrowed(v_snd_3444_, v_i_3412_);
v___x_3448_ = l_Lean_LocalDecl_fvarId(v___x_3447_);
v___x_3449_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg(v_snd_3434_, v___x_3448_);
if (lean_obj_tag(v___x_3449_) == 1)
{
lean_object* v_val_3450_; lean_object* v___x_3451_; uint8_t v___x_3452_; 
lean_dec(v___x_3448_);
v_val_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_val_3450_);
lean_dec_ref_known(v___x_3449_, 1);
v___x_3451_ = lean_array_get_size(v_fst_3433_);
v___x_3452_ = lean_nat_dec_lt(v_val_3450_, v___x_3451_);
if (v___x_3452_ == 0)
{
lean_dec(v_val_3450_);
v___y_3439_ = v_fst_3433_;
goto v___jp_3438_;
}
else
{
lean_object* v_v_3453_; lean_object* v___x_3454_; lean_object* v_xs_x27_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v_v_3453_ = lean_array_fget(v_fst_3433_, v_val_3450_);
v___x_3454_ = lean_box(0);
v_xs_x27_3455_ = lean_array_fset(v_fst_3433_, v_val_3450_, v___x_3454_);
lean_inc(v_i_3415_);
v___x_3456_ = lean_array_push(v_v_3453_, v_i_3415_);
v___x_3457_ = lean_array_fset(v_xs_x27_3455_, v_val_3450_, v___x_3456_);
lean_dec(v_val_3450_);
v___y_3439_ = v___x_3457_;
goto v___jp_3438_;
}
}
else
{
lean_object* v___x_3458_; lean_object* v_byLocal_3459_; 
lean_dec(v___x_3449_);
lean_del_object(v___x_3436_);
v___x_3458_ = lean_array_get_size(v_fst_3433_);
v_byLocal_3459_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1___redArg(v_snd_3434_, v___x_3448_, v___x_3458_);
v_groups_3424_ = v_fst_3433_;
v_byLocal_3425_ = v_byLocal_3459_;
goto v___jp_3423_;
}
}
v___jp_3438_:
{
lean_object* v___x_3441_; 
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 0, v___y_3439_);
v___x_3441_ = v___x_3436_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___y_3439_);
lean_ctor_set(v_reuseFailAlloc_3442_, 1, v_snd_3434_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
v_a_3420_ = v___x_3441_;
goto v___jp_3419_;
}
}
}
}
v___jp_3419_:
{
lean_object* v___x_3421_; 
v___x_3421_ = lean_nat_add(v_i_3415_, v_step_3418_);
lean_dec(v_i_3415_);
v_b_3414_ = v_a_3420_;
v_i_3415_ = v___x_3421_;
goto _start;
}
v___jp_3423_:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v_groups_3429_; lean_object* v___x_3430_; 
v___x_3426_ = lean_unsigned_to_nat(1u);
v___x_3427_ = lean_mk_empty_array_with_capacity(v___x_3426_);
lean_inc(v_i_3415_);
v___x_3428_ = lean_array_push(v___x_3427_, v_i_3415_);
v_groups_3429_ = lean_array_push(v_groups_3424_, v___x_3428_);
v___x_3430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3430_, 0, v_groups_3429_);
lean_ctor_set(v___x_3430_, 1, v_byLocal_3425_);
v_a_3420_ = v___x_3430_;
goto v___jp_3419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg___boxed(lean_object* v_jumps_3461_, lean_object* v_i_3462_, lean_object* v_range_3463_, lean_object* v_b_3464_, lean_object* v_i_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg(v_jumps_3461_, v_i_3462_, v_range_3463_, v_b_3464_, v_i_3465_);
lean_dec_ref(v_range_3463_);
lean_dec(v_i_3462_);
lean_dec_ref(v_jumps_3461_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(lean_object* v_xs_3474_, lean_object* v_fst_3475_, lean_object* v_range_3476_, lean_object* v_b_3477_, lean_object* v_i_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v_stop_3486_; lean_object* v_step_3487_; lean_object* v_a_3489_; uint8_t v___x_3492_; 
v_stop_3486_ = lean_ctor_get(v_range_3476_, 1);
v_step_3487_ = lean_ctor_get(v_range_3476_, 2);
v___x_3492_ = lean_nat_dec_lt(v_i_3478_, v_stop_3486_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3493_; 
lean_dec(v_i_3478_);
v___x_3493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3493_, 0, v_b_3477_);
return v___x_3493_;
}
else
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3494_ = l_Lean_instInhabitedExpr;
v___x_3495_ = lean_array_fget_borrowed(v_xs_3474_, v_i_3478_);
lean_inc(v___x_3495_);
v___x_3496_ = l_Lean_Meta_Sym_inferType(v___x_3495_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v___x_3498_; uint8_t v___x_3499_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3497_);
lean_dec_ref_known(v___x_3496_, 1);
v___x_3498_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__1));
v___x_3499_ = l_Lean_Expr_isConstOf(v_a_3497_, v___x_3498_);
if (v___x_3499_ == 0)
{
lean_object* v___x_3500_; 
lean_inc(v_a_3497_);
v___x_3500_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_3497_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v_args_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v___x_3500_, 1);
v_args_3502_ = lean_ctor_get(v_fst_3475_, 1);
v___x_3503_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__3));
v___x_3504_ = lean_box(0);
v___x_3505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3505_, 0, v_a_3501_);
lean_ctor_set(v___x_3505_, 1, v___x_3504_);
v___x_3506_ = l_Lean_mkConst(v___x_3503_, v___x_3505_);
v___x_3507_ = lean_array_get_borrowed(v___x_3494_, v_args_3502_, v_i_3478_);
lean_inc(v___x_3507_);
lean_inc(v___x_3495_);
v___x_3508_ = l_Lean_mkApp3(v___x_3506_, v_a_3497_, v___x_3495_, v___x_3507_);
v___x_3509_ = lean_array_push(v_b_3477_, v___x_3508_);
v_a_3489_ = v___x_3509_;
goto v___jp_3488_;
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
lean_dec(v_a_3497_);
lean_dec(v_i_3478_);
lean_dec_ref(v_b_3477_);
v_a_3510_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3500_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3500_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
else
{
lean_dec(v_a_3497_);
v_a_3489_ = v_b_3477_;
goto v___jp_3488_;
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_dec(v_i_3478_);
lean_dec_ref(v_b_3477_);
v_a_3518_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3496_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3496_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
v___jp_3488_:
{
lean_object* v___x_3490_; 
v___x_3490_ = lean_nat_add(v_i_3478_, v_step_3487_);
lean_dec(v_i_3478_);
v_b_3477_ = v_a_3489_;
v_i_3478_ = v___x_3490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___boxed(lean_object* v_xs_3526_, lean_object* v_fst_3527_, lean_object* v_range_3528_, lean_object* v_b_3529_, lean_object* v_i_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(v_xs_3526_, v_fst_3527_, v_range_3528_, v_b_3529_, v_i_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v_range_3528_);
lean_dec_ref(v_fst_3527_);
lean_dec_ref(v_xs_3526_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(lean_object* v_g_3539_, lean_object* v___x_3540_, lean_object* v_as_3541_, size_t v_sz_3542_, size_t v_i_3543_, lean_object* v_b_3544_){
_start:
{
uint8_t v___x_3546_; 
v___x_3546_ = lean_usize_dec_lt(v_i_3543_, v_sz_3542_);
if (v___x_3546_ == 0)
{
lean_object* v___x_3547_; 
lean_dec(v___x_3540_);
lean_dec(v_g_3539_);
v___x_3547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3547_, 0, v_b_3544_);
return v___x_3547_;
}
else
{
lean_object* v_a_3548_; lean_object* v_fst_3549_; lean_object* v_snd_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3562_; 
v_a_3548_ = lean_array_uget(v_as_3541_, v_i_3543_);
v_fst_3549_ = lean_ctor_get(v_a_3548_, 0);
v_snd_3550_ = lean_ctor_get(v_a_3548_, 1);
v_isSharedCheck_3562_ = !lean_is_exclusive(v_a_3548_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3552_ = v_a_3548_;
v_isShared_3553_ = v_isSharedCheck_3562_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_snd_3550_);
lean_inc(v_fst_3549_);
lean_dec(v_a_3548_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3562_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3555_; 
lean_inc(v___x_3540_);
lean_inc(v_g_3539_);
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 1, v___x_3540_);
lean_ctor_set(v___x_3552_, 0, v_g_3539_);
v___x_3555_ = v___x_3552_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_g_3539_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v___x_3540_);
v___x_3555_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; size_t v___x_3558_; size_t v___x_3559_; 
v___x_3556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3555_);
lean_ctor_set(v___x_3556_, 1, v_snd_3550_);
v___x_3557_ = lean_array_set(v_b_3544_, v_fst_3549_, v___x_3556_);
lean_dec(v_fst_3549_);
v___x_3558_ = ((size_t)1ULL);
v___x_3559_ = lean_usize_add(v_i_3543_, v___x_3558_);
v_i_3543_ = v___x_3559_;
v_b_3544_ = v___x_3557_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg___boxed(lean_object* v_g_3563_, lean_object* v___x_3564_, lean_object* v_as_3565_, lean_object* v_sz_3566_, lean_object* v_i_3567_, lean_object* v_b_3568_, lean_object* v___y_3569_){
_start:
{
size_t v_sz_boxed_3570_; size_t v_i_boxed_3571_; lean_object* v_res_3572_; 
v_sz_boxed_3570_ = lean_unbox_usize(v_sz_3566_);
lean_dec(v_sz_3566_);
v_i_boxed_3571_ = lean_unbox_usize(v_i_3567_);
lean_dec(v_i_3567_);
v_res_3572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(v_g_3563_, v___x_3564_, v_as_3565_, v_sz_boxed_3570_, v_i_boxed_3571_, v_b_3568_);
lean_dec_ref(v_as_3565_);
return v_res_3572_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3573_; 
v___x_3573_ = l_Array_instInhabited___redArg();
return v___x_3573_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1(void){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3574_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__0);
v___x_3575_ = l_Lean_Elab_Tactic_VCGen_instInhabitedJump_default;
v___x_3576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3575_);
lean_ctor_set(v___x_3576_, 1, v___x_3574_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5(lean_object* v_jumps_3577_, size_t v_sz_3578_, size_t v_i_3579_, lean_object* v_bs_3580_){
_start:
{
uint8_t v___x_3581_; 
v___x_3581_ = lean_usize_dec_lt(v_i_3579_, v_sz_3578_);
if (v___x_3581_ == 0)
{
return v_bs_3580_;
}
else
{
lean_object* v___x_3582_; lean_object* v_v_3583_; lean_object* v___x_3584_; lean_object* v_bs_x27_3585_; lean_object* v___x_3586_; size_t v___x_3587_; size_t v___x_3588_; lean_object* v___x_3589_; 
v___x_3582_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1);
v_v_3583_ = lean_array_uget(v_bs_3580_, v_i_3579_);
v___x_3584_ = lean_unsigned_to_nat(0u);
v_bs_x27_3585_ = lean_array_uset(v_bs_3580_, v_i_3579_, v___x_3584_);
v___x_3586_ = lean_array_get_borrowed(v___x_3582_, v_jumps_3577_, v_v_3583_);
lean_dec(v_v_3583_);
v___x_3587_ = ((size_t)1ULL);
v___x_3588_ = lean_usize_add(v_i_3579_, v___x_3587_);
lean_inc(v___x_3586_);
v___x_3589_ = lean_array_uset(v_bs_x27_3585_, v_i_3579_, v___x_3586_);
v_i_3579_ = v___x_3588_;
v_bs_3580_ = v___x_3589_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___boxed(lean_object* v_jumps_3591_, lean_object* v_sz_3592_, lean_object* v_i_3593_, lean_object* v_bs_3594_){
_start:
{
size_t v_sz_boxed_3595_; size_t v_i_boxed_3596_; lean_object* v_res_3597_; 
v_sz_boxed_3595_ = lean_unbox_usize(v_sz_3592_);
lean_dec(v_sz_3592_);
v_i_boxed_3596_ = lean_unbox_usize(v_i_3593_);
lean_dec(v_i_3593_);
v_res_3597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5(v_jumps_3591_, v_sz_boxed_3595_, v_i_boxed_3596_, v_bs_3594_);
lean_dec_ref(v_jumps_3591_);
return v_res_3597_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__1(void){
_start:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3600_ = lean_box(0);
v___x_3601_ = lean_unsigned_to_nat(16u);
v___x_3602_ = lean_mk_array(v___x_3601_, v___x_3600_);
return v___x_3602_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__2(void){
_start:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v_byLocal_3605_; 
v___x_3603_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__1, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__1);
v___x_3604_ = lean_unsigned_to_nat(0u);
v_byLocal_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byLocal_3605_, 0, v___x_3604_);
lean_ctor_set(v_byLocal_3605_, 1, v___x_3603_);
return v_byLocal_3605_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__3(void){
_start:
{
lean_object* v_byLocal_3606_; lean_object* v_groups_3607_; lean_object* v___x_3608_; 
v_byLocal_3606_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__2, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__2_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__2);
v_groups_3607_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__0));
v___x_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3608_, 0, v_groups_3607_);
lean_ctor_set(v___x_3608_, 1, v_byLocal_3606_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg(lean_object* v___x_3615_, lean_object* v_jumps_3616_, lean_object* v___x_3617_, lean_object* v_i_3618_, lean_object* v_xs_3619_, lean_object* v_range_3620_, lean_object* v_b_3621_, lean_object* v_i_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v_stop_3635_; lean_object* v_step_3636_; uint8_t v___x_3637_; 
v_stop_3635_ = lean_ctor_get(v_range_3620_, 1);
v_step_3636_ = lean_ctor_get(v_range_3620_, 2);
v___x_3637_ = lean_nat_dec_lt(v_i_3622_, v_stop_3635_);
if (v___x_3637_ == 0)
{
lean_object* v___x_3638_; 
lean_dec(v_i_3622_);
lean_dec(v___x_3617_);
v___x_3638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3638_, 0, v_b_3621_);
return v___x_3638_;
}
else
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v_fst_3644_; lean_object* v_snd_3645_; lean_object* v_fst_3646_; lean_object* v_snd_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3744_; 
v___x_3639_ = lean_unsigned_to_nat(0u);
v___x_3640_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1);
v___x_3641_ = lean_array_fget_borrowed(v___x_3615_, v_i_3622_);
v___x_3642_ = lean_array_get_borrowed(v___x_3639_, v___x_3641_, v___x_3639_);
v___x_3643_ = lean_array_get_borrowed(v___x_3640_, v_jumps_3616_, v___x_3642_);
v_fst_3644_ = lean_ctor_get(v___x_3643_, 0);
v_snd_3645_ = lean_ctor_get(v___x_3643_, 1);
v_fst_3646_ = lean_ctor_get(v_b_3621_, 0);
v_snd_3647_ = lean_ctor_get(v_b_3621_, 1);
v_isSharedCheck_3744_ = !lean_is_exclusive(v_b_3621_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3649_ = v_b_3621_;
v_isShared_3650_ = v_isSharedCheck_3744_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_snd_3647_);
lean_inc(v_fst_3646_);
lean_dec(v_b_3621_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3744_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v_fst_3652_; lean_object* v_snd_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___x_3684_; lean_object* v___x_3685_; uint8_t v___x_3686_; 
v___x_3684_ = lean_unsigned_to_nat(1u);
v___x_3685_ = lean_array_get_size(v_snd_3645_);
v___x_3686_ = lean_nat_dec_lt(v_i_3618_, v___x_3685_);
if (v___x_3686_ == 0)
{
lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3687_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__0));
v___x_3688_ = lean_array_get_size(v_xs_3619_);
v___x_3689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3639_);
lean_ctor_set(v___x_3689_, 1, v___x_3688_);
lean_ctor_set(v___x_3689_, 2, v___x_3684_);
v___x_3690_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(v_xs_3619_, v_fst_3644_, v___x_3689_, v___x_3687_, v___x_3639_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
lean_dec_ref_known(v___x_3689_, 3);
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v_a_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v_a_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc(v_a_3691_);
lean_dec_ref_known(v___x_3690_, 1);
v___x_3692_ = lean_array_to_list(v_a_3691_);
v___x_3693_ = l_Lean_mkAndN(v___x_3692_);
v___x_3694_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__1));
v_fst_3652_ = v___x_3693_;
v_snd_3653_ = v___x_3694_;
v___y_3654_ = v___y_3623_;
v___y_3655_ = v___y_3624_;
v___y_3656_ = v___y_3625_;
v___y_3657_ = v___y_3626_;
v___y_3658_ = v___y_3627_;
v___y_3659_ = v___y_3628_;
v___y_3660_ = v___y_3629_;
v___y_3661_ = v___y_3630_;
v___y_3662_ = v___y_3631_;
v___y_3663_ = v___y_3632_;
v___y_3664_ = v___y_3633_;
goto v___jp_3651_;
}
else
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
lean_del_object(v___x_3649_);
lean_dec(v_snd_3647_);
lean_dec(v_fst_3646_);
lean_dec(v_i_3622_);
lean_dec(v___x_3617_);
v_a_3695_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3690_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3690_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
else
{
lean_object* v___x_3703_; size_t v_sz_3704_; size_t v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3703_ = lean_array_fget_borrowed(v_snd_3645_, v_i_3618_);
v_sz_3704_ = lean_array_size(v___x_3641_);
v___x_3705_ = ((size_t)0ULL);
lean_inc(v___x_3641_);
v___x_3706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5(v_jumps_3616_, v_sz_3704_, v___x_3705_, v___x_3641_);
v___x_3707_ = lean_nat_add(v_i_3618_, v___x_3684_);
v___x_3708_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(v_xs_3619_, v___x_3706_, v___x_3707_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
lean_dec(v___x_3707_);
lean_dec_ref(v___x_3706_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; lean_object* v_fst_3710_; lean_object* v_snd_3711_; lean_object* v_proof_3712_; lean_object* v___x_3713_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_a_3709_);
lean_dec_ref_known(v___x_3708_, 1);
v_fst_3710_ = lean_ctor_get(v_a_3709_, 0);
lean_inc(v_fst_3710_);
v_snd_3711_ = lean_ctor_get(v_a_3709_, 1);
lean_inc(v_snd_3711_);
lean_dec(v_a_3709_);
v_proof_3712_ = lean_ctor_get(v_fst_3644_, 0);
lean_inc(v_proof_3712_);
v___x_3713_ = l_Lean_MVarId_getDecl(v_proof_3712_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v_lctx_3715_; lean_object* v_localInstances_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_a_3714_);
lean_dec_ref_known(v___x_3713_, 1);
v_lctx_3715_ = lean_ctor_get(v_a_3714_, 1);
lean_inc_ref(v_lctx_3715_);
v_localInstances_3716_ = lean_ctor_get(v_a_3714_, 4);
lean_inc_ref(v_localInstances_3716_);
lean_dec(v_a_3714_);
lean_inc(v___x_3703_);
v___x_3717_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___boxed), 14, 2);
lean_closure_set(v___x_3717_, 0, v___x_3703_);
lean_closure_set(v___x_3717_, 1, v_fst_3710_);
v___x_3718_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(v_lctx_3715_, v_localInstances_3716_, v___x_3717_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc(v_a_3719_);
lean_dec_ref_known(v___x_3718_, 1);
v_fst_3652_ = v_a_3719_;
v_snd_3653_ = v_snd_3711_;
v___y_3654_ = v___y_3623_;
v___y_3655_ = v___y_3624_;
v___y_3656_ = v___y_3625_;
v___y_3657_ = v___y_3626_;
v___y_3658_ = v___y_3627_;
v___y_3659_ = v___y_3628_;
v___y_3660_ = v___y_3629_;
v___y_3661_ = v___y_3630_;
v___y_3662_ = v___y_3631_;
v___y_3663_ = v___y_3632_;
v___y_3664_ = v___y_3633_;
goto v___jp_3651_;
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
lean_dec(v_snd_3711_);
lean_del_object(v___x_3649_);
lean_dec(v_snd_3647_);
lean_dec(v_fst_3646_);
lean_dec(v_i_3622_);
lean_dec(v___x_3617_);
v_a_3720_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3718_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3718_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
else
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3735_; 
lean_dec(v_snd_3711_);
lean_dec(v_fst_3710_);
lean_del_object(v___x_3649_);
lean_dec(v_snd_3647_);
lean_dec(v_fst_3646_);
lean_dec(v_i_3622_);
lean_dec(v___x_3617_);
v_a_3728_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3730_ = v___x_3713_;
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___x_3713_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3733_; 
if (v_isShared_3731_ == 0)
{
v___x_3733_ = v___x_3730_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
lean_del_object(v___x_3649_);
lean_dec(v_snd_3647_);
lean_dec(v_fst_3646_);
lean_dec(v_i_3622_);
lean_dec(v___x_3617_);
v_a_3736_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___x_3708_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3708_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3741_; 
if (v_isShared_3739_ == 0)
{
v___x_3741_ = v___x_3738_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
v___jp_3651_:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; size_t v_sz_3667_; size_t v___x_3668_; lean_object* v___x_3669_; 
v___x_3665_ = lean_array_push(v_fst_3646_, v_fst_3652_);
v___x_3666_ = l_Array_zip___redArg(v___x_3641_, v_snd_3653_);
lean_dec_ref(v_snd_3653_);
v_sz_3667_ = lean_array_size(v___x_3666_);
v___x_3668_ = ((size_t)0ULL);
lean_inc(v___x_3617_);
lean_inc(v_i_3622_);
v___x_3669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(v_i_3622_, v___x_3617_, v___x_3666_, v_sz_3667_, v___x_3668_, v_snd_3647_);
lean_dec_ref(v___x_3666_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v___x_3672_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_a_3670_);
lean_dec_ref_known(v___x_3669_, 1);
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 1, v_a_3670_);
lean_ctor_set(v___x_3649_, 0, v___x_3665_);
v___x_3672_ = v___x_3649_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3665_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v_a_3670_);
v___x_3672_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
lean_object* v___x_3673_; 
v___x_3673_ = lean_nat_add(v_i_3622_, v_step_3636_);
lean_dec(v_i_3622_);
v_b_3621_ = v___x_3672_;
v_i_3622_ = v___x_3673_;
goto _start;
}
}
else
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
lean_dec_ref(v___x_3665_);
lean_del_object(v___x_3649_);
lean_dec(v_i_3622_);
lean_dec(v___x_3617_);
v_a_3676_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3678_ = v___x_3669_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3669_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3676_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg(lean_object* v___x_3745_, lean_object* v___x_3746_, lean_object* v_jumps_3747_, lean_object* v_xs_3748_, lean_object* v_i_3749_, lean_object* v_range_3750_, lean_object* v_b_3751_, lean_object* v_i_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
lean_object* v_stop_3765_; lean_object* v_step_3766_; uint8_t v___x_3767_; 
v_stop_3765_ = lean_ctor_get(v_range_3750_, 1);
v_step_3766_ = lean_ctor_get(v_range_3750_, 2);
v___x_3767_ = lean_nat_dec_lt(v_i_3752_, v_stop_3765_);
if (v___x_3767_ == 0)
{
lean_object* v___x_3768_; 
lean_dec(v_i_3752_);
lean_dec(v___x_3745_);
v___x_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3768_, 0, v_b_3751_);
return v___x_3768_;
}
else
{
lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v_fst_3774_; lean_object* v_snd_3775_; lean_object* v_fst_3776_; lean_object* v_snd_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3875_; 
v___x_3769_ = lean_unsigned_to_nat(0u);
v___x_3770_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1);
v___x_3771_ = lean_array_fget_borrowed(v___x_3746_, v_i_3752_);
v___x_3772_ = lean_array_get_borrowed(v___x_3769_, v___x_3771_, v___x_3769_);
v___x_3773_ = lean_array_get_borrowed(v___x_3770_, v_jumps_3747_, v___x_3772_);
v_fst_3774_ = lean_ctor_get(v___x_3773_, 0);
v_snd_3775_ = lean_ctor_get(v___x_3773_, 1);
v_fst_3776_ = lean_ctor_get(v_b_3751_, 0);
v_snd_3777_ = lean_ctor_get(v_b_3751_, 1);
v_isSharedCheck_3875_ = !lean_is_exclusive(v_b_3751_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3779_ = v_b_3751_;
v_isShared_3780_ = v_isSharedCheck_3875_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_snd_3777_);
lean_inc(v_fst_3776_);
lean_dec(v_b_3751_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3875_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v_fst_3782_; lean_object* v_snd_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___x_3814_; lean_object* v___x_3815_; uint8_t v___x_3816_; 
v___x_3814_ = lean_unsigned_to_nat(1u);
v___x_3815_ = lean_array_get_size(v_snd_3775_);
v___x_3816_ = lean_nat_dec_lt(v_i_3749_, v___x_3815_);
if (v___x_3816_ == 0)
{
lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
v___x_3817_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__0));
v___x_3818_ = lean_array_get_size(v_xs_3748_);
v___x_3819_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3769_);
lean_ctor_set(v___x_3819_, 1, v___x_3818_);
lean_ctor_set(v___x_3819_, 2, v___x_3814_);
v___x_3820_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(v_xs_3748_, v_fst_3774_, v___x_3819_, v___x_3817_, v___x_3769_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
lean_dec_ref_known(v___x_3819_, 3);
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v_a_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
v_a_3821_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_a_3821_);
lean_dec_ref_known(v___x_3820_, 1);
v___x_3822_ = lean_array_to_list(v_a_3821_);
v___x_3823_ = l_Lean_mkAndN(v___x_3822_);
v___x_3824_ = lean_mk_empty_array_with_capacity(v___x_3814_);
lean_dec_ref(v___x_3824_);
v___x_3825_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__1));
v_fst_3782_ = v___x_3823_;
v_snd_3783_ = v___x_3825_;
v___y_3784_ = v___y_3753_;
v___y_3785_ = v___y_3754_;
v___y_3786_ = v___y_3755_;
v___y_3787_ = v___y_3756_;
v___y_3788_ = v___y_3757_;
v___y_3789_ = v___y_3758_;
v___y_3790_ = v___y_3759_;
v___y_3791_ = v___y_3760_;
v___y_3792_ = v___y_3761_;
v___y_3793_ = v___y_3762_;
v___y_3794_ = v___y_3763_;
goto v___jp_3781_;
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_del_object(v___x_3779_);
lean_dec(v_snd_3777_);
lean_dec(v_fst_3776_);
lean_dec(v_i_3752_);
lean_dec(v___x_3745_);
v_a_3826_ = lean_ctor_get(v___x_3820_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3820_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3820_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3820_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
else
{
lean_object* v___x_3834_; size_t v_sz_3835_; size_t v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3834_ = lean_array_fget_borrowed(v_snd_3775_, v_i_3749_);
v_sz_3835_ = lean_array_size(v___x_3771_);
v___x_3836_ = ((size_t)0ULL);
lean_inc(v___x_3771_);
v___x_3837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5(v_jumps_3747_, v_sz_3835_, v___x_3836_, v___x_3771_);
v___x_3838_ = lean_nat_add(v_i_3749_, v___x_3814_);
v___x_3839_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(v_xs_3748_, v___x_3837_, v___x_3838_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
lean_dec(v___x_3838_);
lean_dec_ref(v___x_3837_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; lean_object* v_fst_3841_; lean_object* v_snd_3842_; lean_object* v_proof_3843_; lean_object* v___x_3844_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_a_3840_);
lean_dec_ref_known(v___x_3839_, 1);
v_fst_3841_ = lean_ctor_get(v_a_3840_, 0);
lean_inc(v_fst_3841_);
v_snd_3842_ = lean_ctor_get(v_a_3840_, 1);
lean_inc(v_snd_3842_);
lean_dec(v_a_3840_);
v_proof_3843_ = lean_ctor_get(v_fst_3774_, 0);
lean_inc(v_proof_3843_);
v___x_3844_ = l_Lean_MVarId_getDecl(v_proof_3843_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; lean_object* v_lctx_3846_; lean_object* v_localInstances_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref_known(v___x_3844_, 1);
v_lctx_3846_ = lean_ctor_get(v_a_3845_, 1);
lean_inc_ref(v_lctx_3846_);
v_localInstances_3847_ = lean_ctor_get(v_a_3845_, 4);
lean_inc_ref(v_localInstances_3847_);
lean_dec(v_a_3845_);
lean_inc(v___x_3834_);
v___x_3848_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___boxed), 14, 2);
lean_closure_set(v___x_3848_, 0, v___x_3834_);
lean_closure_set(v___x_3848_, 1, v_fst_3841_);
v___x_3849_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(v_lctx_3846_, v_localInstances_3847_, v___x_3848_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3850_);
lean_dec_ref_known(v___x_3849_, 1);
v_fst_3782_ = v_a_3850_;
v_snd_3783_ = v_snd_3842_;
v___y_3784_ = v___y_3753_;
v___y_3785_ = v___y_3754_;
v___y_3786_ = v___y_3755_;
v___y_3787_ = v___y_3756_;
v___y_3788_ = v___y_3757_;
v___y_3789_ = v___y_3758_;
v___y_3790_ = v___y_3759_;
v___y_3791_ = v___y_3760_;
v___y_3792_ = v___y_3761_;
v___y_3793_ = v___y_3762_;
v___y_3794_ = v___y_3763_;
goto v___jp_3781_;
}
else
{
lean_object* v_a_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3858_; 
lean_dec(v_snd_3842_);
lean_del_object(v___x_3779_);
lean_dec(v_snd_3777_);
lean_dec(v_fst_3776_);
lean_dec(v_i_3752_);
lean_dec(v___x_3745_);
v_a_3851_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3853_ = v___x_3849_;
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_a_3851_);
lean_dec(v___x_3849_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
if (v_isShared_3854_ == 0)
{
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3851_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
}
else
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3866_; 
lean_dec(v_snd_3842_);
lean_dec(v_fst_3841_);
lean_del_object(v___x_3779_);
lean_dec(v_snd_3777_);
lean_dec(v_fst_3776_);
lean_dec(v_i_3752_);
lean_dec(v___x_3745_);
v_a_3859_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3861_ = v___x_3844_;
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3844_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3864_; 
if (v_isShared_3862_ == 0)
{
v___x_3864_ = v___x_3861_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3859_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
else
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3874_; 
lean_del_object(v___x_3779_);
lean_dec(v_snd_3777_);
lean_dec(v_fst_3776_);
lean_dec(v_i_3752_);
lean_dec(v___x_3745_);
v_a_3867_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3869_ = v___x_3839_;
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3839_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
if (v_isShared_3870_ == 0)
{
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3867_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
v___jp_3781_:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; size_t v_sz_3797_; size_t v___x_3798_; lean_object* v___x_3799_; 
v___x_3795_ = lean_array_push(v_fst_3776_, v_fst_3782_);
v___x_3796_ = l_Array_zip___redArg(v___x_3771_, v_snd_3783_);
lean_dec_ref(v_snd_3783_);
v_sz_3797_ = lean_array_size(v___x_3796_);
v___x_3798_ = ((size_t)0ULL);
lean_inc(v___x_3745_);
lean_inc(v_i_3752_);
v___x_3799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(v_i_3752_, v___x_3745_, v___x_3796_, v_sz_3797_, v___x_3798_, v_snd_3777_);
lean_dec_ref(v___x_3796_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3802_; 
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
lean_inc(v_a_3800_);
lean_dec_ref_known(v___x_3799_, 1);
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 1, v_a_3800_);
lean_ctor_set(v___x_3779_, 0, v___x_3795_);
v___x_3802_ = v___x_3779_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v___x_3795_);
lean_ctor_set(v_reuseFailAlloc_3805_, 1, v_a_3800_);
v___x_3802_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3803_ = lean_nat_add(v_i_3752_, v_step_3766_);
lean_dec(v_i_3752_);
v___x_3804_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg(v___x_3746_, v_jumps_3747_, v___x_3745_, v_i_3749_, v_xs_3748_, v_range_3750_, v___x_3802_, v___x_3803_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
return v___x_3804_;
}
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_dec_ref(v___x_3795_);
lean_del_object(v___x_3779_);
lean_dec(v_i_3752_);
lean_dec(v___x_3745_);
v_a_3806_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3799_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3799_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(lean_object* v_xs_3876_, lean_object* v_jumps_3877_, lean_object* v_i_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v___x_3891_; lean_object* v_groups_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3891_ = lean_unsigned_to_nat(0u);
v_groups_3892_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__0));
v___x_3893_ = lean_array_get_size(v_jumps_3877_);
v___x_3894_ = lean_unsigned_to_nat(1u);
v___x_3895_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3891_);
lean_ctor_set(v___x_3895_, 1, v___x_3893_);
lean_ctor_set(v___x_3895_, 2, v___x_3894_);
v___x_3896_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__3, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__3);
v___x_3897_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg(v_jumps_3877_, v_i_3878_, v___x_3895_, v___x_3896_, v___x_3891_);
lean_dec_ref_known(v___x_3895_, 3);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; lean_object* v_fst_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3938_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3898_);
lean_dec_ref_known(v___x_3897_, 1);
v_fst_3899_ = lean_ctor_get(v_a_3898_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v_a_3898_);
if (v_isSharedCheck_3938_ == 0)
{
lean_object* v_unused_3939_; 
v_unused_3939_ = lean_ctor_get(v_a_3898_, 1);
lean_dec(v_unused_3939_);
v___x_3901_ = v_a_3898_;
v_isShared_3902_ = v_isSharedCheck_3938_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_fst_3899_);
lean_dec(v_a_3898_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3938_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3908_; 
v___x_3903_ = lean_box(0);
v___x_3904_ = lean_mk_array(v___x_3893_, v___x_3903_);
v___x_3905_ = lean_array_get_size(v_fst_3899_);
v___x_3906_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3891_);
lean_ctor_set(v___x_3906_, 1, v___x_3905_);
lean_ctor_set(v___x_3906_, 2, v___x_3894_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 1, v___x_3904_);
lean_ctor_set(v___x_3901_, 0, v_groups_3892_);
v___x_3908_ = v___x_3901_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_groups_3892_);
lean_ctor_set(v_reuseFailAlloc_3937_, 1, v___x_3904_);
v___x_3908_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
lean_object* v___x_3909_; 
v___x_3909_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg(v___x_3905_, v_fst_3899_, v_jumps_3877_, v_xs_3876_, v_i_3878_, v___x_3906_, v___x_3908_, v___x_3891_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_);
lean_dec_ref_known(v___x_3906_, 3);
lean_dec(v_fst_3899_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3928_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3912_ = v___x_3909_;
v_isShared_3913_ = v_isSharedCheck_3928_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3909_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3928_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v_fst_3914_; lean_object* v_snd_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3927_; 
v_fst_3914_ = lean_ctor_get(v_a_3910_, 0);
v_snd_3915_ = lean_ctor_get(v_a_3910_, 1);
v_isSharedCheck_3927_ = !lean_is_exclusive(v_a_3910_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3917_ = v_a_3910_;
v_isShared_3918_ = v_isSharedCheck_3927_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_snd_3915_);
lean_inc(v_fst_3914_);
lean_dec(v_a_3910_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3927_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3922_; 
v___x_3919_ = lean_array_get_size(v_fst_3914_);
v___x_3920_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(v_fst_3914_, v___x_3891_, v___x_3919_);
lean_dec(v_fst_3914_);
if (v_isShared_3918_ == 0)
{
lean_ctor_set(v___x_3917_, 0, v___x_3920_);
v___x_3922_ = v___x_3917_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3920_);
lean_ctor_set(v_reuseFailAlloc_3926_, 1, v_snd_3915_);
v___x_3922_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
lean_object* v___x_3924_; 
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 0, v___x_3922_);
v___x_3924_ = v___x_3912_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3922_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
}
else
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3936_; 
v_a_3929_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3931_ = v___x_3909_;
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3909_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3932_ == 0)
{
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
}
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
v_a_3940_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v___x_3897_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3897_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___boxed(lean_object* v_xs_3948_, lean_object* v_jumps_3949_, lean_object* v_i_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_){
_start:
{
lean_object* v_res_3963_; 
v_res_3963_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(v_xs_3948_, v_jumps_3949_, v_i_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_);
lean_dec(v_a_3961_);
lean_dec_ref(v_a_3960_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
lean_dec(v_a_3955_);
lean_dec_ref(v_a_3954_);
lean_dec(v_a_3953_);
lean_dec(v_a_3952_);
lean_dec_ref(v_a_3951_);
lean_dec(v_i_3950_);
lean_dec_ref(v_jumps_3949_);
lean_dec_ref(v_xs_3948_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___boxed(lean_object** _args){
lean_object* v___x_3964_ = _args[0];
lean_object* v_jumps_3965_ = _args[1];
lean_object* v___x_3966_ = _args[2];
lean_object* v_i_3967_ = _args[3];
lean_object* v_xs_3968_ = _args[4];
lean_object* v_range_3969_ = _args[5];
lean_object* v_b_3970_ = _args[6];
lean_object* v_i_3971_ = _args[7];
lean_object* v___y_3972_ = _args[8];
lean_object* v___y_3973_ = _args[9];
lean_object* v___y_3974_ = _args[10];
lean_object* v___y_3975_ = _args[11];
lean_object* v___y_3976_ = _args[12];
lean_object* v___y_3977_ = _args[13];
lean_object* v___y_3978_ = _args[14];
lean_object* v___y_3979_ = _args[15];
lean_object* v___y_3980_ = _args[16];
lean_object* v___y_3981_ = _args[17];
lean_object* v___y_3982_ = _args[18];
lean_object* v___y_3983_ = _args[19];
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg(v___x_3964_, v_jumps_3965_, v___x_3966_, v_i_3967_, v_xs_3968_, v_range_3969_, v_b_3970_, v_i_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec_ref(v_range_3969_);
lean_dec_ref(v_xs_3968_);
lean_dec(v_i_3967_);
lean_dec_ref(v_jumps_3965_);
lean_dec_ref(v___x_3964_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg___boxed(lean_object** _args){
lean_object* v___x_3985_ = _args[0];
lean_object* v___x_3986_ = _args[1];
lean_object* v_jumps_3987_ = _args[2];
lean_object* v_xs_3988_ = _args[3];
lean_object* v_i_3989_ = _args[4];
lean_object* v_range_3990_ = _args[5];
lean_object* v_b_3991_ = _args[6];
lean_object* v_i_3992_ = _args[7];
lean_object* v___y_3993_ = _args[8];
lean_object* v___y_3994_ = _args[9];
lean_object* v___y_3995_ = _args[10];
lean_object* v___y_3996_ = _args[11];
lean_object* v___y_3997_ = _args[12];
lean_object* v___y_3998_ = _args[13];
lean_object* v___y_3999_ = _args[14];
lean_object* v___y_4000_ = _args[15];
lean_object* v___y_4001_ = _args[16];
lean_object* v___y_4002_ = _args[17];
lean_object* v___y_4003_ = _args[18];
lean_object* v___y_4004_ = _args[19];
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg(v___x_3985_, v___x_3986_, v_jumps_3987_, v_xs_3988_, v_i_3989_, v_range_3990_, v_b_3991_, v_i_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
lean_dec(v___y_4003_);
lean_dec_ref(v___y_4002_);
lean_dec(v___y_4001_);
lean_dec_ref(v___y_4000_);
lean_dec(v___y_3999_);
lean_dec_ref(v___y_3998_);
lean_dec(v___y_3997_);
lean_dec_ref(v___y_3996_);
lean_dec(v___y_3995_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec_ref(v_range_3990_);
lean_dec(v_i_3989_);
lean_dec_ref(v_xs_3988_);
lean_dec_ref(v_jumps_3987_);
lean_dec_ref(v___x_3986_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0(lean_object* v_00_u03b2_4006_, lean_object* v_m_4007_, lean_object* v_a_4008_){
_start:
{
lean_object* v___x_4009_; 
v___x_4009_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg(v_m_4007_, v_a_4008_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___boxed(lean_object* v_00_u03b2_4010_, lean_object* v_m_4011_, lean_object* v_a_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0(v_00_u03b2_4010_, v_m_4011_, v_a_4012_);
lean_dec(v_a_4012_);
lean_dec_ref(v_m_4011_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1(lean_object* v_00_u03b2_4014_, lean_object* v_m_4015_, lean_object* v_a_4016_, lean_object* v_b_4017_){
_start:
{
lean_object* v___x_4018_; 
v___x_4018_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1___redArg(v_m_4015_, v_a_4016_, v_b_4017_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2(lean_object* v_jumps_4019_, lean_object* v_i_4020_, lean_object* v_range_4021_, lean_object* v_b_4022_, lean_object* v_i_4023_, lean_object* v_hs_4024_, lean_object* v_hl_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_){
_start:
{
lean_object* v___x_4038_; 
v___x_4038_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg(v_jumps_4019_, v_i_4020_, v_range_4021_, v_b_4022_, v_i_4023_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___boxed(lean_object** _args){
lean_object* v_jumps_4039_ = _args[0];
lean_object* v_i_4040_ = _args[1];
lean_object* v_range_4041_ = _args[2];
lean_object* v_b_4042_ = _args[3];
lean_object* v_i_4043_ = _args[4];
lean_object* v_hs_4044_ = _args[5];
lean_object* v_hl_4045_ = _args[6];
lean_object* v___y_4046_ = _args[7];
lean_object* v___y_4047_ = _args[8];
lean_object* v___y_4048_ = _args[9];
lean_object* v___y_4049_ = _args[10];
lean_object* v___y_4050_ = _args[11];
lean_object* v___y_4051_ = _args[12];
lean_object* v___y_4052_ = _args[13];
lean_object* v___y_4053_ = _args[14];
lean_object* v___y_4054_ = _args[15];
lean_object* v___y_4055_ = _args[16];
lean_object* v___y_4056_ = _args[17];
lean_object* v___y_4057_ = _args[18];
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2(v_jumps_4039_, v_i_4040_, v_range_4041_, v_b_4042_, v_i_4043_, v_hs_4044_, v_hl_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
lean_dec(v___y_4056_);
lean_dec_ref(v___y_4055_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
lean_dec_ref(v_range_4041_);
lean_dec(v_i_4040_);
lean_dec_ref(v_jumps_4039_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3(lean_object* v_g_4059_, lean_object* v___x_4060_, lean_object* v_as_4061_, size_t v_sz_4062_, size_t v_i_4063_, lean_object* v_b_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
lean_object* v___x_4077_; 
v___x_4077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(v_g_4059_, v___x_4060_, v_as_4061_, v_sz_4062_, v_i_4063_, v_b_4064_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___boxed(lean_object** _args){
lean_object* v_g_4078_ = _args[0];
lean_object* v___x_4079_ = _args[1];
lean_object* v_as_4080_ = _args[2];
lean_object* v_sz_4081_ = _args[3];
lean_object* v_i_4082_ = _args[4];
lean_object* v_b_4083_ = _args[5];
lean_object* v___y_4084_ = _args[6];
lean_object* v___y_4085_ = _args[7];
lean_object* v___y_4086_ = _args[8];
lean_object* v___y_4087_ = _args[9];
lean_object* v___y_4088_ = _args[10];
lean_object* v___y_4089_ = _args[11];
lean_object* v___y_4090_ = _args[12];
lean_object* v___y_4091_ = _args[13];
lean_object* v___y_4092_ = _args[14];
lean_object* v___y_4093_ = _args[15];
lean_object* v___y_4094_ = _args[16];
lean_object* v___y_4095_ = _args[17];
_start:
{
size_t v_sz_boxed_4096_; size_t v_i_boxed_4097_; lean_object* v_res_4098_; 
v_sz_boxed_4096_ = lean_unbox_usize(v_sz_4081_);
lean_dec(v_sz_4081_);
v_i_boxed_4097_ = lean_unbox_usize(v_i_4082_);
lean_dec(v_i_4082_);
v_res_4098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3(v_g_4078_, v___x_4079_, v_as_4080_, v_sz_boxed_4096_, v_i_boxed_4097_, v_b_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec(v___y_4086_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec_ref(v_as_4080_);
return v_res_4098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4(lean_object* v_xs_4099_, lean_object* v_fst_4100_, lean_object* v_range_4101_, lean_object* v_b_4102_, lean_object* v_i_4103_, lean_object* v_hs_4104_, lean_object* v_hl_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
lean_object* v___x_4118_; 
v___x_4118_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(v_xs_4099_, v_fst_4100_, v_range_4101_, v_b_4102_, v_i_4103_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
return v___x_4118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___boxed(lean_object** _args){
lean_object* v_xs_4119_ = _args[0];
lean_object* v_fst_4120_ = _args[1];
lean_object* v_range_4121_ = _args[2];
lean_object* v_b_4122_ = _args[3];
lean_object* v_i_4123_ = _args[4];
lean_object* v_hs_4124_ = _args[5];
lean_object* v_hl_4125_ = _args[6];
lean_object* v___y_4126_ = _args[7];
lean_object* v___y_4127_ = _args[8];
lean_object* v___y_4128_ = _args[9];
lean_object* v___y_4129_ = _args[10];
lean_object* v___y_4130_ = _args[11];
lean_object* v___y_4131_ = _args[12];
lean_object* v___y_4132_ = _args[13];
lean_object* v___y_4133_ = _args[14];
lean_object* v___y_4134_ = _args[15];
lean_object* v___y_4135_ = _args[16];
lean_object* v___y_4136_ = _args[17];
lean_object* v___y_4137_ = _args[18];
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4(v_xs_4119_, v_fst_4120_, v_range_4121_, v_b_4122_, v_i_4123_, v_hs_4124_, v_hl_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec_ref(v_range_4121_);
lean_dec_ref(v_fst_4120_);
lean_dec_ref(v_xs_4119_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7(lean_object* v___x_4139_, lean_object* v___x_4140_, lean_object* v_jumps_4141_, lean_object* v_xs_4142_, lean_object* v_i_4143_, lean_object* v_range_4144_, lean_object* v_b_4145_, lean_object* v_i_4146_, lean_object* v_hs_4147_, lean_object* v_hl_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v___x_4161_; 
v___x_4161_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg(v___x_4139_, v___x_4140_, v_jumps_4141_, v_xs_4142_, v_i_4143_, v_range_4144_, v_b_4145_, v_i_4146_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___boxed(lean_object** _args){
lean_object* v___x_4162_ = _args[0];
lean_object* v___x_4163_ = _args[1];
lean_object* v_jumps_4164_ = _args[2];
lean_object* v_xs_4165_ = _args[3];
lean_object* v_i_4166_ = _args[4];
lean_object* v_range_4167_ = _args[5];
lean_object* v_b_4168_ = _args[6];
lean_object* v_i_4169_ = _args[7];
lean_object* v_hs_4170_ = _args[8];
lean_object* v_hl_4171_ = _args[9];
lean_object* v___y_4172_ = _args[10];
lean_object* v___y_4173_ = _args[11];
lean_object* v___y_4174_ = _args[12];
lean_object* v___y_4175_ = _args[13];
lean_object* v___y_4176_ = _args[14];
lean_object* v___y_4177_ = _args[15];
lean_object* v___y_4178_ = _args[16];
lean_object* v___y_4179_ = _args[17];
lean_object* v___y_4180_ = _args[18];
lean_object* v___y_4181_ = _args[19];
lean_object* v___y_4182_ = _args[20];
lean_object* v___y_4183_ = _args[21];
_start:
{
lean_object* v_res_4184_; 
v_res_4184_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7(v___x_4162_, v___x_4163_, v_jumps_4164_, v_xs_4165_, v_i_4166_, v_range_4167_, v_b_4168_, v_i_4169_, v_hs_4170_, v_hl_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_);
lean_dec(v___y_4182_);
lean_dec_ref(v___y_4181_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4179_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec_ref(v_range_4167_);
lean_dec(v_i_4166_);
lean_dec_ref(v_xs_4165_);
lean_dec_ref(v_jumps_4164_);
lean_dec_ref(v___x_4163_);
return v_res_4184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0(lean_object* v_00_u03b2_4185_, lean_object* v_a_4186_, lean_object* v_x_4187_){
_start:
{
lean_object* v___x_4188_; 
v___x_4188_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg(v_a_4186_, v_x_4187_);
return v___x_4188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4189_, lean_object* v_a_4190_, lean_object* v_x_4191_){
_start:
{
lean_object* v_res_4192_; 
v_res_4192_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0(v_00_u03b2_4189_, v_a_4190_, v_x_4191_);
lean_dec(v_x_4191_);
lean_dec(v_a_4190_);
return v_res_4192_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2(lean_object* v_00_u03b2_4193_, lean_object* v_a_4194_, lean_object* v_x_4195_){
_start:
{
uint8_t v___x_4196_; 
v___x_4196_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg(v_a_4194_, v_x_4195_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4197_, lean_object* v_a_4198_, lean_object* v_x_4199_){
_start:
{
uint8_t v_res_4200_; lean_object* v_r_4201_; 
v_res_4200_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2(v_00_u03b2_4197_, v_a_4198_, v_x_4199_);
lean_dec(v_x_4199_);
lean_dec(v_a_4198_);
v_r_4201_ = lean_box(v_res_4200_);
return v_r_4201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3(lean_object* v_00_u03b2_4202_, lean_object* v_data_4203_){
_start:
{
lean_object* v___x_4204_; 
v___x_4204_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3___redArg(v_data_4203_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4(lean_object* v_00_u03b2_4205_, lean_object* v_a_4206_, lean_object* v_b_4207_, lean_object* v_x_4208_){
_start:
{
lean_object* v___x_4209_; 
v___x_4209_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4___redArg(v_a_4206_, v_b_4207_, v_x_4208_);
return v___x_4209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11(lean_object* v___x_4210_, lean_object* v_jumps_4211_, lean_object* v___x_4212_, lean_object* v_i_4213_, lean_object* v_xs_4214_, lean_object* v_range_4215_, lean_object* v_b_4216_, lean_object* v_i_4217_, lean_object* v_hs_4218_, lean_object* v_hl_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_){
_start:
{
lean_object* v___x_4232_; 
v___x_4232_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg(v___x_4210_, v_jumps_4211_, v___x_4212_, v_i_4213_, v_xs_4214_, v_range_4215_, v_b_4216_, v_i_4217_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___boxed(lean_object** _args){
lean_object* v___x_4233_ = _args[0];
lean_object* v_jumps_4234_ = _args[1];
lean_object* v___x_4235_ = _args[2];
lean_object* v_i_4236_ = _args[3];
lean_object* v_xs_4237_ = _args[4];
lean_object* v_range_4238_ = _args[5];
lean_object* v_b_4239_ = _args[6];
lean_object* v_i_4240_ = _args[7];
lean_object* v_hs_4241_ = _args[8];
lean_object* v_hl_4242_ = _args[9];
lean_object* v___y_4243_ = _args[10];
lean_object* v___y_4244_ = _args[11];
lean_object* v___y_4245_ = _args[12];
lean_object* v___y_4246_ = _args[13];
lean_object* v___y_4247_ = _args[14];
lean_object* v___y_4248_ = _args[15];
lean_object* v___y_4249_ = _args[16];
lean_object* v___y_4250_ = _args[17];
lean_object* v___y_4251_ = _args[18];
lean_object* v___y_4252_ = _args[19];
lean_object* v___y_4253_ = _args[20];
lean_object* v___y_4254_ = _args[21];
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11(v___x_4233_, v_jumps_4234_, v___x_4235_, v_i_4236_, v_xs_4237_, v_range_4238_, v_b_4239_, v_i_4240_, v_hs_4241_, v_hl_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec(v___y_4244_);
lean_dec_ref(v___y_4243_);
lean_dec_ref(v_range_4238_);
lean_dec_ref(v_xs_4237_);
lean_dec(v_i_4236_);
lean_dec_ref(v_jumps_4234_);
lean_dec_ref(v___x_4233_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_4256_, lean_object* v_i_4257_, lean_object* v_source_4258_, lean_object* v_target_4259_){
_start:
{
lean_object* v___x_4260_; 
v___x_4260_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5___redArg(v_i_4257_, v_source_4258_, v_target_4259_);
return v___x_4260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_4261_, lean_object* v_x_4262_, lean_object* v_x_4263_){
_start:
{
lean_object* v___x_4264_; 
v___x_4264_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5_spec__11___redArg(v_x_4262_, v_x_4263_);
return v___x_4264_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__1(void){
_start:
{
lean_object* v___x_4266_; lean_object* v___x_4267_; 
v___x_4266_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__0));
v___x_4267_ = l_Lean_stringToMessageData(v___x_4266_);
return v___x_4267_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10(void){
_start:
{
lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4282_ = lean_box(0);
v___x_4283_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__9));
v___x_4284_ = l_Lean_mkConst(v___x_4283_, v___x_4282_);
return v___x_4284_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__12(void){
_start:
{
lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___x_4288_ = lean_box(0);
v___x_4289_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__11));
v___x_4290_ = l_Lean_mkConst(v___x_4289_, v___x_4288_);
return v___x_4290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(lean_object* v_00_u03c6_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_){
_start:
{
lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___x_4306_; 
lean_inc_ref(v_00_u03c6_4291_);
v___x_4306_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_00_u03c6_4291_, v_a_4293_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4352_; 
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4352_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4352_ == 0)
{
v___x_4309_ = v___x_4306_;
v_isShared_4310_ = v_isSharedCheck_4352_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v___x_4306_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4352_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4311_; lean_object* v___x_4312_; uint8_t v___x_4313_; 
v___x_4311_ = l_Lean_Expr_cleanupAnnotations(v_a_4307_);
lean_dec(v_a_4307_);
v___x_4312_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__3));
v___x_4313_ = l_Lean_Expr_isConstOf(v___x_4311_, v___x_4312_);
if (v___x_4313_ == 0)
{
uint8_t v___x_4314_; 
v___x_4314_ = l_Lean_Expr_isApp(v___x_4311_);
if (v___x_4314_ == 0)
{
lean_dec_ref(v___x_4311_);
lean_del_object(v___x_4309_);
v___y_4298_ = v_a_4292_;
v___y_4299_ = v_a_4293_;
v___y_4300_ = v_a_4294_;
v___y_4301_ = v_a_4295_;
goto v___jp_4297_;
}
else
{
lean_object* v___x_4315_; uint8_t v___x_4316_; 
v___x_4315_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4311_);
v___x_4316_ = l_Lean_Expr_isApp(v___x_4315_);
if (v___x_4316_ == 0)
{
lean_dec_ref(v___x_4315_);
lean_dec_ref(v___x_4311_);
lean_del_object(v___x_4309_);
v___y_4298_ = v_a_4292_;
v___y_4299_ = v_a_4293_;
v___y_4300_ = v_a_4294_;
v___y_4301_ = v_a_4295_;
goto v___jp_4297_;
}
else
{
lean_object* v_arg_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; uint8_t v___x_4320_; 
v_arg_4317_ = lean_ctor_get(v___x_4315_, 1);
lean_inc_ref(v_arg_4317_);
v___x_4318_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4315_);
lean_dec_ref(v___x_4315_);
v___x_4319_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__5));
v___x_4320_ = l_Lean_Expr_isConstOf(v___x_4318_, v___x_4319_);
if (v___x_4320_ == 0)
{
uint8_t v___x_4321_; 
lean_dec_ref(v___x_4311_);
v___x_4321_ = l_Lean_Expr_isApp(v___x_4318_);
if (v___x_4321_ == 0)
{
lean_dec_ref(v___x_4318_);
lean_dec_ref(v_arg_4317_);
lean_del_object(v___x_4309_);
v___y_4298_ = v_a_4292_;
v___y_4299_ = v_a_4293_;
v___y_4300_ = v_a_4294_;
v___y_4301_ = v_a_4295_;
goto v___jp_4297_;
}
else
{
lean_object* v___x_4322_; lean_object* v___x_4323_; uint8_t v___x_4324_; 
v___x_4322_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4318_);
v___x_4323_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__3));
v___x_4324_ = l_Lean_Expr_isConstOf(v___x_4322_, v___x_4323_);
lean_dec_ref(v___x_4322_);
if (v___x_4324_ == 0)
{
lean_dec_ref(v___x_4318_);
lean_dec_ref(v_arg_4317_);
lean_del_object(v___x_4309_);
v___y_4298_ = v_a_4292_;
v___y_4299_ = v_a_4293_;
v___y_4300_ = v_a_4294_;
v___y_4301_ = v_a_4295_;
goto v___jp_4297_;
}
else
{
lean_object* v_arg_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4332_; 
v_arg_4325_ = lean_ctor_get(v___x_4318_, 1);
lean_inc_ref(v_arg_4325_);
lean_dec_ref(v___x_4318_);
v___x_4326_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__7));
v___x_4327_ = l_Lean_Expr_getAppFn(v_00_u03c6_4291_);
lean_dec_ref(v_00_u03c6_4291_);
v___x_4328_ = l_Lean_Expr_constLevels_x21(v___x_4327_);
lean_dec_ref(v___x_4327_);
v___x_4329_ = l_Lean_mkConst(v___x_4326_, v___x_4328_);
v___x_4330_ = l_Lean_mkAppB(v___x_4329_, v_arg_4325_, v_arg_4317_);
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 0, v___x_4330_);
v___x_4332_ = v___x_4309_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v___x_4330_);
v___x_4332_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
return v___x_4332_;
}
}
}
}
else
{
lean_object* v_arg_4334_; lean_object* v___x_4335_; 
lean_dec_ref(v___x_4318_);
lean_del_object(v___x_4309_);
lean_dec_ref(v_00_u03c6_4291_);
v_arg_4334_ = lean_ctor_get(v___x_4311_, 1);
lean_inc_ref(v_arg_4334_);
lean_dec_ref(v___x_4311_);
lean_inc_ref(v_arg_4317_);
v___x_4335_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(v_arg_4317_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_);
if (lean_obj_tag(v___x_4335_) == 0)
{
lean_object* v_a_4336_; lean_object* v___x_4337_; 
v_a_4336_ = lean_ctor_get(v___x_4335_, 0);
lean_inc(v_a_4336_);
lean_dec_ref_known(v___x_4335_, 1);
lean_inc_ref(v_arg_4334_);
v___x_4337_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(v_arg_4334_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_);
if (lean_obj_tag(v___x_4337_) == 0)
{
lean_object* v_a_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4347_; 
v_a_4338_ = lean_ctor_get(v___x_4337_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4337_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4340_ = v___x_4337_;
v_isShared_4341_ = v_isSharedCheck_4347_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_a_4338_);
lean_dec(v___x_4337_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4347_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4345_; 
v___x_4342_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10);
v___x_4343_ = l_Lean_mkApp4(v___x_4342_, v_arg_4317_, v_arg_4334_, v_a_4336_, v_a_4338_);
if (v_isShared_4341_ == 0)
{
lean_ctor_set(v___x_4340_, 0, v___x_4343_);
v___x_4345_ = v___x_4340_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v___x_4343_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
}
else
{
lean_dec(v_a_4336_);
lean_dec_ref(v_arg_4334_);
lean_dec_ref(v_arg_4317_);
return v___x_4337_;
}
}
else
{
lean_dec_ref(v_arg_4334_);
lean_dec_ref(v_arg_4317_);
return v___x_4335_;
}
}
}
}
}
else
{
lean_object* v___x_4348_; lean_object* v___x_4350_; 
lean_dec_ref(v___x_4311_);
lean_dec_ref(v_00_u03c6_4291_);
v___x_4348_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__12, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__12_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__12);
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 0, v___x_4348_);
v___x_4350_ = v___x_4309_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v___x_4348_);
v___x_4350_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
return v___x_4350_;
}
}
}
}
else
{
lean_dec_ref(v_00_u03c6_4291_);
return v___x_4306_;
}
v___jp_4297_:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
v___x_4302_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__1, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__1);
v___x_4303_ = l_Lean_indentExpr(v_00_u03c6_4291_);
v___x_4304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4302_);
lean_ctor_set(v___x_4304_, 1, v___x_4303_);
v___x_4305_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v___x_4304_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_);
return v___x_4305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___boxed(lean_object* v_00_u03c6_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(v_00_u03c6_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
lean_dec(v_a_4357_);
lean_dec_ref(v_a_4356_);
lean_dec(v_a_4355_);
lean_dec_ref(v_a_4354_);
return v_res_4359_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__1(void){
_start:
{
lean_object* v___x_4361_; lean_object* v___x_4362_; 
v___x_4361_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__0));
v___x_4362_ = l_Lean_stringToMessageData(v___x_4361_);
return v___x_4362_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4364_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__0));
v___x_4365_ = l_Lean_stringToMessageData(v___x_4364_);
return v___x_4365_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4370_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__3));
v___x_4371_ = l_Lean_stringToMessageData(v___x_4370_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0(lean_object* v_tail_4372_, lean_object* v_locals_4373_, lean_object* v_00_u03c6_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4384_; uint8_t v___x_4389_; 
v___x_4389_ = l_List_isEmpty___redArg(v_tail_4372_);
if (v___x_4389_ == 0)
{
if (lean_obj_tag(v_locals_4373_) == 1)
{
lean_object* v_head_4390_; lean_object* v_tail_4391_; lean_object* v___x_4392_; 
v_head_4390_ = lean_ctor_get(v_locals_4373_, 0);
lean_inc(v_head_4390_);
v_tail_4391_ = lean_ctor_get(v_locals_4373_, 1);
lean_inc(v_tail_4391_);
lean_dec_ref_known(v_locals_4373_, 2);
v___x_4392_ = l_Lean_LocalDecl_value_x3f(v_head_4390_, v___x_4389_);
if (lean_obj_tag(v___x_4392_) == 0)
{
lean_object* v_w_4393_; lean_object* v___x_4394_; 
v_w_4393_ = l_Lean_LocalDecl_toExpr(v_head_4390_);
lean_inc_ref(v_00_u03c6_4374_);
v___x_4394_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_00_u03c6_4374_, v___y_4376_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_a_4395_; lean_object* v___x_4396_; uint8_t v___x_4397_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
lean_inc(v_a_4395_);
lean_dec_ref_known(v___x_4394_, 1);
v___x_4396_ = l_Lean_Expr_cleanupAnnotations(v_a_4395_);
lean_dec(v_a_4395_);
v___x_4397_ = l_Lean_Expr_isApp(v___x_4396_);
if (v___x_4397_ == 0)
{
lean_dec_ref(v___x_4396_);
lean_dec_ref(v_w_4393_);
lean_dec(v_tail_4391_);
lean_dec(v_tail_4372_);
v___y_4381_ = v___y_4375_;
v___y_4382_ = v___y_4376_;
v___y_4383_ = v___y_4377_;
v___y_4384_ = v___y_4378_;
goto v___jp_4380_;
}
else
{
lean_object* v___x_4398_; uint8_t v___x_4399_; 
v___x_4398_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4396_);
v___x_4399_ = l_Lean_Expr_isApp(v___x_4398_);
if (v___x_4399_ == 0)
{
lean_dec_ref(v___x_4398_);
lean_dec_ref(v___x_4396_);
lean_dec_ref(v_w_4393_);
lean_dec(v_tail_4391_);
lean_dec(v_tail_4372_);
v___y_4381_ = v___y_4375_;
v___y_4382_ = v___y_4376_;
v___y_4383_ = v___y_4377_;
v___y_4384_ = v___y_4378_;
goto v___jp_4380_;
}
else
{
lean_object* v_arg_4400_; lean_object* v_arg_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; uint8_t v___x_4404_; 
v_arg_4400_ = lean_ctor_get(v___x_4396_, 1);
lean_inc_ref(v_arg_4400_);
lean_dec_ref(v___x_4396_);
v_arg_4401_ = lean_ctor_get(v___x_4398_, 1);
lean_inc_ref(v_arg_4401_);
v___x_4402_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4398_);
lean_dec_ref(v___x_4398_);
v___x_4403_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__5));
v___x_4404_ = l_Lean_Expr_isConstOf(v___x_4402_, v___x_4403_);
if (v___x_4404_ == 0)
{
lean_object* v___x_4405_; uint8_t v___x_4406_; 
v___x_4405_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___closed__1));
v___x_4406_ = l_Lean_Expr_isConstOf(v___x_4402_, v___x_4405_);
lean_dec_ref(v___x_4402_);
if (v___x_4406_ == 0)
{
lean_dec_ref(v_arg_4401_);
lean_dec_ref(v_arg_4400_);
lean_dec_ref(v_w_4393_);
lean_dec(v_tail_4391_);
lean_dec(v_tail_4372_);
v___y_4381_ = v___y_4375_;
v___y_4382_ = v___y_4376_;
v___y_4383_ = v___y_4377_;
v___y_4384_ = v___y_4378_;
goto v___jp_4380_;
}
else
{
lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v___x_4407_ = lean_unsigned_to_nat(1u);
v___x_4408_ = lean_mk_empty_array_with_capacity(v___x_4407_);
lean_inc_ref(v_w_4393_);
v___x_4409_ = lean_array_push(v___x_4408_, v_w_4393_);
lean_inc_ref(v_arg_4400_);
v___x_4410_ = l_Lean_Expr_beta(v_arg_4400_, v___x_4409_);
v___x_4411_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v___x_4410_, v_tail_4372_, v_tail_4391_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4424_; 
v_a_4412_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4414_ = v___x_4411_;
v_isShared_4415_ = v_isSharedCheck_4424_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4411_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4424_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4422_; 
v___x_4416_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__2));
v___x_4417_ = l_Lean_Expr_getAppFn(v_00_u03c6_4374_);
lean_dec_ref(v_00_u03c6_4374_);
v___x_4418_ = l_Lean_Expr_constLevels_x21(v___x_4417_);
lean_dec_ref(v___x_4417_);
v___x_4419_ = l_Lean_mkConst(v___x_4416_, v___x_4418_);
v___x_4420_ = l_Lean_mkApp4(v___x_4419_, v_arg_4401_, v_arg_4400_, v_w_4393_, v_a_4412_);
if (v_isShared_4415_ == 0)
{
lean_ctor_set(v___x_4414_, 0, v___x_4420_);
v___x_4422_ = v___x_4414_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v___x_4420_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
else
{
lean_dec_ref(v_arg_4401_);
lean_dec_ref(v_arg_4400_);
lean_dec_ref(v_w_4393_);
lean_dec_ref(v_00_u03c6_4374_);
return v___x_4411_;
}
}
}
else
{
lean_object* v___x_4425_; 
lean_dec_ref(v___x_4402_);
lean_dec_ref(v_00_u03c6_4374_);
lean_inc_ref(v_arg_4400_);
v___x_4425_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v_arg_4400_, v_tail_4372_, v_tail_4391_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4435_; 
v_a_4426_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4428_ = v___x_4425_;
v_isShared_4429_ = v_isSharedCheck_4435_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4425_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4435_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4433_; 
v___x_4430_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10);
v___x_4431_ = l_Lean_mkApp4(v___x_4430_, v_arg_4401_, v_arg_4400_, v_w_4393_, v_a_4426_);
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 0, v___x_4431_);
v___x_4433_ = v___x_4428_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v___x_4431_);
v___x_4433_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
return v___x_4433_;
}
}
}
else
{
lean_dec_ref(v_arg_4401_);
lean_dec_ref(v_arg_4400_);
lean_dec_ref(v_w_4393_);
return v___x_4425_;
}
}
}
}
}
else
{
lean_dec_ref(v_w_4393_);
lean_dec(v_tail_4391_);
lean_dec_ref(v_00_u03c6_4374_);
lean_dec(v_tail_4372_);
return v___x_4394_;
}
}
else
{
lean_dec_ref_known(v___x_4392_, 1);
lean_dec(v_head_4390_);
if (lean_obj_tag(v_00_u03c6_4374_) == 8)
{
lean_object* v_value_4436_; lean_object* v_body_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; 
v_value_4436_ = lean_ctor_get(v_00_u03c6_4374_, 2);
lean_inc_ref(v_value_4436_);
v_body_4437_ = lean_ctor_get(v_00_u03c6_4374_, 3);
lean_inc_ref(v_body_4437_);
lean_dec_ref_known(v_00_u03c6_4374_, 4);
v___x_4438_ = lean_expr_instantiate1(v_body_4437_, v_value_4436_);
lean_dec_ref(v_value_4436_);
lean_dec_ref(v_body_4437_);
v___x_4439_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v___x_4438_, v_tail_4372_, v_tail_4391_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
return v___x_4439_;
}
else
{
lean_object* v___x_4440_; 
v___x_4440_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v_00_u03c6_4374_, v_tail_4372_, v_tail_4391_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
return v___x_4440_;
}
}
}
else
{
lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; 
lean_dec(v_locals_4373_);
lean_dec(v_tail_4372_);
v___x_4441_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__4, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__4_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__4);
v___x_4442_ = l_Lean_indentExpr(v_00_u03c6_4374_);
v___x_4443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4443_, 0, v___x_4441_);
lean_ctor_set(v___x_4443_, 1, v___x_4442_);
v___x_4444_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v___x_4443_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
return v___x_4444_;
}
}
else
{
lean_object* v___x_4445_; 
lean_dec(v_locals_4373_);
lean_dec(v_tail_4372_);
v___x_4445_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(v_00_u03c6_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
return v___x_4445_;
}
v___jp_4380_:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4385_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__1, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__1);
v___x_4386_ = l_Lean_indentExpr(v_00_u03c6_4374_);
v___x_4387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4387_, 0, v___x_4385_);
lean_ctor_set(v___x_4387_, 1, v___x_4386_);
v___x_4388_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v___x_4387_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
return v___x_4388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___boxed(lean_object* v_tail_4446_, lean_object* v_locals_4447_, lean_object* v_00_u03c6_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0(v_tail_4446_, v_locals_4447_, v_00_u03c6_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(lean_object* v_00_u03c6_4455_, lean_object* v_path_4456_, lean_object* v_locals_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_){
_start:
{
if (lean_obj_tag(v_path_4456_) == 1)
{
lean_object* v_head_4463_; lean_object* v_tail_4464_; lean_object* v_fst_4465_; lean_object* v_snd_4466_; lean_object* v___f_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
v_head_4463_ = lean_ctor_get(v_path_4456_, 0);
lean_inc(v_head_4463_);
v_tail_4464_ = lean_ctor_get(v_path_4456_, 1);
lean_inc(v_tail_4464_);
lean_dec_ref_known(v_path_4456_, 2);
v_fst_4465_ = lean_ctor_get(v_head_4463_, 0);
lean_inc(v_fst_4465_);
v_snd_4466_ = lean_ctor_get(v_head_4463_, 1);
lean_inc(v_snd_4466_);
lean_dec(v_head_4463_);
v___f_4467_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4467_, 0, v_tail_4464_);
lean_closure_set(v___f_4467_, 1, v_locals_4457_);
v___x_4468_ = lean_unsigned_to_nat(0u);
v___x_4469_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(v_00_u03c6_4455_, v_fst_4465_, v___x_4468_, v_snd_4466_, v___f_4467_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
lean_dec(v_snd_4466_);
lean_dec(v_fst_4465_);
return v___x_4469_;
}
else
{
lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
lean_dec(v_locals_4457_);
lean_dec(v_path_4456_);
v___x_4470_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__1, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__1);
v___x_4471_ = l_Lean_indentExpr(v_00_u03c6_4455_);
v___x_4472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4472_, 0, v___x_4470_);
lean_ctor_set(v___x_4472_, 1, v___x_4471_);
v___x_4473_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v___x_4472_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
return v___x_4473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___boxed(lean_object* v_00_u03c6_4474_, lean_object* v_path_4475_, lean_object* v_locals_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_){
_start:
{
lean_object* v_res_4482_; 
v_res_4482_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v_00_u03c6_4474_, v_path_4475_, v_locals_4476_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_);
lean_dec(v_a_4480_);
lean_dec_ref(v_a_4479_);
lean_dec(v_a_4478_);
lean_dec_ref(v_a_4477_);
return v_res_4482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg(lean_object* v_type_4483_, lean_object* v_k_4484_, uint8_t v_cleanupAnnotations_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
lean_object* v___f_4498_; uint8_t v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
lean_inc(v___y_4492_);
lean_inc_ref(v___y_4491_);
lean_inc(v___y_4490_);
lean_inc_ref(v___y_4489_);
lean_inc(v___y_4488_);
lean_inc(v___y_4487_);
lean_inc_ref(v___y_4486_);
v___f_4498_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__7___redArg___lam__0___boxed), 15, 8);
lean_closure_set(v___f_4498_, 0, v_k_4484_);
lean_closure_set(v___f_4498_, 1, v___y_4486_);
lean_closure_set(v___f_4498_, 2, v___y_4487_);
lean_closure_set(v___f_4498_, 3, v___y_4488_);
lean_closure_set(v___f_4498_, 4, v___y_4489_);
lean_closure_set(v___f_4498_, 5, v___y_4490_);
lean_closure_set(v___f_4498_, 6, v___y_4491_);
lean_closure_set(v___f_4498_, 7, v___y_4492_);
v___x_4499_ = 0;
v___x_4500_ = lean_box(0);
v___x_4501_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_4499_, v___x_4500_, v_type_4483_, v___f_4498_, v_cleanupAnnotations_4485_, v___x_4499_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
if (lean_obj_tag(v___x_4501_) == 0)
{
return v___x_4501_;
}
else
{
lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4509_; 
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4504_ = v___x_4501_;
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_dec(v___x_4501_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4507_; 
if (v_isShared_4505_ == 0)
{
v___x_4507_ = v___x_4504_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4502_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg___boxed(lean_object* v_type_4510_, lean_object* v_k_4511_, lean_object* v_cleanupAnnotations_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4525_; lean_object* v_res_4526_; 
v_cleanupAnnotations_boxed_4525_ = lean_unbox(v_cleanupAnnotations_4512_);
v_res_4526_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg(v_type_4510_, v_k_4511_, v_cleanupAnnotations_boxed_4525_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_);
lean_dec(v___y_4523_);
lean_dec_ref(v___y_4522_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_dec(v___y_4514_);
lean_dec_ref(v___y_4513_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1(lean_object* v_00_u03b1_4527_, lean_object* v_type_4528_, lean_object* v_k_4529_, uint8_t v_cleanupAnnotations_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_){
_start:
{
lean_object* v___x_4543_; 
v___x_4543_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg(v_type_4528_, v_k_4529_, v_cleanupAnnotations_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
return v___x_4543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___boxed(lean_object* v_00_u03b1_4544_, lean_object* v_type_4545_, lean_object* v_k_4546_, lean_object* v_cleanupAnnotations_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4560_; lean_object* v_res_4561_; 
v_cleanupAnnotations_boxed_4560_ = lean_unbox(v_cleanupAnnotations_4547_);
v_res_4561_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1(v_00_u03b1_4544_, v_type_4545_, v_k_4546_, v_cleanupAnnotations_boxed_4560_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
return v_res_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___redArg(lean_object* v_e_4562_, lean_object* v___y_4563_){
_start:
{
uint8_t v___x_4565_; 
v___x_4565_ = l_Lean_Expr_hasMVar(v_e_4562_);
if (v___x_4565_ == 0)
{
lean_object* v___x_4566_; 
v___x_4566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4566_, 0, v_e_4562_);
return v___x_4566_;
}
else
{
lean_object* v___x_4567_; lean_object* v_mctx_4568_; lean_object* v___x_4569_; lean_object* v_fst_4570_; lean_object* v_snd_4571_; lean_object* v___x_4572_; lean_object* v_cache_4573_; lean_object* v_zetaDeltaFVarIds_4574_; lean_object* v_postponed_4575_; lean_object* v_diag_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4585_; 
v___x_4567_ = lean_st_ref_get(v___y_4563_);
v_mctx_4568_ = lean_ctor_get(v___x_4567_, 0);
lean_inc_ref(v_mctx_4568_);
lean_dec(v___x_4567_);
v___x_4569_ = l_Lean_instantiateMVarsCore(v_mctx_4568_, v_e_4562_);
v_fst_4570_ = lean_ctor_get(v___x_4569_, 0);
lean_inc(v_fst_4570_);
v_snd_4571_ = lean_ctor_get(v___x_4569_, 1);
lean_inc(v_snd_4571_);
lean_dec_ref(v___x_4569_);
v___x_4572_ = lean_st_ref_take(v___y_4563_);
v_cache_4573_ = lean_ctor_get(v___x_4572_, 1);
v_zetaDeltaFVarIds_4574_ = lean_ctor_get(v___x_4572_, 2);
v_postponed_4575_ = lean_ctor_get(v___x_4572_, 3);
v_diag_4576_ = lean_ctor_get(v___x_4572_, 4);
v_isSharedCheck_4585_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4585_ == 0)
{
lean_object* v_unused_4586_; 
v_unused_4586_ = lean_ctor_get(v___x_4572_, 0);
lean_dec(v_unused_4586_);
v___x_4578_ = v___x_4572_;
v_isShared_4579_ = v_isSharedCheck_4585_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_diag_4576_);
lean_inc(v_postponed_4575_);
lean_inc(v_zetaDeltaFVarIds_4574_);
lean_inc(v_cache_4573_);
lean_dec(v___x_4572_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4585_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___x_4581_; 
if (v_isShared_4579_ == 0)
{
lean_ctor_set(v___x_4578_, 0, v_snd_4571_);
v___x_4581_ = v___x_4578_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v_snd_4571_);
lean_ctor_set(v_reuseFailAlloc_4584_, 1, v_cache_4573_);
lean_ctor_set(v_reuseFailAlloc_4584_, 2, v_zetaDeltaFVarIds_4574_);
lean_ctor_set(v_reuseFailAlloc_4584_, 3, v_postponed_4575_);
lean_ctor_set(v_reuseFailAlloc_4584_, 4, v_diag_4576_);
v___x_4581_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___x_4582_ = lean_st_ref_put(v___y_4563_, v___x_4581_);
v___x_4583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4583_, 0, v_fst_4570_);
return v___x_4583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___redArg___boxed(lean_object* v_e_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___redArg(v_e_4587_, v___y_4588_);
lean_dec(v___y_4588_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2(lean_object* v_e_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_){
_start:
{
lean_object* v___x_4604_; 
v___x_4604_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___redArg(v_e_4591_, v___y_4600_);
return v___x_4604_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___boxed(lean_object* v_e_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_){
_start:
{
lean_object* v_res_4618_; 
v_res_4618_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2(v_e_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
lean_dec(v___y_4616_);
lean_dec_ref(v___y_4615_);
lean_dec(v___y_4614_);
lean_dec_ref(v___y_4613_);
lean_dec(v___y_4612_);
lean_dec_ref(v___y_4611_);
lean_dec(v___y_4610_);
lean_dec_ref(v___y_4609_);
lean_dec(v___y_4608_);
lean_dec(v___y_4607_);
lean_dec_ref(v___y_4606_);
return v_res_4618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___lam__0(lean_object* v_a_4619_, lean_object* v_hyp_4620_, lean_object* v_xs_4621_, lean_object* v_x_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_){
_start:
{
lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4635_ = lean_unsigned_to_nat(0u);
v___x_4636_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(v_xs_4621_, v_a_4619_, v___x_4635_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
if (lean_obj_tag(v___x_4636_) == 0)
{
lean_object* v_a_4637_; lean_object* v_fst_4638_; lean_object* v_snd_4639_; uint8_t v___x_4640_; uint8_t v___x_4641_; uint8_t v___x_4642_; lean_object* v___x_4643_; 
v_a_4637_ = lean_ctor_get(v___x_4636_, 0);
lean_inc(v_a_4637_);
lean_dec_ref_known(v___x_4636_, 1);
v_fst_4638_ = lean_ctor_get(v_a_4637_, 0);
lean_inc(v_fst_4638_);
v_snd_4639_ = lean_ctor_get(v_a_4637_, 1);
lean_inc(v_snd_4639_);
lean_dec(v_a_4637_);
v___x_4640_ = 0;
v___x_4641_ = 1;
v___x_4642_ = 1;
v___x_4643_ = l_Lean_Meta_mkLambdaFVars(v_xs_4621_, v_fst_4638_, v___x_4640_, v___x_4641_, v___x_4640_, v___x_4641_, v___x_4642_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
if (lean_obj_tag(v___x_4643_) == 0)
{
lean_object* v_a_4644_; lean_object* v___x_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4652_; 
v_a_4644_ = lean_ctor_get(v___x_4643_, 0);
lean_inc(v_a_4644_);
lean_dec_ref_known(v___x_4643_, 1);
v___x_4645_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3___redArg(v_hyp_4620_, v_a_4644_, v___y_4631_);
v_isSharedCheck_4652_ = !lean_is_exclusive(v___x_4645_);
if (v_isSharedCheck_4652_ == 0)
{
lean_object* v_unused_4653_; 
v_unused_4653_ = lean_ctor_get(v___x_4645_, 0);
lean_dec(v_unused_4653_);
v___x_4647_ = v___x_4645_;
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
else
{
lean_dec(v___x_4645_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
lean_object* v___x_4650_; 
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 0, v_snd_4639_);
v___x_4650_ = v___x_4647_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_snd_4639_);
v___x_4650_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
return v___x_4650_;
}
}
}
else
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4661_; 
lean_dec(v_snd_4639_);
lean_dec(v_hyp_4620_);
v_a_4654_ = lean_ctor_get(v___x_4643_, 0);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4643_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4656_ = v___x_4643_;
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4643_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4659_; 
if (v_isShared_4657_ == 0)
{
v___x_4659_ = v___x_4656_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_a_4654_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
}
else
{
lean_object* v_a_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4669_; 
lean_dec(v_hyp_4620_);
v_a_4662_ = lean_ctor_get(v___x_4636_, 0);
v_isSharedCheck_4669_ = !lean_is_exclusive(v___x_4636_);
if (v_isSharedCheck_4669_ == 0)
{
v___x_4664_ = v___x_4636_;
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_a_4662_);
lean_dec(v___x_4636_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v___x_4667_; 
if (v_isShared_4665_ == 0)
{
v___x_4667_ = v___x_4664_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v_a_4662_);
v___x_4667_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
return v___x_4667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___lam__0___boxed(lean_object* v_a_4670_, lean_object* v_hyp_4671_, lean_object* v_xs_4672_, lean_object* v_x_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_){
_start:
{
lean_object* v_res_4686_; 
v_res_4686_ = l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___lam__0(v_a_4670_, v_hyp_4671_, v_xs_4672_, v_x_4673_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_);
lean_dec(v___y_4684_);
lean_dec_ref(v___y_4683_);
lean_dec(v___y_4682_);
lean_dec_ref(v___y_4681_);
lean_dec(v___y_4680_);
lean_dec_ref(v___y_4679_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec(v___y_4676_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec_ref(v_x_4673_);
lean_dec_ref(v_xs_4672_);
lean_dec_ref(v_a_4670_);
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg(lean_object* v_jp_4687_, size_t v_sz_4688_, size_t v_i_4689_, lean_object* v_bs_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_){
_start:
{
uint8_t v___x_4696_; 
v___x_4696_ = lean_usize_dec_lt(v_i_4689_, v_sz_4688_);
if (v___x_4696_ == 0)
{
lean_object* v___x_4697_; 
v___x_4697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4697_, 0, v_bs_4690_);
return v___x_4697_;
}
else
{
lean_object* v_v_4698_; lean_object* v___x_4699_; lean_object* v_bs_x27_4700_; lean_object* v___x_4701_; 
v_v_4698_ = lean_array_uget(v_bs_4690_, v_i_4689_);
v___x_4699_ = lean_unsigned_to_nat(0u);
v_bs_x27_4700_ = lean_array_uset(v_bs_4690_, v_i_4689_, v___x_4699_);
lean_inc(v_v_4698_);
v___x_4701_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals(v_jp_4687_, v_v_4698_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
if (lean_obj_tag(v___x_4701_) == 0)
{
lean_object* v_a_4702_; lean_object* v___x_4703_; size_t v___x_4704_; size_t v___x_4705_; lean_object* v___x_4706_; 
v_a_4702_ = lean_ctor_get(v___x_4701_, 0);
lean_inc(v_a_4702_);
lean_dec_ref_known(v___x_4701_, 1);
v___x_4703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4703_, 0, v_v_4698_);
lean_ctor_set(v___x_4703_, 1, v_a_4702_);
v___x_4704_ = ((size_t)1ULL);
v___x_4705_ = lean_usize_add(v_i_4689_, v___x_4704_);
v___x_4706_ = lean_array_uset(v_bs_x27_4700_, v_i_4689_, v___x_4703_);
v_i_4689_ = v___x_4705_;
v_bs_4690_ = v___x_4706_;
goto _start;
}
else
{
lean_object* v_a_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4715_; 
lean_dec_ref(v_bs_x27_4700_);
lean_dec(v_v_4698_);
v_a_4708_ = lean_ctor_get(v___x_4701_, 0);
v_isSharedCheck_4715_ = !lean_is_exclusive(v___x_4701_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4710_ = v___x_4701_;
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
else
{
lean_inc(v_a_4708_);
lean_dec(v___x_4701_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v___x_4713_; 
if (v_isShared_4711_ == 0)
{
v___x_4713_ = v___x_4710_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_a_4708_);
v___x_4713_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
return v___x_4713_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg___boxed(lean_object* v_jp_4716_, lean_object* v_sz_4717_, lean_object* v_i_4718_, lean_object* v_bs_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_){
_start:
{
size_t v_sz_boxed_4725_; size_t v_i_boxed_4726_; lean_object* v_res_4727_; 
v_sz_boxed_4725_ = lean_unbox_usize(v_sz_4717_);
lean_dec(v_sz_4717_);
v_i_boxed_4726_ = lean_unbox_usize(v_i_4718_);
lean_dec(v_i_4718_);
v_res_4727_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg(v_jp_4716_, v_sz_boxed_4725_, v_i_boxed_4726_, v_bs_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_);
lean_dec(v___y_4723_);
lean_dec_ref(v___y_4722_);
lean_dec(v___y_4721_);
lean_dec_ref(v___y_4720_);
lean_dec_ref(v_jp_4716_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___lam__0(lean_object* v_proof_4728_, lean_object* v_snd_4729_, lean_object* v_snd_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_){
_start:
{
lean_object* v___x_4743_; 
lean_inc(v_proof_4728_);
v___x_4743_ = l_Lean_MVarId_getType(v_proof_4728_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_);
if (lean_obj_tag(v___x_4743_) == 0)
{
lean_object* v_a_4744_; lean_object* v___x_4745_; 
v_a_4744_ = lean_ctor_get(v___x_4743_, 0);
lean_inc(v_a_4744_);
lean_dec_ref_known(v___x_4743_, 1);
v___x_4745_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___redArg(v_a_4744_, v___y_4739_);
if (lean_obj_tag(v___x_4745_) == 0)
{
lean_object* v_a_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; 
v_a_4746_ = lean_ctor_get(v___x_4745_, 0);
lean_inc(v_a_4746_);
lean_dec_ref_known(v___x_4745_, 1);
v___x_4747_ = lean_array_to_list(v_snd_4729_);
v___x_4748_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v_a_4746_, v_snd_4730_, v___x_4747_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_);
if (lean_obj_tag(v___x_4748_) == 0)
{
lean_object* v_a_4749_; lean_object* v___x_4750_; 
v_a_4749_ = lean_ctor_get(v___x_4748_, 0);
lean_inc(v_a_4749_);
lean_dec_ref_known(v___x_4748_, 1);
v___x_4750_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3___redArg(v_proof_4728_, v_a_4749_, v___y_4739_);
return v___x_4750_;
}
else
{
lean_object* v_a_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4758_; 
lean_dec(v_proof_4728_);
v_a_4751_ = lean_ctor_get(v___x_4748_, 0);
v_isSharedCheck_4758_ = !lean_is_exclusive(v___x_4748_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4753_ = v___x_4748_;
v_isShared_4754_ = v_isSharedCheck_4758_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_a_4751_);
lean_dec(v___x_4748_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4758_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
lean_object* v___x_4756_; 
if (v_isShared_4754_ == 0)
{
v___x_4756_ = v___x_4753_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_a_4751_);
v___x_4756_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
return v___x_4756_;
}
}
}
}
else
{
lean_object* v_a_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4766_; 
lean_dec(v_snd_4730_);
lean_dec_ref(v_snd_4729_);
lean_dec(v_proof_4728_);
v_a_4759_ = lean_ctor_get(v___x_4745_, 0);
v_isSharedCheck_4766_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4766_ == 0)
{
v___x_4761_ = v___x_4745_;
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_a_4759_);
lean_dec(v___x_4745_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v___x_4764_; 
if (v_isShared_4762_ == 0)
{
v___x_4764_ = v___x_4761_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_a_4759_);
v___x_4764_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
return v___x_4764_;
}
}
}
}
else
{
lean_object* v_a_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4774_; 
lean_dec(v_snd_4730_);
lean_dec_ref(v_snd_4729_);
lean_dec(v_proof_4728_);
v_a_4767_ = lean_ctor_get(v___x_4743_, 0);
v_isSharedCheck_4774_ = !lean_is_exclusive(v___x_4743_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4769_ = v___x_4743_;
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_a_4767_);
lean_dec(v___x_4743_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
lean_object* v___x_4772_; 
if (v_isShared_4770_ == 0)
{
v___x_4772_ = v___x_4769_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_a_4767_);
v___x_4772_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
return v___x_4772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___lam__0___boxed(lean_object* v_proof_4775_, lean_object* v_snd_4776_, lean_object* v_snd_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_){
_start:
{
lean_object* v_res_4790_; 
v_res_4790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___lam__0(v_proof_4775_, v_snd_4776_, v_snd_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_);
lean_dec(v___y_4788_);
lean_dec_ref(v___y_4787_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
lean_dec(v___y_4784_);
lean_dec_ref(v___y_4783_);
lean_dec(v___y_4782_);
lean_dec_ref(v___y_4781_);
lean_dec(v___y_4780_);
lean_dec(v___y_4779_);
lean_dec_ref(v___y_4778_);
return v_res_4790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3(lean_object* v_as_4791_, size_t v_sz_4792_, size_t v_i_4793_, lean_object* v_b_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_){
_start:
{
uint8_t v___x_4807_; 
v___x_4807_ = lean_usize_dec_lt(v_i_4793_, v_sz_4792_);
if (v___x_4807_ == 0)
{
lean_object* v___x_4808_; 
v___x_4808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4808_, 0, v_b_4794_);
return v___x_4808_;
}
else
{
lean_object* v_a_4809_; lean_object* v_fst_4810_; lean_object* v_fst_4811_; lean_object* v_snd_4812_; lean_object* v_snd_4813_; lean_object* v_proof_4814_; lean_object* v___x_4815_; lean_object* v___f_4816_; lean_object* v___x_4817_; 
v_a_4809_ = lean_array_uget_borrowed(v_as_4791_, v_i_4793_);
v_fst_4810_ = lean_ctor_get(v_a_4809_, 0);
v_fst_4811_ = lean_ctor_get(v_fst_4810_, 0);
v_snd_4812_ = lean_ctor_get(v_a_4809_, 1);
v_snd_4813_ = lean_ctor_get(v_fst_4810_, 1);
v_proof_4814_ = lean_ctor_get(v_fst_4811_, 0);
v___x_4815_ = lean_box(0);
lean_inc(v_snd_4812_);
lean_inc(v_snd_4813_);
lean_inc_n(v_proof_4814_, 2);
v___f_4816_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___lam__0___boxed), 15, 3);
lean_closure_set(v___f_4816_, 0, v_proof_4814_);
lean_closure_set(v___f_4816_, 1, v_snd_4813_);
lean_closure_set(v___f_4816_, 2, v_snd_4812_);
v___x_4817_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__10___redArg(v_proof_4814_, v___f_4816_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_, v___y_4805_);
if (lean_obj_tag(v___x_4817_) == 0)
{
size_t v___x_4818_; size_t v___x_4819_; 
lean_dec_ref_known(v___x_4817_, 1);
v___x_4818_ = ((size_t)1ULL);
v___x_4819_ = lean_usize_add(v_i_4793_, v___x_4818_);
v_i_4793_ = v___x_4819_;
v_b_4794_ = v___x_4815_;
goto _start;
}
else
{
return v___x_4817_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___boxed(lean_object* v_as_4821_, lean_object* v_sz_4822_, lean_object* v_i_4823_, lean_object* v_b_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_){
_start:
{
size_t v_sz_boxed_4837_; size_t v_i_boxed_4838_; lean_object* v_res_4839_; 
v_sz_boxed_4837_ = lean_unbox_usize(v_sz_4822_);
lean_dec(v_sz_4822_);
v_i_boxed_4838_ = lean_unbox_usize(v_i_4823_);
lean_dec(v_i_4823_);
v_res_4839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3(v_as_4821_, v_sz_boxed_4837_, v_i_boxed_4838_, v_b_4824_, v___y_4825_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
lean_dec(v___y_4835_);
lean_dec_ref(v___y_4834_);
lean_dec(v___y_4833_);
lean_dec_ref(v___y_4832_);
lean_dec(v___y_4831_);
lean_dec_ref(v___y_4830_);
lean_dec(v___y_4829_);
lean_dec_ref(v___y_4828_);
lean_dec(v___y_4827_);
lean_dec(v___y_4826_);
lean_dec_ref(v___y_4825_);
lean_dec_ref(v_as_4821_);
return v_res_4839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint(lean_object* v_jp_4840_, lean_object* v_jumps_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_){
_start:
{
size_t v_sz_4854_; size_t v___x_4855_; lean_object* v___x_4856_; 
v_sz_4854_ = lean_array_size(v_jumps_4841_);
v___x_4855_ = ((size_t)0ULL);
v___x_4856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg(v_jp_4840_, v_sz_4854_, v___x_4855_, v_jumps_4841_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_);
if (lean_obj_tag(v___x_4856_) == 0)
{
lean_object* v_a_4857_; lean_object* v_hyp_4858_; lean_object* v___f_4859_; lean_object* v___x_4860_; 
v_a_4857_ = lean_ctor_get(v___x_4856_, 0);
lean_inc_n(v_a_4857_, 2);
lean_dec_ref_known(v___x_4856_, 1);
v_hyp_4858_ = lean_ctor_get(v_jp_4840_, 2);
lean_inc_n(v_hyp_4858_, 2);
lean_dec_ref(v_jp_4840_);
v___f_4859_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___lam__0___boxed), 16, 2);
lean_closure_set(v___f_4859_, 0, v_a_4857_);
lean_closure_set(v___f_4859_, 1, v_hyp_4858_);
v___x_4860_ = l_Lean_MVarId_getType(v_hyp_4858_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_);
if (lean_obj_tag(v___x_4860_) == 0)
{
lean_object* v_a_4861_; uint8_t v___x_4862_; lean_object* v___x_4863_; 
v_a_4861_ = lean_ctor_get(v___x_4860_, 0);
lean_inc(v_a_4861_);
lean_dec_ref_known(v___x_4860_, 1);
v___x_4862_ = 0;
v___x_4863_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg(v_a_4861_, v___f_4859_, v___x_4862_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_);
if (lean_obj_tag(v___x_4863_) == 0)
{
lean_object* v_a_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; size_t v_sz_4867_; lean_object* v___x_4868_; 
v_a_4864_ = lean_ctor_get(v___x_4863_, 0);
lean_inc(v_a_4864_);
lean_dec_ref_known(v___x_4863_, 1);
v___x_4865_ = l_Array_zip___redArg(v_a_4857_, v_a_4864_);
lean_dec(v_a_4864_);
lean_dec(v_a_4857_);
v___x_4866_ = lean_box(0);
v_sz_4867_ = lean_array_size(v___x_4865_);
v___x_4868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3(v___x_4865_, v_sz_4867_, v___x_4855_, v___x_4866_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_);
lean_dec_ref(v___x_4865_);
if (lean_obj_tag(v___x_4868_) == 0)
{
lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4875_; 
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4868_);
if (v_isSharedCheck_4875_ == 0)
{
lean_object* v_unused_4876_; 
v_unused_4876_ = lean_ctor_get(v___x_4868_, 0);
lean_dec(v_unused_4876_);
v___x_4870_ = v___x_4868_;
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
else
{
lean_dec(v___x_4868_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v___x_4873_; 
if (v_isShared_4871_ == 0)
{
lean_ctor_set(v___x_4870_, 0, v___x_4866_);
v___x_4873_ = v___x_4870_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v___x_4866_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
}
else
{
return v___x_4868_;
}
}
else
{
lean_object* v_a_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4884_; 
lean_dec(v_a_4857_);
v_a_4877_ = lean_ctor_get(v___x_4863_, 0);
v_isSharedCheck_4884_ = !lean_is_exclusive(v___x_4863_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4879_ = v___x_4863_;
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_a_4877_);
lean_dec(v___x_4863_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___x_4882_; 
if (v_isShared_4880_ == 0)
{
v___x_4882_ = v___x_4879_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v_a_4877_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
return v___x_4882_;
}
}
}
}
else
{
lean_object* v_a_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4892_; 
lean_dec_ref(v___f_4859_);
lean_dec(v_a_4857_);
v_a_4885_ = lean_ctor_get(v___x_4860_, 0);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4860_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4887_ = v___x_4860_;
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_a_4885_);
lean_dec(v___x_4860_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v___x_4890_; 
if (v_isShared_4888_ == 0)
{
v___x_4890_ = v___x_4887_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v_a_4885_);
v___x_4890_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
return v___x_4890_;
}
}
}
}
else
{
lean_object* v_a_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4900_; 
lean_dec_ref(v_jp_4840_);
v_a_4893_ = lean_ctor_get(v___x_4856_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4856_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4895_ = v___x_4856_;
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_a_4893_);
lean_dec(v___x_4856_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
lean_object* v___x_4898_; 
if (v_isShared_4896_ == 0)
{
v___x_4898_ = v___x_4895_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v_a_4893_);
v___x_4898_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
return v___x_4898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___boxed(lean_object* v_jp_4901_, lean_object* v_jumps_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_){
_start:
{
lean_object* v_res_4915_; 
v_res_4915_ = l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint(v_jp_4901_, v_jumps_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_);
lean_dec(v_a_4913_);
lean_dec_ref(v_a_4912_);
lean_dec(v_a_4911_);
lean_dec_ref(v_a_4910_);
lean_dec(v_a_4909_);
lean_dec_ref(v_a_4908_);
lean_dec(v_a_4907_);
lean_dec_ref(v_a_4906_);
lean_dec(v_a_4905_);
lean_dec(v_a_4904_);
lean_dec_ref(v_a_4903_);
return v_res_4915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0(lean_object* v_jp_4916_, size_t v_sz_4917_, size_t v_i_4918_, lean_object* v_bs_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_){
_start:
{
lean_object* v___x_4932_; 
v___x_4932_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg(v_jp_4916_, v_sz_4917_, v_i_4918_, v_bs_4919_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_);
return v___x_4932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___boxed(lean_object* v_jp_4933_, lean_object* v_sz_4934_, lean_object* v_i_4935_, lean_object* v_bs_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_){
_start:
{
size_t v_sz_boxed_4949_; size_t v_i_boxed_4950_; lean_object* v_res_4951_; 
v_sz_boxed_4949_ = lean_unbox_usize(v_sz_4934_);
lean_dec(v_sz_4934_);
v_i_boxed_4950_ = lean_unbox_usize(v_i_4935_);
lean_dec(v_i_4935_);
v_res_4951_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0(v_jp_4933_, v_sz_boxed_4949_, v_i_boxed_4950_, v_bs_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_);
lean_dec(v___y_4947_);
lean_dec_ref(v___y_4946_);
lean_dec(v___y_4945_);
lean_dec_ref(v___y_4944_);
lean_dec(v___y_4943_);
lean_dec_ref(v___y_4942_);
lean_dec(v___y_4941_);
lean_dec_ref(v___y_4940_);
lean_dec(v___y_4939_);
lean_dec(v___y_4938_);
lean_dec_ref(v___y_4937_);
lean_dec_ref(v_jp_4933_);
return v_res_4951_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_WPApp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Reduce(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_JoinPoint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_WPApp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_VCGen_JoinPoint(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_WPApp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_Util(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_Reduce(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_VCGen_JoinPoint(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_WPApp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_JoinPoint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_VCGen_JoinPoint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_VCGen_JoinPoint(builtin);
}
#ifdef __cplusplus
}
#endif
