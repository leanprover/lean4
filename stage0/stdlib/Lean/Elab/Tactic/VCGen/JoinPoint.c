// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.JoinPoint
// Imports: public import Lean.Elab.Tactic.VCGen.Context public import Lean.Elab.Tactic.VCGen.WPApp import Lean.Meta.Sym.InferType import Lean.Meta.Sym.InstantiateMVarsS import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.AbstractS import Lean.Meta.Sym.Intro import Lean.Elab.Tactic.VCGen.Util
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
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_betaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_dec(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_Sym_mkForallFVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_Pred(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_prog(lean_object*);
lean_object* l_Lean_Expr_fvarId_x3f(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Tactic_Do_isJP(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "top"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "vcgen +jp: `"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` is not a type"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__2___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__8_spec__11_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__8_spec__11_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__3;
static const lean_array_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___boxed(lean_object**);
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
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
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "vcgen +jp: missing witness for"};
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1___redArg(lean_object* v_x_166_, uint8_t v_bi_167_, lean_object* v_t_168_, lean_object* v_b_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___y_178_; lean_object* v___x_181_; uint8_t v_debug_182_; 
v___x_181_ = lean_st_ref_get(v___y_171_);
v_debug_182_ = lean_ctor_get_uint8(v___x_181_, sizeof(void*)*12);
lean_dec(v___x_181_);
if (v_debug_182_ == 0)
{
v___y_178_ = v___y_171_;
goto v___jp_177_;
}
else
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_168_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v___x_184_; 
lean_dec_ref_known(v___x_183_, 1);
v___x_184_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_dec_ref_known(v___x_184_, 1);
v___y_178_ = v___y_171_;
goto v___jp_177_;
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec_ref(v_b_169_);
lean_dec_ref(v_t_168_);
lean_dec(v_x_166_);
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec_ref(v_b_169_);
lean_dec_ref(v_t_168_);
lean_dec(v_x_166_);
v_a_193_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_183_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_183_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
v___jp_177_:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = l_Lean_Expr_forallE___override(v_x_166_, v_t_168_, v_b_169_, v_bi_167_);
v___x_180_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_179_, v___y_178_);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1___redArg___boxed(lean_object* v_x_201_, lean_object* v_bi_202_, lean_object* v_t_203_, lean_object* v_b_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
uint8_t v_bi_boxed_212_; lean_object* v_res_213_; 
v_bi_boxed_212_ = lean_unbox(v_bi_202_);
v_res_213_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1___redArg(v_x_201_, v_bi_boxed_212_, v_t_203_, v_b_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1(lean_object* v_x_214_, uint8_t v_bi_215_, lean_object* v_t_216_, lean_object* v_b_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1___redArg(v_x_214_, v_bi_215_, v_t_216_, v_b_217_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1___boxed(lean_object* v_x_231_, lean_object* v_bi_232_, lean_object* v_t_233_, lean_object* v_b_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
uint8_t v_bi_boxed_247_; lean_object* v_res_248_; 
v_bi_boxed_247_ = lean_unbox(v_bi_232_);
v_res_248_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1(v_x_231_, v_bi_boxed_247_, v_t_233_, v_b_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___redArg___lam__0(lean_object* v_k_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v_b_257_, lean_object* v_c_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v___x_264_; 
lean_inc(v___y_262_);
lean_inc_ref(v___y_261_);
lean_inc(v___y_260_);
lean_inc_ref(v___y_259_);
lean_inc(v___y_256_);
lean_inc_ref(v___y_255_);
lean_inc(v___y_254_);
lean_inc_ref(v___y_253_);
lean_inc(v___y_252_);
lean_inc(v___y_251_);
lean_inc_ref(v___y_250_);
v___x_264_ = lean_apply_14(v_k_249_, v_b_257_, v_c_258_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, lean_box(0));
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___redArg___lam__0___boxed(lean_object* v_k_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v_b_273_, lean_object* v_c_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___redArg___lam__0(v_k_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v_b_273_, v_c_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___redArg(lean_object* v_type_281_, lean_object* v_maxFVars_x3f_282_, lean_object* v_k_283_, uint8_t v_cleanupAnnotations_284_, uint8_t v_whnfType_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v___f_298_; lean_object* v___x_299_; 
lean_inc(v___y_292_);
lean_inc_ref(v___y_291_);
lean_inc(v___y_290_);
lean_inc_ref(v___y_289_);
lean_inc(v___y_288_);
lean_inc(v___y_287_);
lean_inc_ref(v___y_286_);
v___f_298_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___redArg___lam__0___boxed), 15, 8);
lean_closure_set(v___f_298_, 0, v_k_283_);
lean_closure_set(v___f_298_, 1, v___y_286_);
lean_closure_set(v___f_298_, 2, v___y_287_);
lean_closure_set(v___f_298_, 3, v___y_288_);
lean_closure_set(v___f_298_, 4, v___y_289_);
lean_closure_set(v___f_298_, 5, v___y_290_);
lean_closure_set(v___f_298_, 6, v___y_291_);
lean_closure_set(v___f_298_, 7, v___y_292_);
v___x_299_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_281_, v_maxFVars_x3f_282_, v___f_298_, v_cleanupAnnotations_284_, v_whnfType_285_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
if (lean_obj_tag(v___x_299_) == 0)
{
return v___x_299_;
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___redArg___boxed(lean_object** _args){
lean_object* v_type_308_ = _args[0];
lean_object* v_maxFVars_x3f_309_ = _args[1];
lean_object* v_k_310_ = _args[2];
lean_object* v_cleanupAnnotations_311_ = _args[3];
lean_object* v_whnfType_312_ = _args[4];
lean_object* v___y_313_ = _args[5];
lean_object* v___y_314_ = _args[6];
lean_object* v___y_315_ = _args[7];
lean_object* v___y_316_ = _args[8];
lean_object* v___y_317_ = _args[9];
lean_object* v___y_318_ = _args[10];
lean_object* v___y_319_ = _args[11];
lean_object* v___y_320_ = _args[12];
lean_object* v___y_321_ = _args[13];
lean_object* v___y_322_ = _args[14];
lean_object* v___y_323_ = _args[15];
lean_object* v___y_324_ = _args[16];
_start:
{
uint8_t v_cleanupAnnotations_boxed_325_; uint8_t v_whnfType_boxed_326_; lean_object* v_res_327_; 
v_cleanupAnnotations_boxed_325_ = lean_unbox(v_cleanupAnnotations_311_);
v_whnfType_boxed_326_ = lean_unbox(v_whnfType_312_);
v_res_327_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___redArg(v_type_308_, v_maxFVars_x3f_309_, v_k_310_, v_cleanupAnnotations_boxed_325_, v_whnfType_boxed_326_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3(lean_object* v_00_u03b1_328_, lean_object* v_type_329_, lean_object* v_maxFVars_x3f_330_, lean_object* v_k_331_, uint8_t v_cleanupAnnotations_332_, uint8_t v_whnfType_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___redArg(v_type_329_, v_maxFVars_x3f_330_, v_k_331_, v_cleanupAnnotations_332_, v_whnfType_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___boxed(lean_object** _args){
lean_object* v_00_u03b1_347_ = _args[0];
lean_object* v_type_348_ = _args[1];
lean_object* v_maxFVars_x3f_349_ = _args[2];
lean_object* v_k_350_ = _args[3];
lean_object* v_cleanupAnnotations_351_ = _args[4];
lean_object* v_whnfType_352_ = _args[5];
lean_object* v___y_353_ = _args[6];
lean_object* v___y_354_ = _args[7];
lean_object* v___y_355_ = _args[8];
lean_object* v___y_356_ = _args[9];
lean_object* v___y_357_ = _args[10];
lean_object* v___y_358_ = _args[11];
lean_object* v___y_359_ = _args[12];
lean_object* v___y_360_ = _args[13];
lean_object* v___y_361_ = _args[14];
lean_object* v___y_362_ = _args[15];
lean_object* v___y_363_ = _args[16];
lean_object* v___y_364_ = _args[17];
_start:
{
uint8_t v_cleanupAnnotations_boxed_365_; uint8_t v_whnfType_boxed_366_; lean_object* v_res_367_; 
v_cleanupAnnotations_boxed_365_ = lean_unbox(v_cleanupAnnotations_351_);
v_whnfType_boxed_366_ = lean_unbox(v_whnfType_352_);
v_res_367_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3(v_00_u03b1_347_, v_type_348_, v_maxFVars_x3f_349_, v_k_350_, v_cleanupAnnotations_boxed_365_, v_whnfType_boxed_366_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4___redArg(lean_object* v_x_368_, lean_object* v_t_369_, lean_object* v_v_370_, lean_object* v_b_371_, uint8_t v_nondep_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v___y_381_; lean_object* v___x_384_; uint8_t v_debug_385_; 
v___x_384_ = lean_st_ref_get(v___y_374_);
v_debug_385_ = lean_ctor_get_uint8(v___x_384_, sizeof(void*)*12);
lean_dec(v___x_384_);
if (v_debug_385_ == 0)
{
v___y_381_ = v___y_374_;
goto v___jp_380_;
}
else
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_369_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v___x_387_; 
lean_dec_ref_known(v___x_386_, 1);
v___x_387_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_v_370_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v___x_388_; 
lean_dec_ref_known(v___x_387_, 1);
v___x_388_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_371_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_dec_ref_known(v___x_388_, 1);
v___y_381_ = v___y_374_;
goto v___jp_380_;
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_dec_ref(v_b_371_);
lean_dec_ref(v_v_370_);
lean_dec_ref(v_t_369_);
lean_dec(v_x_368_);
v_a_389_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_388_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_388_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec_ref(v_b_371_);
lean_dec_ref(v_v_370_);
lean_dec_ref(v_t_369_);
lean_dec(v_x_368_);
v_a_397_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_387_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_387_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec_ref(v_b_371_);
lean_dec_ref(v_v_370_);
lean_dec_ref(v_t_369_);
lean_dec(v_x_368_);
v_a_405_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_386_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_386_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
v___jp_380_:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = l_Lean_Expr_letE___override(v_x_368_, v_t_369_, v_v_370_, v_b_371_, v_nondep_372_);
v___x_383_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_382_, v___y_381_);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4___redArg___boxed(lean_object* v_x_413_, lean_object* v_t_414_, lean_object* v_v_415_, lean_object* v_b_416_, lean_object* v_nondep_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
uint8_t v_nondep_boxed_425_; lean_object* v_res_426_; 
v_nondep_boxed_425_ = lean_unbox(v_nondep_417_);
v_res_426_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4___redArg(v_x_413_, v_t_414_, v_v_415_, v_b_416_, v_nondep_boxed_425_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4(lean_object* v_x_427_, lean_object* v_t_428_, lean_object* v_v_429_, lean_object* v_b_430_, uint8_t v_nondep_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4___redArg(v_x_427_, v_t_428_, v_v_429_, v_b_430_, v_nondep_431_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4___boxed(lean_object** _args){
lean_object* v_x_445_ = _args[0];
lean_object* v_t_446_ = _args[1];
lean_object* v_v_447_ = _args[2];
lean_object* v_b_448_ = _args[3];
lean_object* v_nondep_449_ = _args[4];
lean_object* v___y_450_ = _args[5];
lean_object* v___y_451_ = _args[6];
lean_object* v___y_452_ = _args[7];
lean_object* v___y_453_ = _args[8];
lean_object* v___y_454_ = _args[9];
lean_object* v___y_455_ = _args[10];
lean_object* v___y_456_ = _args[11];
lean_object* v___y_457_ = _args[12];
lean_object* v___y_458_ = _args[13];
lean_object* v___y_459_ = _args[14];
lean_object* v___y_460_ = _args[15];
lean_object* v___y_461_ = _args[16];
_start:
{
uint8_t v_nondep_boxed_462_; lean_object* v_res_463_; 
v_nondep_boxed_462_ = lean_unbox(v_nondep_449_);
v_res_463_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4(v_x_445_, v_t_446_, v_v_447_, v_b_448_, v_nondep_boxed_462_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg___lam__0(lean_object* v_x_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___x_477_; 
lean_inc(v___y_471_);
lean_inc_ref(v___y_470_);
lean_inc(v___y_469_);
lean_inc_ref(v___y_468_);
lean_inc(v___y_467_);
lean_inc(v___y_466_);
lean_inc_ref(v___y_465_);
v___x_477_ = lean_apply_12(v_x_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, lean_box(0));
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg___lam__0___boxed(lean_object* v_x_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg___lam__0(v_x_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg(lean_object* v_mvarId_492_, lean_object* v_x_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___f_506_; lean_object* v___x_507_; 
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc(v___y_498_);
lean_inc_ref(v___y_497_);
lean_inc(v___y_496_);
lean_inc(v___y_495_);
lean_inc_ref(v___y_494_);
v___f_506_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_506_, 0, v_x_493_);
lean_closure_set(v___f_506_, 1, v___y_494_);
lean_closure_set(v___f_506_, 2, v___y_495_);
lean_closure_set(v___f_506_, 3, v___y_496_);
lean_closure_set(v___f_506_, 4, v___y_497_);
lean_closure_set(v___f_506_, 5, v___y_498_);
lean_closure_set(v___f_506_, 6, v___y_499_);
lean_closure_set(v___f_506_, 7, v___y_500_);
v___x_507_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_492_, v___f_506_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_507_) == 0)
{
return v___x_507_;
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_507_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg___boxed(lean_object* v_mvarId_516_, lean_object* v_x_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg(v_mvarId_516_, v_x_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6(lean_object* v_00_u03b1_531_, lean_object* v_mvarId_532_, lean_object* v_x_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg(v_mvarId_532_, v_x_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___boxed(lean_object* v_00_u03b1_547_, lean_object* v_mvarId_548_, lean_object* v_x_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6(v_00_u03b1_547_, v_mvarId_548_, v_x_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0_spec__0_spec__5___redArg(lean_object* v_f_563_, lean_object* v_a_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___y_573_; lean_object* v___x_576_; uint8_t v_debug_577_; 
v___x_576_ = lean_st_ref_get(v___y_566_);
v_debug_577_ = lean_ctor_get_uint8(v___x_576_, sizeof(void*)*12);
lean_dec(v___x_576_);
if (v_debug_577_ == 0)
{
v___y_573_ = v___y_566_;
goto v___jp_572_;
}
else
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_563_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v___x_579_; 
lean_dec_ref_known(v___x_578_, 1);
v___x_579_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_dec_ref_known(v___x_579_, 1);
v___y_573_ = v___y_566_;
goto v___jp_572_;
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref(v_a_564_);
lean_dec_ref(v_f_563_);
v_a_580_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_579_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_579_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec_ref(v_a_564_);
lean_dec_ref(v_f_563_);
v_a_588_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_578_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_578_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
v___jp_572_:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = l_Lean_Expr_app___override(v_f_563_, v_a_564_);
v___x_575_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_574_, v___y_573_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_f_596_, lean_object* v_a_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0_spec__0_spec__5___redArg(v_f_596_, v_a_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0_spec__0(lean_object* v_args_606_, lean_object* v_endIdx_607_, lean_object* v_b_608_, lean_object* v_i_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
uint8_t v___x_622_; 
v___x_622_ = lean_nat_dec_le(v_endIdx_607_, v_i_609_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = l_Lean_instInhabitedExpr;
v___x_624_ = lean_array_get_borrowed(v___x_623_, v_args_606_, v_i_609_);
lean_inc(v___x_624_);
v___x_625_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0_spec__0_spec__5___redArg(v_b_608_, v___x_624_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v___x_625_, 1);
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = lean_nat_add(v_i_609_, v___x_627_);
lean_dec(v_i_609_);
v_b_608_ = v_a_626_;
v_i_609_ = v___x_628_;
goto _start;
}
else
{
lean_dec(v_i_609_);
return v___x_625_;
}
}
else
{
lean_object* v___x_630_; 
lean_dec(v_i_609_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v_b_608_);
return v___x_630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0_spec__0___boxed(lean_object* v_args_631_, lean_object* v_endIdx_632_, lean_object* v_b_633_, lean_object* v_i_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0_spec__0(v_args_631_, v_endIdx_632_, v_b_633_, v_i_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v_endIdx_632_);
lean_dec_ref(v_args_631_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0(lean_object* v_f_648_, lean_object* v_args_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = lean_array_get_size(v_args_649_);
v___x_664_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0_spec__0(v_args_649_, v___x_663_, v_f_648_, v___x_662_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0___boxed(lean_object* v_f_665_, lean_object* v_args_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0(v_f_665_, v_args_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec_ref(v_args_666_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0(lean_object* v_args_683_, lean_object* v_head_684_, lean_object* v_ss_685_, lean_object* v_a_686_, lean_object* v___x_687_, lean_object* v_arg_688_, lean_object* v_arg_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v___x_692_, lean_object* v_prog_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_706_ = lean_unsigned_to_nat(7u);
v___x_707_ = lean_array_set(v_args_683_, v___x_706_, v_prog_693_);
v___x_708_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0(v_head_684_, v___x_707_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec_ref(v___x_707_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_710_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
v___x_710_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0(v_a_709_, v_ss_685_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_710_, 1);
v___x_712_ = l_Lean_Expr_getAppFn(v_a_686_);
v___x_713_ = l_Lean_Expr_constLevels_x21(v___x_712_);
lean_dec_ref(v___x_712_);
v___x_714_ = l_Lean_mkConst(v___x_687_, v___x_713_);
v___x_715_ = lean_unsigned_to_nat(4u);
v___x_716_ = lean_mk_empty_array_with_capacity(v___x_715_);
v___x_717_ = lean_array_push(v___x_716_, v_arg_688_);
v___x_718_ = lean_array_push(v___x_717_, v_arg_689_);
v___x_719_ = lean_array_push(v___x_718_, v_a_690_);
v___x_720_ = lean_array_push(v___x_719_, v_a_711_);
v___x_721_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0(v___x_714_, v___x_720_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec_ref(v___x_720_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_721_, 1);
v___x_723_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0(v_a_691_, v___x_692_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; uint8_t v___x_726_; lean_object* v___x_727_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_723_, 1);
v___x_725_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0___closed__1));
v___x_726_ = 0;
v___x_727_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1___redArg(v___x_725_, v___x_726_, v_a_724_, v_a_722_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_729_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___x_727_, 1);
v___x_729_ = l_Lean_Meta_Sym_mkForallFVarsS(v___x_692_, v_a_728_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
return v___x_729_;
}
else
{
lean_dec_ref(v___x_692_);
return v___x_727_;
}
}
else
{
lean_dec(v_a_722_);
lean_dec_ref(v___x_692_);
return v___x_723_;
}
}
else
{
lean_dec_ref(v___x_692_);
lean_dec_ref(v_a_691_);
return v___x_721_;
}
}
else
{
lean_dec_ref(v___x_692_);
lean_dec_ref(v_a_691_);
lean_dec_ref(v_a_690_);
lean_dec_ref(v_arg_689_);
lean_dec_ref(v_arg_688_);
lean_dec(v___x_687_);
return v___x_710_;
}
}
else
{
lean_dec_ref(v___x_692_);
lean_dec_ref(v_a_691_);
lean_dec_ref(v_a_690_);
lean_dec_ref(v_arg_689_);
lean_dec_ref(v_arg_688_);
lean_dec(v___x_687_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0___boxed(lean_object** _args){
lean_object* v_args_730_ = _args[0];
lean_object* v_head_731_ = _args[1];
lean_object* v_ss_732_ = _args[2];
lean_object* v_a_733_ = _args[3];
lean_object* v___x_734_ = _args[4];
lean_object* v_arg_735_ = _args[5];
lean_object* v_arg_736_ = _args[6];
lean_object* v_a_737_ = _args[7];
lean_object* v_a_738_ = _args[8];
lean_object* v___x_739_ = _args[9];
lean_object* v_prog_740_ = _args[10];
lean_object* v___y_741_ = _args[11];
lean_object* v___y_742_ = _args[12];
lean_object* v___y_743_ = _args[13];
lean_object* v___y_744_ = _args[14];
lean_object* v___y_745_ = _args[15];
lean_object* v___y_746_ = _args[16];
lean_object* v___y_747_ = _args[17];
lean_object* v___y_748_ = _args[18];
lean_object* v___y_749_ = _args[19];
lean_object* v___y_750_ = _args[20];
lean_object* v___y_751_ = _args[21];
lean_object* v___y_752_ = _args[22];
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0(v_args_730_, v_head_731_, v_ss_732_, v_a_733_, v___x_734_, v_arg_735_, v_arg_736_, v_a_737_, v_a_738_, v___x_739_, v_prog_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec_ref(v_a_733_);
lean_dec_ref(v_ss_732_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2_spec__3(lean_object* v_msgData_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; lean_object* v_env_761_; uint8_t v___x_762_; lean_object* v_env_763_; lean_object* v___x_764_; lean_object* v_toCold_765_; lean_object* v_mctx_766_; lean_object* v_lctx_767_; lean_object* v_options_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_760_ = lean_st_ref_get(v___y_758_);
v_env_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc_ref(v_env_761_);
lean_dec(v___x_760_);
v___x_762_ = 0;
v_env_763_ = l_Lean_Environment_setRecordingDeps(v_env_761_, v___x_762_);
v___x_764_ = lean_st_ref_get(v___y_756_);
v_toCold_765_ = lean_ctor_get(v___y_757_, 0);
v_mctx_766_ = lean_ctor_get(v___x_764_, 0);
lean_inc_ref(v_mctx_766_);
lean_dec(v___x_764_);
v_lctx_767_ = lean_ctor_get(v___y_755_, 2);
v_options_768_ = lean_ctor_get(v_toCold_765_, 2);
lean_inc_ref(v_options_768_);
lean_inc_ref(v_lctx_767_);
v___x_769_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_769_, 0, v_env_763_);
lean_ctor_set(v___x_769_, 1, v_mctx_766_);
lean_ctor_set(v___x_769_, 2, v_lctx_767_);
lean_ctor_set(v___x_769_, 3, v_options_768_);
v___x_770_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v_msgData_754_);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2_spec__3___boxed(lean_object* v_msgData_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2_spec__3(v_msgData_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___redArg(lean_object* v_msg_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_ref_785_; lean_object* v___x_786_; lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_795_; 
v_ref_785_ = lean_ctor_get(v___y_782_, 2);
v___x_786_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2_spec__3(v_msg_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_795_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_793_; 
lean_inc(v_ref_785_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v_ref_785_);
lean_ctor_set(v___x_791_, 1, v_a_787_);
if (v_isShared_790_ == 0)
{
lean_ctor_set_tag(v___x_789_, 1);
lean_ctor_set(v___x_789_, 0, v___x_791_);
v___x_793_ = v___x_789_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___redArg___boxed(lean_object* v_msg_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___redArg(v_msg_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
return v_res_802_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__1(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = lean_box(0);
v___x_805_ = l_Lean_mkSort(v___x_804_);
return v___x_805_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__3(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__2));
v___x_808_ = l_Lean_stringToMessageData(v___x_807_);
return v___x_808_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__5(void){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__4));
v___x_811_ = l_Lean_stringToMessageData(v___x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1(lean_object* v_instCL_812_, lean_object* v___x_813_, lean_object* v___x_814_, lean_object* v_xs_815_, lean_object* v_lctx_816_, lean_object* v_localInstances_817_, lean_object* v_args_818_, lean_object* v_head_819_, lean_object* v_a_820_, lean_object* v___x_821_, lean_object* v_arg_822_, lean_object* v_arg_823_, lean_object* v___x_824_, lean_object* v_val_825_, lean_object* v_ss_826_, lean_object* v_B_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f(v_instCL_812_, v_ss_826_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_970_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_970_ == 0)
{
v___x_843_ = v___x_840_;
v_isShared_844_ = v_isSharedCheck_970_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_840_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_970_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
if (lean_obj_tag(v_a_841_) == 1)
{
lean_object* v_val_845_; lean_object* v___x_846_; 
lean_del_object(v___x_843_);
v_val_845_ = lean_ctor_get(v_a_841_, 0);
lean_inc(v_val_845_);
lean_dec_ref_known(v_a_841_, 1);
lean_inc_ref(v_B_827_);
v___x_846_ = l_Lean_Meta_Sym_getLevel___redArg(v_B_827_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_848_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_846_, 1);
v___x_848_ = l_Lean_Level_dec(v_a_847_);
lean_dec(v_a_847_);
if (lean_obj_tag(v___x_848_) == 1)
{
lean_object* v_val_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_951_; 
v_val_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_951_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_951_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_val_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_951_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_853_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__0));
v___x_854_ = l_Lean_Name_mkStr3(v___x_813_, v___x_814_, v___x_853_);
v___x_855_ = lean_box(0);
v___x_856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_856_, 0, v_val_849_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = l_Lean_mkConst(v___x_854_, v___x_856_);
v___x_858_ = lean_unsigned_to_nat(2u);
v___x_859_ = lean_mk_empty_array_with_capacity(v___x_858_);
v___x_860_ = lean_array_push(v___x_859_, v_B_827_);
v___x_861_ = lean_array_push(v___x_860_, v_val_845_);
v___x_862_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0(v___x_857_, v___x_861_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec_ref(v___x_861_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___x_862_, 1);
lean_inc_ref(v_xs_815_);
v___x_864_ = l_Array_append___redArg(v_xs_815_, v_ss_826_);
v___x_865_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__1, &l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__1);
lean_inc_ref(v___x_864_);
v___x_866_ = l_Lean_Meta_Sym_mkForallFVarsS(v___x_864_, v___x_865_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_866_, 1);
v___x_868_ = 2;
v___x_869_ = lean_box(0);
v___x_870_ = lean_unsigned_to_nat(0u);
v___x_871_ = l_Lean_Meta_mkFreshExprMVarAt(v_lctx_816_, v_localInstances_817_, v_a_867_, v___x_868_, v___x_869_, v___x_870_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_873_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref_known(v___x_871_, 1);
v___x_873_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0(v___x_824_, v_xs_815_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_875_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref_known(v___x_873_, 1);
lean_inc_ref(v___x_864_);
lean_inc(v_a_872_);
lean_inc(v_a_863_);
lean_inc_ref(v_arg_823_);
lean_inc_ref(v_arg_822_);
lean_inc(v___x_821_);
lean_inc_ref(v_head_819_);
lean_inc_ref(v_args_818_);
v___x_875_ = l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0(v_args_818_, v_head_819_, v_ss_826_, v_a_820_, v___x_821_, v_arg_822_, v_arg_823_, v_a_863_, v_a_872_, v___x_864_, v_a_874_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_877_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v___x_875_, 1);
v___x_877_ = l_Lean_Meta_Sym_betaS(v_val_825_, v_xs_815_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_879_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v___x_877_, 1);
lean_inc(v_a_872_);
lean_inc(v_a_863_);
v___x_879_ = l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__0(v_args_818_, v_head_819_, v_ss_826_, v_a_820_, v___x_821_, v_arg_822_, v_arg_823_, v_a_863_, v_a_872_, v___x_864_, v_a_878_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_894_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_894_ == 0)
{
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_894_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_894_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_884_ = l_Lean_Expr_mvarId_x21(v_a_872_);
lean_dec(v_a_872_);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v_a_876_);
lean_ctor_set(v___x_885_, 1, v_a_880_);
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v_a_863_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_884_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_887_);
v___x_889_ = v___x_851_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_893_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_891_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_889_);
v___x_891_ = v___x_882_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec(v_a_876_);
lean_dec(v_a_872_);
lean_dec(v_a_863_);
lean_del_object(v___x_851_);
v_a_895_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_879_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_879_);
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
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec(v_a_876_);
lean_dec(v_a_872_);
lean_dec_ref(v___x_864_);
lean_dec(v_a_863_);
lean_del_object(v___x_851_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_822_);
lean_dec(v___x_821_);
lean_dec_ref(v_head_819_);
lean_dec_ref(v_args_818_);
v_a_903_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_877_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_877_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec(v_a_872_);
lean_dec_ref(v___x_864_);
lean_dec(v_a_863_);
lean_del_object(v___x_851_);
lean_dec_ref(v_val_825_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_822_);
lean_dec(v___x_821_);
lean_dec_ref(v_head_819_);
lean_dec_ref(v_args_818_);
lean_dec_ref(v_xs_815_);
v_a_911_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_875_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_875_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec(v_a_872_);
lean_dec_ref(v___x_864_);
lean_dec(v_a_863_);
lean_del_object(v___x_851_);
lean_dec_ref(v_val_825_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_822_);
lean_dec(v___x_821_);
lean_dec_ref(v_head_819_);
lean_dec_ref(v_args_818_);
lean_dec_ref(v_xs_815_);
v_a_919_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_873_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_873_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec_ref(v___x_864_);
lean_dec(v_a_863_);
lean_del_object(v___x_851_);
lean_dec_ref(v_val_825_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_822_);
lean_dec(v___x_821_);
lean_dec_ref(v_head_819_);
lean_dec_ref(v_args_818_);
lean_dec_ref(v_xs_815_);
v_a_927_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_871_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_871_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec_ref(v___x_864_);
lean_dec(v_a_863_);
lean_del_object(v___x_851_);
lean_dec_ref(v_val_825_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_822_);
lean_dec(v___x_821_);
lean_dec_ref(v_head_819_);
lean_dec_ref(v_args_818_);
lean_dec_ref(v_localInstances_817_);
lean_dec_ref(v_lctx_816_);
lean_dec_ref(v_xs_815_);
v_a_935_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_866_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_866_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_del_object(v___x_851_);
lean_dec_ref(v_val_825_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_822_);
lean_dec(v___x_821_);
lean_dec_ref(v_head_819_);
lean_dec_ref(v_args_818_);
lean_dec_ref(v_localInstances_817_);
lean_dec_ref(v_lctx_816_);
lean_dec_ref(v_xs_815_);
v_a_943_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_862_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_862_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
else
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
lean_dec(v___x_848_);
lean_dec(v_val_845_);
lean_dec_ref(v_val_825_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_822_);
lean_dec(v___x_821_);
lean_dec_ref(v_head_819_);
lean_dec_ref(v_args_818_);
lean_dec_ref(v_localInstances_817_);
lean_dec_ref(v_lctx_816_);
lean_dec_ref(v_xs_815_);
lean_dec_ref(v___x_814_);
lean_dec_ref(v___x_813_);
v___x_952_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__3, &l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__3);
v___x_953_ = l_Lean_MessageData_ofExpr(v_B_827_);
v___x_954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__5, &l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___closed__5);
v___x_956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_954_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___redArg(v___x_956_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
return v___x_957_;
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec(v_val_845_);
lean_dec_ref(v_B_827_);
lean_dec_ref(v_val_825_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_822_);
lean_dec(v___x_821_);
lean_dec_ref(v_head_819_);
lean_dec_ref(v_args_818_);
lean_dec_ref(v_localInstances_817_);
lean_dec_ref(v_lctx_816_);
lean_dec_ref(v_xs_815_);
lean_dec_ref(v___x_814_);
lean_dec_ref(v___x_813_);
v_a_958_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_846_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_846_);
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
else
{
lean_object* v___x_966_; lean_object* v___x_968_; 
lean_dec(v_a_841_);
lean_dec_ref(v_B_827_);
lean_dec_ref(v_val_825_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_822_);
lean_dec(v___x_821_);
lean_dec_ref(v_head_819_);
lean_dec_ref(v_args_818_);
lean_dec_ref(v_localInstances_817_);
lean_dec_ref(v_lctx_816_);
lean_dec_ref(v_xs_815_);
lean_dec_ref(v___x_814_);
lean_dec_ref(v___x_813_);
v___x_966_ = lean_box(0);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_966_);
v___x_968_ = v___x_843_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
lean_dec_ref(v_B_827_);
lean_dec_ref(v_val_825_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_822_);
lean_dec(v___x_821_);
lean_dec_ref(v_head_819_);
lean_dec_ref(v_args_818_);
lean_dec_ref(v_localInstances_817_);
lean_dec_ref(v_lctx_816_);
lean_dec_ref(v_xs_815_);
lean_dec_ref(v___x_814_);
lean_dec_ref(v___x_813_);
v_a_971_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_840_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_840_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___boxed(lean_object** _args){
lean_object* v_instCL_979_ = _args[0];
lean_object* v___x_980_ = _args[1];
lean_object* v___x_981_ = _args[2];
lean_object* v_xs_982_ = _args[3];
lean_object* v_lctx_983_ = _args[4];
lean_object* v_localInstances_984_ = _args[5];
lean_object* v_args_985_ = _args[6];
lean_object* v_head_986_ = _args[7];
lean_object* v_a_987_ = _args[8];
lean_object* v___x_988_ = _args[9];
lean_object* v_arg_989_ = _args[10];
lean_object* v_arg_990_ = _args[11];
lean_object* v___x_991_ = _args[12];
lean_object* v_val_992_ = _args[13];
lean_object* v_ss_993_ = _args[14];
lean_object* v_B_994_ = _args[15];
lean_object* v___y_995_ = _args[16];
lean_object* v___y_996_ = _args[17];
lean_object* v___y_997_ = _args[18];
lean_object* v___y_998_ = _args[19];
lean_object* v___y_999_ = _args[20];
lean_object* v___y_1000_ = _args[21];
lean_object* v___y_1001_ = _args[22];
lean_object* v___y_1002_ = _args[23];
lean_object* v___y_1003_ = _args[24];
lean_object* v___y_1004_ = _args[25];
lean_object* v___y_1005_ = _args[26];
lean_object* v___y_1006_ = _args[27];
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1(v_instCL_979_, v___x_980_, v___x_981_, v_xs_982_, v_lctx_983_, v_localInstances_984_, v_args_985_, v_head_986_, v_a_987_, v___x_988_, v_arg_989_, v_arg_990_, v___x_991_, v_val_992_, v_ss_993_, v_B_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec_ref(v_ss_993_);
lean_dec_ref(v_a_987_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__2(lean_object* v_info_1008_, lean_object* v_instCL_1009_, lean_object* v___x_1010_, lean_object* v___x_1011_, lean_object* v_lctx_1012_, lean_object* v_localInstances_1013_, lean_object* v_a_1014_, lean_object* v___x_1015_, lean_object* v_arg_1016_, lean_object* v_arg_1017_, lean_object* v___x_1018_, lean_object* v_val_1019_, lean_object* v_xs_1020_, lean_object* v_x_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_head_1034_; lean_object* v_args_1035_; lean_object* v_excessArgs_1036_; lean_object* v___f_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; lean_object* v___x_1042_; 
v_head_1034_ = lean_ctor_get(v_info_1008_, 1);
v_args_1035_ = lean_ctor_get(v_info_1008_, 2);
v_excessArgs_1036_ = lean_ctor_get(v_info_1008_, 3);
lean_inc_ref(v_excessArgs_1036_);
lean_inc_ref(v_head_1034_);
lean_inc_ref(v_args_1035_);
v___f_1037_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__1___boxed), 28, 14);
lean_closure_set(v___f_1037_, 0, v_instCL_1009_);
lean_closure_set(v___f_1037_, 1, v___x_1010_);
lean_closure_set(v___f_1037_, 2, v___x_1011_);
lean_closure_set(v___f_1037_, 3, v_xs_1020_);
lean_closure_set(v___f_1037_, 4, v_lctx_1012_);
lean_closure_set(v___f_1037_, 5, v_localInstances_1013_);
lean_closure_set(v___f_1037_, 6, v_args_1035_);
lean_closure_set(v___f_1037_, 7, v_head_1034_);
lean_closure_set(v___f_1037_, 8, v_a_1014_);
lean_closure_set(v___f_1037_, 9, v___x_1015_);
lean_closure_set(v___f_1037_, 10, v_arg_1016_);
lean_closure_set(v___f_1037_, 11, v_arg_1017_);
lean_closure_set(v___f_1037_, 12, v___x_1018_);
lean_closure_set(v___f_1037_, 13, v_val_1019_);
v___x_1038_ = l_Lean_Elab_Tactic_VCGen_WPApp_Pred(v_info_1008_);
lean_dec_ref(v_info_1008_);
v___x_1039_ = lean_array_get_size(v_excessArgs_1036_);
lean_dec_ref(v_excessArgs_1036_);
v___x_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
v___x_1041_ = 0;
v___x_1042_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___redArg(v___x_1038_, v___x_1040_, v___f_1037_, v___x_1041_, v___x_1041_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__2___boxed(lean_object** _args){
lean_object* v_info_1043_ = _args[0];
lean_object* v_instCL_1044_ = _args[1];
lean_object* v___x_1045_ = _args[2];
lean_object* v___x_1046_ = _args[3];
lean_object* v_lctx_1047_ = _args[4];
lean_object* v_localInstances_1048_ = _args[5];
lean_object* v_a_1049_ = _args[6];
lean_object* v___x_1050_ = _args[7];
lean_object* v_arg_1051_ = _args[8];
lean_object* v_arg_1052_ = _args[9];
lean_object* v___x_1053_ = _args[10];
lean_object* v_val_1054_ = _args[11];
lean_object* v_xs_1055_ = _args[12];
lean_object* v_x_1056_ = _args[13];
lean_object* v___y_1057_ = _args[14];
lean_object* v___y_1058_ = _args[15];
lean_object* v___y_1059_ = _args[16];
lean_object* v___y_1060_ = _args[17];
lean_object* v___y_1061_ = _args[18];
lean_object* v___y_1062_ = _args[19];
lean_object* v___y_1063_ = _args[20];
lean_object* v___y_1064_ = _args[21];
lean_object* v___y_1065_ = _args[22];
lean_object* v___y_1066_ = _args[23];
lean_object* v___y_1067_ = _args[24];
lean_object* v___y_1068_ = _args[25];
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__2(v_info_1043_, v_instCL_1044_, v___x_1045_, v___x_1046_, v_lctx_1047_, v_localInstances_1048_, v_a_1049_, v___x_1050_, v_arg_1051_, v_arg_1052_, v___x_1053_, v_val_1054_, v_xs_1055_, v_x_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec_ref(v_x_1056_);
return v_res_1069_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__7___redArg(lean_object* v_a_1070_, lean_object* v_x_1071_){
_start:
{
if (lean_obj_tag(v_x_1071_) == 0)
{
uint8_t v___x_1072_; 
v___x_1072_ = 0;
return v___x_1072_;
}
else
{
lean_object* v_key_1073_; lean_object* v_tail_1074_; uint8_t v___x_1075_; 
v_key_1073_ = lean_ctor_get(v_x_1071_, 0);
v_tail_1074_ = lean_ctor_get(v_x_1071_, 2);
v___x_1075_ = l_Lean_instBEqMVarId_beq(v_key_1073_, v_a_1070_);
if (v___x_1075_ == 0)
{
v_x_1071_ = v_tail_1074_;
goto _start;
}
else
{
return v___x_1075_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__7___redArg___boxed(lean_object* v_a_1077_, lean_object* v_x_1078_){
_start:
{
uint8_t v_res_1079_; lean_object* v_r_1080_; 
v_res_1079_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__7___redArg(v_a_1077_, v_x_1078_);
lean_dec(v_x_1078_);
lean_dec(v_a_1077_);
v_r_1080_ = lean_box(v_res_1079_);
return v_r_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__9___redArg(lean_object* v_a_1081_, lean_object* v_b_1082_, lean_object* v_x_1083_){
_start:
{
if (lean_obj_tag(v_x_1083_) == 0)
{
lean_dec(v_b_1082_);
lean_dec(v_a_1081_);
return v_x_1083_;
}
else
{
lean_object* v_key_1084_; lean_object* v_value_1085_; lean_object* v_tail_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1098_; 
v_key_1084_ = lean_ctor_get(v_x_1083_, 0);
v_value_1085_ = lean_ctor_get(v_x_1083_, 1);
v_tail_1086_ = lean_ctor_get(v_x_1083_, 2);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_x_1083_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1088_ = v_x_1083_;
v_isShared_1089_ = v_isSharedCheck_1098_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_tail_1086_);
lean_inc(v_value_1085_);
lean_inc(v_key_1084_);
lean_dec(v_x_1083_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1098_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
uint8_t v___x_1090_; 
v___x_1090_ = l_Lean_instBEqMVarId_beq(v_key_1084_, v_a_1081_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1091_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__9___redArg(v_a_1081_, v_b_1082_, v_tail_1086_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 2, v___x_1091_);
v___x_1093_ = v___x_1088_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_key_1084_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_value_1085_);
lean_ctor_set(v_reuseFailAlloc_1094_, 2, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
else
{
lean_object* v___x_1096_; 
lean_dec(v_value_1085_);
lean_dec(v_key_1084_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v_b_1082_);
lean_ctor_set(v___x_1088_, 0, v_a_1081_);
v___x_1096_ = v___x_1088_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1081_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_b_1082_);
lean_ctor_set(v_reuseFailAlloc_1097_, 2, v_tail_1086_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__8_spec__11_spec__12___redArg(lean_object* v_x_1099_, lean_object* v_x_1100_){
_start:
{
if (lean_obj_tag(v_x_1100_) == 0)
{
return v_x_1099_;
}
else
{
lean_object* v_key_1101_; lean_object* v_value_1102_; lean_object* v_tail_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1126_; 
v_key_1101_ = lean_ctor_get(v_x_1100_, 0);
v_value_1102_ = lean_ctor_get(v_x_1100_, 1);
v_tail_1103_ = lean_ctor_get(v_x_1100_, 2);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_x_1100_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1105_ = v_x_1100_;
v_isShared_1106_ = v_isSharedCheck_1126_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_tail_1103_);
lean_inc(v_value_1102_);
lean_inc(v_key_1101_);
lean_dec(v_x_1100_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1126_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; uint64_t v___x_1108_; uint64_t v___x_1109_; uint64_t v___x_1110_; uint64_t v_fold_1111_; uint64_t v___x_1112_; uint64_t v___x_1113_; uint64_t v___x_1114_; size_t v___x_1115_; size_t v___x_1116_; size_t v___x_1117_; size_t v___x_1118_; size_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1107_ = lean_array_get_size(v_x_1099_);
v___x_1108_ = l_Lean_instHashableMVarId_hash(v_key_1101_);
v___x_1109_ = 32ULL;
v___x_1110_ = lean_uint64_shift_right(v___x_1108_, v___x_1109_);
v_fold_1111_ = lean_uint64_xor(v___x_1108_, v___x_1110_);
v___x_1112_ = 16ULL;
v___x_1113_ = lean_uint64_shift_right(v_fold_1111_, v___x_1112_);
v___x_1114_ = lean_uint64_xor(v_fold_1111_, v___x_1113_);
v___x_1115_ = lean_uint64_to_usize(v___x_1114_);
v___x_1116_ = lean_usize_of_nat(v___x_1107_);
v___x_1117_ = ((size_t)1ULL);
v___x_1118_ = lean_usize_sub(v___x_1116_, v___x_1117_);
v___x_1119_ = lean_usize_land(v___x_1115_, v___x_1118_);
v___x_1120_ = lean_array_uget_borrowed(v_x_1099_, v___x_1119_);
lean_inc(v___x_1120_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 2, v___x_1120_);
v___x_1122_ = v___x_1105_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_key_1101_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_value_1102_);
lean_ctor_set(v_reuseFailAlloc_1125_, 2, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_array_uset(v_x_1099_, v___x_1119_, v___x_1122_);
v_x_1099_ = v___x_1123_;
v_x_1100_ = v_tail_1103_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__8_spec__11___redArg(lean_object* v_i_1127_, lean_object* v_source_1128_, lean_object* v_target_1129_){
_start:
{
lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = lean_array_get_size(v_source_1128_);
v___x_1131_ = lean_nat_dec_lt(v_i_1127_, v___x_1130_);
if (v___x_1131_ == 0)
{
lean_dec_ref(v_source_1128_);
lean_dec(v_i_1127_);
return v_target_1129_;
}
else
{
lean_object* v_es_1132_; lean_object* v___x_1133_; lean_object* v_source_1134_; lean_object* v_target_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v_es_1132_ = lean_array_fget(v_source_1128_, v_i_1127_);
v___x_1133_ = lean_box(0);
v_source_1134_ = lean_array_fset(v_source_1128_, v_i_1127_, v___x_1133_);
v_target_1135_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__8_spec__11_spec__12___redArg(v_target_1129_, v_es_1132_);
v___x_1136_ = lean_unsigned_to_nat(1u);
v___x_1137_ = lean_nat_add(v_i_1127_, v___x_1136_);
lean_dec(v_i_1127_);
v_i_1127_ = v___x_1137_;
v_source_1128_ = v_source_1134_;
v_target_1129_ = v_target_1135_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__8___redArg(lean_object* v_data_1139_){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v_nbuckets_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1140_ = lean_array_get_size(v_data_1139_);
v___x_1141_ = lean_unsigned_to_nat(2u);
v_nbuckets_1142_ = lean_nat_mul(v___x_1140_, v___x_1141_);
v___x_1143_ = lean_unsigned_to_nat(0u);
v___x_1144_ = lean_box(0);
v___x_1145_ = lean_mk_array(v_nbuckets_1142_, v___x_1144_);
v___x_1146_ = lean_array_propagate_mark(v_data_1139_, v___x_1145_);
v___x_1147_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__8_spec__11___redArg(v___x_1143_, v_data_1139_, v___x_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5___redArg(lean_object* v_m_1148_, lean_object* v_a_1149_, lean_object* v_b_1150_){
_start:
{
lean_object* v_size_1151_; lean_object* v_buckets_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1195_; 
v_size_1151_ = lean_ctor_get(v_m_1148_, 0);
v_buckets_1152_ = lean_ctor_get(v_m_1148_, 1);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_m_1148_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1154_ = v_m_1148_;
v_isShared_1155_ = v_isSharedCheck_1195_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_buckets_1152_);
lean_inc(v_size_1151_);
lean_dec(v_m_1148_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1195_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; uint64_t v___x_1157_; uint64_t v___x_1158_; uint64_t v___x_1159_; uint64_t v_fold_1160_; uint64_t v___x_1161_; uint64_t v___x_1162_; uint64_t v___x_1163_; size_t v___x_1164_; size_t v___x_1165_; size_t v___x_1166_; size_t v___x_1167_; size_t v___x_1168_; lean_object* v_bkt_1169_; uint8_t v___x_1170_; 
v___x_1156_ = lean_array_get_size(v_buckets_1152_);
v___x_1157_ = l_Lean_instHashableMVarId_hash(v_a_1149_);
v___x_1158_ = 32ULL;
v___x_1159_ = lean_uint64_shift_right(v___x_1157_, v___x_1158_);
v_fold_1160_ = lean_uint64_xor(v___x_1157_, v___x_1159_);
v___x_1161_ = 16ULL;
v___x_1162_ = lean_uint64_shift_right(v_fold_1160_, v___x_1161_);
v___x_1163_ = lean_uint64_xor(v_fold_1160_, v___x_1162_);
v___x_1164_ = lean_uint64_to_usize(v___x_1163_);
v___x_1165_ = lean_usize_of_nat(v___x_1156_);
v___x_1166_ = ((size_t)1ULL);
v___x_1167_ = lean_usize_sub(v___x_1165_, v___x_1166_);
v___x_1168_ = lean_usize_land(v___x_1164_, v___x_1167_);
v_bkt_1169_ = lean_array_uget_borrowed(v_buckets_1152_, v___x_1168_);
v___x_1170_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__7___redArg(v_a_1149_, v_bkt_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v_size_x27_1172_; lean_object* v___x_1173_; lean_object* v_buckets_x27_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1171_ = lean_unsigned_to_nat(1u);
v_size_x27_1172_ = lean_nat_add(v_size_1151_, v___x_1171_);
lean_dec(v_size_1151_);
lean_inc(v_bkt_1169_);
v___x_1173_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1173_, 0, v_a_1149_);
lean_ctor_set(v___x_1173_, 1, v_b_1150_);
lean_ctor_set(v___x_1173_, 2, v_bkt_1169_);
v_buckets_x27_1174_ = lean_array_uset(v_buckets_1152_, v___x_1168_, v___x_1173_);
v___x_1175_ = lean_unsigned_to_nat(4u);
v___x_1176_ = lean_nat_mul(v_size_x27_1172_, v___x_1175_);
v___x_1177_ = lean_unsigned_to_nat(3u);
v___x_1178_ = lean_nat_div(v___x_1176_, v___x_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_array_get_size(v_buckets_x27_1174_);
v___x_1180_ = lean_nat_dec_le(v___x_1178_, v___x_1179_);
lean_dec(v___x_1178_);
if (v___x_1180_ == 0)
{
lean_object* v_val_1181_; lean_object* v___x_1183_; 
v_val_1181_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__8___redArg(v_buckets_x27_1174_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v_val_1181_);
lean_ctor_set(v___x_1154_, 0, v_size_x27_1172_);
v___x_1183_ = v___x_1154_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_size_x27_1172_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_val_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
else
{
lean_object* v___x_1186_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v_buckets_x27_1174_);
lean_ctor_set(v___x_1154_, 0, v_size_x27_1172_);
v___x_1186_ = v___x_1154_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_size_x27_1172_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_buckets_x27_1174_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
else
{
lean_object* v___x_1188_; lean_object* v_buckets_x27_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
lean_inc(v_bkt_1169_);
v___x_1188_ = lean_box(0);
v_buckets_x27_1189_ = lean_array_uset(v_buckets_1152_, v___x_1168_, v___x_1188_);
v___x_1190_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__9___redArg(v_a_1149_, v_b_1150_, v_bkt_1169_);
v___x_1191_ = lean_array_uset(v_buckets_x27_1189_, v___x_1168_, v___x_1190_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v___x_1191_);
v___x_1193_ = v___x_1154_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_size_1151_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__7(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__6));
v___x_1210_ = l_Lean_stringToMessageData(v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3(lean_object* v_jp_1211_, lean_object* v_val_1212_, lean_object* v_goal_1213_, lean_object* v_info_1214_, lean_object* v___x_1215_, lean_object* v_scope_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1232_; 
lean_inc(v_jp_1211_);
v___x_1232_ = l_Lean_FVarId_getUserName___redArg(v_jp_1211_, v___y_1224_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1541_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1541_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1541_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
uint8_t v_useJP_1242_; 
v_useJP_1242_ = lean_ctor_get_uint8(v___y_1217_, sizeof(void*)*5);
if (v_useJP_1242_ == 0)
{
lean_dec(v_a_1233_);
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_goal_1213_);
lean_dec_ref(v_val_1212_);
lean_dec(v_jp_1211_);
goto v___jp_1237_;
}
else
{
uint8_t v___x_1243_; 
v___x_1243_ = l_Lean_Elab_Tactic_Do_isJP(v_a_1233_);
lean_dec(v_a_1233_);
if (v___x_1243_ == 0)
{
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_goal_1213_);
lean_dec_ref(v_val_1212_);
lean_dec(v_jp_1211_);
goto v___jp_1237_;
}
else
{
uint8_t v___x_1244_; 
v___x_1244_ = l_Lean_Expr_isLambda(v_val_1212_);
if (v___x_1244_ == 0)
{
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_goal_1213_);
lean_dec_ref(v_val_1212_);
lean_dec(v_jp_1211_);
goto v___jp_1237_;
}
else
{
lean_object* v___x_1245_; 
lean_del_object(v___x_1235_);
lean_inc(v_goal_1213_);
v___x_1245_ = l_Lean_MVarId_getType(v_goal_1213_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref_known(v___x_1245_, 1);
v___x_1247_ = l_Lean_Expr_cleanupAnnotations(v_a_1246_);
v___x_1248_ = l_Lean_Expr_isApp(v___x_1247_);
if (v___x_1248_ == 0)
{
lean_dec_ref(v___x_1247_);
lean_dec(v_a_1246_);
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_goal_1213_);
lean_dec_ref(v_val_1212_);
lean_dec(v_jp_1211_);
goto v___jp_1229_;
}
else
{
lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1249_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1247_);
lean_dec_ref(v___x_1247_);
v___x_1250_ = l_Lean_Expr_isApp(v___x_1249_);
if (v___x_1250_ == 0)
{
lean_dec_ref(v___x_1249_);
lean_dec(v_a_1246_);
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_goal_1213_);
lean_dec_ref(v_val_1212_);
lean_dec(v_jp_1211_);
goto v___jp_1229_;
}
else
{
lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1249_);
lean_dec_ref(v___x_1249_);
v___x_1252_ = l_Lean_Expr_isApp(v___x_1251_);
if (v___x_1252_ == 0)
{
lean_dec_ref(v___x_1251_);
lean_dec(v_a_1246_);
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_goal_1213_);
lean_dec_ref(v_val_1212_);
lean_dec(v_jp_1211_);
goto v___jp_1229_;
}
else
{
lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1251_);
v___x_1254_ = l_Lean_Expr_isApp(v___x_1253_);
if (v___x_1254_ == 0)
{
lean_dec_ref(v___x_1253_);
lean_dec_ref(v___x_1251_);
lean_dec(v_a_1246_);
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_goal_1213_);
lean_dec_ref(v_val_1212_);
lean_dec(v_jp_1211_);
goto v___jp_1229_;
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v___x_1255_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1253_);
v___x_1256_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__1));
v___x_1257_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f_spec__0___closed__2));
v___x_1258_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__2));
v___x_1259_ = l_Lean_Expr_isConstOf(v___x_1255_, v___x_1258_);
lean_dec_ref(v___x_1255_);
if (v___x_1259_ == 0)
{
lean_dec_ref(v___x_1253_);
lean_dec_ref(v___x_1251_);
lean_dec(v_a_1246_);
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_goal_1213_);
lean_dec_ref(v_val_1212_);
lean_dec(v_jp_1211_);
goto v___jp_1229_;
}
else
{
lean_object* v_arg_1260_; lean_object* v_arg_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v_arg_1260_ = lean_ctor_get(v___x_1251_, 1);
lean_inc_ref(v_arg_1260_);
lean_dec_ref(v___x_1251_);
v_arg_1261_ = lean_ctor_get(v___x_1253_, 1);
lean_inc_ref(v_arg_1261_);
lean_dec_ref(v___x_1253_);
lean_inc(v_jp_1211_);
v___x_1262_ = l_Lean_Expr_fvar___override(v_jp_1211_);
lean_inc_ref(v___x_1262_);
v___x_1263_ = l_Lean_Meta_Sym_inferType(v___x_1262_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc_n(v_a_1264_, 2);
lean_dec_ref_known(v___x_1263_, 1);
v___x_1265_ = l_Lean_Elab_Tactic_VCGen_WPApp_Prog(v_info_1214_);
v___x_1266_ = l_Lean_Elab_Tactic_Do_getNumJoinParams(v_a_1264_, v___x_1265_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
lean_dec_ref(v___x_1265_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v_instCL_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___x_1457_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___x_1499_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1266_, 1);
v___x_1457_ = l_Lean_Elab_Tactic_VCGen_WPApp_instAL(v_info_1214_);
lean_inc_ref(v___x_1457_);
v___x_1499_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_1457_, v___y_1225_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1501_; uint8_t v___x_1502_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1499_, 1);
v___x_1501_ = l_Lean_Expr_cleanupAnnotations(v_a_1500_);
lean_dec(v_a_1500_);
v___x_1502_ = l_Lean_Expr_isApp(v___x_1501_);
if (v___x_1502_ == 0)
{
lean_dec_ref(v___x_1501_);
v___y_1459_ = v___y_1217_;
v___y_1460_ = v___y_1218_;
v___y_1461_ = v___y_1219_;
v___y_1462_ = v___y_1220_;
v___y_1463_ = v___y_1221_;
v___y_1464_ = v___y_1222_;
v___y_1465_ = v___y_1223_;
v___y_1466_ = v___y_1224_;
v___y_1467_ = v___y_1225_;
v___y_1468_ = v___y_1226_;
v___y_1469_ = v___y_1227_;
goto v___jp_1458_;
}
else
{
lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___x_1503_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1501_);
v___x_1504_ = l_Lean_Expr_isApp(v___x_1503_);
if (v___x_1504_ == 0)
{
lean_dec_ref(v___x_1503_);
lean_dec_ref(v___x_1501_);
v___y_1459_ = v___y_1217_;
v___y_1460_ = v___y_1218_;
v___y_1461_ = v___y_1219_;
v___y_1462_ = v___y_1220_;
v___y_1463_ = v___y_1221_;
v___y_1464_ = v___y_1222_;
v___y_1465_ = v___y_1223_;
v___y_1466_ = v___y_1224_;
v___y_1467_ = v___y_1225_;
v___y_1468_ = v___y_1226_;
v___y_1469_ = v___y_1227_;
goto v___jp_1458_;
}
else
{
lean_object* v___x_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; 
v___x_1505_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1503_);
lean_dec_ref(v___x_1503_);
v___x_1506_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__6));
v___x_1507_ = l_Lean_Expr_isConstOf(v___x_1505_, v___x_1506_);
lean_dec_ref(v___x_1505_);
if (v___x_1507_ == 0)
{
lean_dec_ref(v___x_1501_);
v___y_1459_ = v___y_1217_;
v___y_1460_ = v___y_1218_;
v___y_1461_ = v___y_1219_;
v___y_1462_ = v___y_1220_;
v___y_1463_ = v___y_1221_;
v___y_1464_ = v___y_1222_;
v___y_1465_ = v___y_1223_;
v___y_1466_ = v___y_1224_;
v___y_1467_ = v___y_1225_;
v___y_1468_ = v___y_1226_;
v___y_1469_ = v___y_1227_;
goto v___jp_1458_;
}
else
{
lean_object* v_arg_1508_; 
lean_dec_ref(v___x_1457_);
v_arg_1508_ = lean_ctor_get(v___x_1501_, 1);
lean_inc_ref(v_arg_1508_);
lean_dec_ref(v___x_1501_);
v_instCL_1269_ = v_arg_1508_;
v___y_1270_ = v___y_1217_;
v___y_1271_ = v___y_1218_;
v___y_1272_ = v___y_1219_;
v___y_1273_ = v___y_1220_;
v___y_1274_ = v___y_1221_;
v___y_1275_ = v___y_1222_;
v___y_1276_ = v___y_1223_;
v___y_1277_ = v___y_1224_;
v___y_1278_ = v___y_1225_;
v___y_1279_ = v___y_1226_;
v___y_1280_ = v___y_1227_;
goto v___jp_1268_;
}
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_dec_ref(v___x_1457_);
lean_dec(v_a_1267_);
lean_dec(v_a_1264_);
lean_dec_ref(v___x_1262_);
lean_dec_ref(v_arg_1261_);
lean_dec_ref(v_arg_1260_);
lean_dec(v_a_1246_);
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_goal_1213_);
lean_dec_ref(v_val_1212_);
lean_dec(v_jp_1211_);
v_a_1509_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1499_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1499_);
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
v___jp_1268_:
{
lean_object* v_lctx_1281_; lean_object* v_localInstances_1282_; lean_object* v___f_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; lean_object* v___x_1286_; 
v_lctx_1281_ = lean_ctor_get(v___y_1277_, 2);
v_localInstances_1282_ = lean_ctor_get(v___y_1277_, 3);
lean_inc(v_a_1246_);
lean_inc_ref(v_localInstances_1282_);
lean_inc_ref(v_lctx_1281_);
lean_inc_ref(v_info_1214_);
v___f_1283_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__2___boxed), 26, 12);
lean_closure_set(v___f_1283_, 0, v_info_1214_);
lean_closure_set(v___f_1283_, 1, v_instCL_1269_);
lean_closure_set(v___f_1283_, 2, v___x_1256_);
lean_closure_set(v___f_1283_, 3, v___x_1257_);
lean_closure_set(v___f_1283_, 4, v_lctx_1281_);
lean_closure_set(v___f_1283_, 5, v_localInstances_1282_);
lean_closure_set(v___f_1283_, 6, v_a_1246_);
lean_closure_set(v___f_1283_, 7, v___x_1258_);
lean_closure_set(v___f_1283_, 8, v_arg_1261_);
lean_closure_set(v___f_1283_, 9, v_arg_1260_);
lean_closure_set(v___f_1283_, 10, v___x_1262_);
lean_closure_set(v___f_1283_, 11, v_val_1212_);
v___x_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1284_, 0, v_a_1267_);
v___x_1285_ = 0;
v___x_1286_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___redArg(v_a_1264_, v___x_1284_, v___f_1283_, v___x_1285_, v___x_1285_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1448_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1448_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1448_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
if (lean_obj_tag(v_a_1287_) == 1)
{
lean_object* v_val_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1443_; 
lean_del_object(v___x_1289_);
v_val_1291_ = lean_ctor_get(v_a_1287_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_a_1287_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1293_ = v_a_1287_;
v_isShared_1294_ = v_isSharedCheck_1443_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_val_1291_);
lean_dec(v_a_1287_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1443_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v_snd_1295_; lean_object* v_snd_1296_; lean_object* v_fst_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1441_; 
v_snd_1295_ = lean_ctor_get(v_val_1291_, 1);
lean_inc(v_snd_1295_);
v_snd_1296_ = lean_ctor_get(v_snd_1295_, 1);
lean_inc(v_snd_1296_);
v_fst_1297_ = lean_ctor_get(v_val_1291_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_val_1291_);
if (v_isSharedCheck_1441_ == 0)
{
lean_object* v_unused_1442_; 
v_unused_1442_ = lean_ctor_get(v_val_1291_, 1);
lean_dec(v_unused_1442_);
v___x_1299_ = v_val_1291_;
v_isShared_1300_ = v_isSharedCheck_1441_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_fst_1297_);
lean_dec(v_val_1291_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1441_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v_fst_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1439_; 
v_fst_1301_ = lean_ctor_get(v_snd_1295_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_snd_1295_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; 
v_unused_1440_ = lean_ctor_get(v_snd_1295_, 1);
lean_dec(v_unused_1440_);
v___x_1303_ = v_snd_1295_;
v_isShared_1304_ = v_isSharedCheck_1439_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_fst_1301_);
lean_dec(v_snd_1295_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1439_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v_fst_1305_; lean_object* v_snd_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1438_; 
v_fst_1305_ = lean_ctor_get(v_snd_1296_, 0);
v_snd_1306_ = lean_ctor_get(v_snd_1296_, 1);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_snd_1296_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1308_ = v_snd_1296_;
v_isShared_1309_ = v_isSharedCheck_1438_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_snd_1306_);
lean_inc(v_fst_1305_);
lean_dec(v_snd_1296_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1438_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1310_; 
lean_inc(v_goal_1213_);
v___x_1310_ = l_Lean_MVarId_getTag(v_goal_1213_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1312_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref_known(v___x_1310_, 1);
v___x_1312_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_snd_1306_, v_a_1311_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc_n(v_a_1313_, 2);
lean_dec_ref_known(v___x_1312_, 1);
v___x_1314_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__4));
lean_inc(v_fst_1305_);
v___x_1315_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__4___redArg(v___x_1314_, v_fst_1305_, v_a_1313_, v_a_1246_, v___x_1285_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1317_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1315_, 1);
v___x_1317_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_1213_, v_a_1316_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1317_, 1);
v___x_1319_ = lean_unsigned_to_nat(1u);
v___x_1320_ = l_Lean_Meta_Sym_introN(v_a_1318_, v___x_1319_, v___x_1243_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1397_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1397_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1397_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
if (lean_obj_tag(v_a_1321_) == 1)
{
lean_object* v_newDecls_1325_; lean_object* v_mvarId_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1390_; 
lean_dec(v_fst_1305_);
v_newDecls_1325_ = lean_ctor_get(v_a_1321_, 0);
v_mvarId_1326_ = lean_ctor_get(v_a_1321_, 1);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_a_1321_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1328_ = v_a_1321_;
v_isShared_1329_ = v_isSharedCheck_1390_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_mvarId_1326_);
lean_inc(v_newDecls_1325_);
lean_dec(v_a_1321_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1390_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v_excessArgs_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v_specBackwardRuleCache_1338_; lean_object* v_splitBackwardRuleCache_1339_; lean_object* v_latticeBackwardRuleCache_1340_; lean_object* v_frameBackwardRuleCache_1341_; lean_object* v_frameDB_1342_; lean_object* v_invariants_1343_; lean_object* v_vcs_1344_; lean_object* v_simpState_1345_; lean_object* v_fuel_1346_; lean_object* v_inlineHandledInvariants_1347_; lean_object* v_pendingJoinPoints_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1389_; 
v_excessArgs_1330_ = lean_ctor_get(v_info_1214_, 3);
lean_inc_ref(v_excessArgs_1330_);
lean_dec_ref(v_info_1214_);
v___x_1331_ = lean_unsigned_to_nat(0u);
v___x_1332_ = lean_array_get(v___x_1215_, v_newDecls_1325_, v___x_1331_);
lean_dec_ref(v_newDecls_1325_);
v___x_1333_ = l_Lean_Expr_fvar___override(v___x_1332_);
v___x_1334_ = l_Lean_Expr_mvarId_x21(v_a_1313_);
lean_dec(v_a_1313_);
v___x_1335_ = lean_array_get_size(v_excessArgs_1330_);
lean_dec_ref(v_excessArgs_1330_);
lean_inc(v___x_1334_);
v___x_1336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1333_);
lean_ctor_set(v___x_1336_, 1, v_fst_1301_);
lean_ctor_set(v___x_1336_, 2, v_fst_1297_);
lean_ctor_set(v___x_1336_, 3, v___x_1334_);
lean_ctor_set(v___x_1336_, 4, v___x_1335_);
v___x_1337_ = lean_st_ref_take(v___y_1271_);
v_specBackwardRuleCache_1338_ = lean_ctor_get(v___x_1337_, 0);
v_splitBackwardRuleCache_1339_ = lean_ctor_get(v___x_1337_, 1);
v_latticeBackwardRuleCache_1340_ = lean_ctor_get(v___x_1337_, 2);
v_frameBackwardRuleCache_1341_ = lean_ctor_get(v___x_1337_, 3);
v_frameDB_1342_ = lean_ctor_get(v___x_1337_, 4);
v_invariants_1343_ = lean_ctor_get(v___x_1337_, 5);
v_vcs_1344_ = lean_ctor_get(v___x_1337_, 6);
v_simpState_1345_ = lean_ctor_get(v___x_1337_, 7);
v_fuel_1346_ = lean_ctor_get(v___x_1337_, 8);
v_inlineHandledInvariants_1347_ = lean_ctor_get(v___x_1337_, 9);
v_pendingJoinPoints_1348_ = lean_ctor_get(v___x_1337_, 10);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1350_ = v___x_1337_;
v_isShared_1351_ = v_isSharedCheck_1389_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_pendingJoinPoints_1348_);
lean_inc(v_inlineHandledInvariants_1347_);
lean_inc(v_fuel_1346_);
lean_inc(v_simpState_1345_);
lean_inc(v_vcs_1344_);
lean_inc(v_invariants_1343_);
lean_inc(v_frameDB_1342_);
lean_inc(v_frameBackwardRuleCache_1341_);
lean_inc(v_latticeBackwardRuleCache_1340_);
lean_inc(v_splitBackwardRuleCache_1339_);
lean_inc(v_specBackwardRuleCache_1338_);
lean_dec(v___x_1337_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1389_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1352_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__5));
lean_inc_ref(v___x_1336_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 1, v___x_1352_);
lean_ctor_set(v___x_1308_, 0, v___x_1336_);
v___x_1354_ = v___x_1308_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
lean_inc(v___x_1334_);
v___x_1355_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5___redArg(v_pendingJoinPoints_1348_, v___x_1334_, v___x_1354_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 10, v___x_1355_);
v___x_1357_ = v___x_1350_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_specBackwardRuleCache_1338_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_splitBackwardRuleCache_1339_);
lean_ctor_set(v_reuseFailAlloc_1387_, 2, v_latticeBackwardRuleCache_1340_);
lean_ctor_set(v_reuseFailAlloc_1387_, 3, v_frameBackwardRuleCache_1341_);
lean_ctor_set(v_reuseFailAlloc_1387_, 4, v_frameDB_1342_);
lean_ctor_set(v_reuseFailAlloc_1387_, 5, v_invariants_1343_);
lean_ctor_set(v_reuseFailAlloc_1387_, 6, v_vcs_1344_);
lean_ctor_set(v_reuseFailAlloc_1387_, 7, v_simpState_1345_);
lean_ctor_set(v_reuseFailAlloc_1387_, 8, v_fuel_1346_);
lean_ctor_set(v_reuseFailAlloc_1387_, 9, v_inlineHandledInvariants_1347_);
lean_ctor_set(v_reuseFailAlloc_1387_, 10, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; lean_object* v_specs_1359_; lean_object* v_lastLiftedPre_x3f_1360_; lean_object* v_nextDeclIdx_1361_; lean_object* v_joinPoints_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1386_; 
v___x_1358_ = lean_st_ref_put(v___y_1271_, v___x_1357_);
v_specs_1359_ = lean_ctor_get(v_scope_1216_, 0);
v_lastLiftedPre_x3f_1360_ = lean_ctor_get(v_scope_1216_, 1);
v_nextDeclIdx_1361_ = lean_ctor_get(v_scope_1216_, 2);
v_joinPoints_1362_ = lean_ctor_get(v_scope_1216_, 3);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_scope_1216_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1364_ = v_scope_1216_;
v_isShared_1365_ = v_isSharedCheck_1386_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_joinPoints_1362_);
lean_inc(v_nextDeclIdx_1361_);
lean_inc(v_lastLiftedPre_x3f_1360_);
lean_inc(v_specs_1359_);
lean_dec(v_scope_1216_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1386_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1366_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_jp_1211_, v___x_1336_, v_joinPoints_1362_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 3, v___x_1366_);
v___x_1368_ = v___x_1364_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_specs_1359_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_lastLiftedPre_x3f_1360_);
lean_ctor_set(v_reuseFailAlloc_1385_, 2, v_nextDeclIdx_1361_);
lean_ctor_set(v_reuseFailAlloc_1385_, 3, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1369_ = lean_box(0);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 1, v___x_1369_);
lean_ctor_set(v___x_1328_, 0, v___x_1334_);
v___x_1371_ = v___x_1328_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1373_; 
if (v_isShared_1300_ == 0)
{
lean_ctor_set_tag(v___x_1299_, 1);
lean_ctor_set(v___x_1299_, 1, v___x_1371_);
lean_ctor_set(v___x_1299_, 0, v_mvarId_1326_);
v___x_1373_ = v___x_1299_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_mvarId_1326_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1375_; 
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 1, v___x_1373_);
lean_ctor_set(v___x_1303_, 0, v___x_1368_);
v___x_1375_ = v___x_1303_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1377_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1375_);
v___x_1377_ = v___x_1293_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
lean_object* v___x_1379_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1377_);
v___x_1379_ = v___x_1323_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
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
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
lean_del_object(v___x_1323_);
lean_dec(v_a_1321_);
lean_dec(v_a_1313_);
lean_del_object(v___x_1308_);
lean_del_object(v___x_1303_);
lean_dec(v_fst_1301_);
lean_dec(v_fst_1297_);
lean_del_object(v___x_1293_);
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_jp_1211_);
v___x_1391_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__7, &l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__7);
v___x_1392_ = l_Lean_indentExpr(v_fst_1305_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set_tag(v___x_1299_, 7);
lean_ctor_set(v___x_1299_, 1, v___x_1392_);
lean_ctor_set(v___x_1299_, 0, v___x_1391_);
v___x_1394_ = v___x_1299_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___redArg(v___x_1394_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1395_;
}
}
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec(v_a_1313_);
lean_del_object(v___x_1308_);
lean_dec(v_fst_1305_);
lean_del_object(v___x_1303_);
lean_dec(v_fst_1301_);
lean_del_object(v___x_1299_);
lean_dec(v_fst_1297_);
lean_del_object(v___x_1293_);
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_jp_1211_);
v_a_1398_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1320_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1320_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
lean_dec(v_a_1313_);
lean_del_object(v___x_1308_);
lean_dec(v_fst_1305_);
lean_del_object(v___x_1303_);
lean_dec(v_fst_1301_);
lean_del_object(v___x_1299_);
lean_dec(v_fst_1297_);
lean_del_object(v___x_1293_);
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_jp_1211_);
v_a_1406_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1317_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1317_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
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
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec(v_a_1313_);
lean_del_object(v___x_1308_);
lean_dec(v_fst_1305_);
lean_del_object(v___x_1303_);
lean_dec(v_fst_1301_);
lean_del_object(v___x_1299_);
lean_dec(v_fst_1297_);
lean_del_object(v___x_1293_);
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_goal_1213_);
lean_dec(v_jp_1211_);
v_a_1414_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1315_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1315_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_del_object(v___x_1308_);
lean_dec(v_fst_1305_);
lean_del_object(v___x_1303_);
lean_dec(v_fst_1301_);
lean_del_object(v___x_1299_);
lean_dec(v_fst_1297_);
lean_del_object(v___x_1293_);
lean_dec(v_a_1246_);
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_goal_1213_);
lean_dec(v_jp_1211_);
v_a_1422_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1312_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1312_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_del_object(v___x_1308_);
lean_dec(v_snd_1306_);
lean_dec(v_fst_1305_);
lean_del_object(v___x_1303_);
lean_dec(v_fst_1301_);
lean_del_object(v___x_1299_);
lean_dec(v_fst_1297_);
lean_del_object(v___x_1293_);
lean_dec(v_a_1246_);
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_goal_1213_);
lean_dec(v_jp_1211_);
v_a_1430_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1310_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1310_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
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
lean_object* v___x_1444_; lean_object* v___x_1446_; 
lean_dec(v_a_1287_);
lean_dec(v_a_1246_);
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_goal_1213_);
lean_dec(v_jp_1211_);
v___x_1444_ = lean_box(0);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1444_);
v___x_1446_ = v___x_1289_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
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
lean_dec(v_a_1246_);
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_goal_1213_);
lean_dec(v_jp_1211_);
v_a_1449_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1286_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1286_);
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
v___jp_1458_:
{
lean_object* v___x_1470_; 
lean_inc_ref(v___x_1457_);
v___x_1470_ = l_Lean_Meta_Sym_inferType(v___x_1457_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
v___x_1472_ = l_Lean_Expr_getAppFn(v_a_1471_);
lean_dec(v_a_1471_);
v___x_1473_ = l_Lean_Expr_constLevels_x21(v___x_1472_);
lean_dec_ref(v___x_1472_);
v___x_1474_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_baseInstance_x3f___closed__4));
v___x_1475_ = l_Lean_mkConst(v___x_1474_, v___x_1473_);
v___x_1476_ = l_Lean_Elab_Tactic_VCGen_WPApp_Pred(v_info_1214_);
v___x_1477_ = lean_unsigned_to_nat(2u);
v___x_1478_ = lean_mk_empty_array_with_capacity(v___x_1477_);
v___x_1479_ = lean_array_push(v___x_1478_, v___x_1476_);
v___x_1480_ = lean_array_push(v___x_1479_, v___x_1457_);
v___x_1481_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0(v___x_1475_, v___x_1480_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec_ref(v___x_1480_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref_known(v___x_1481_, 1);
v_instCL_1269_ = v_a_1482_;
v___y_1270_ = v___y_1459_;
v___y_1271_ = v___y_1460_;
v___y_1272_ = v___y_1461_;
v___y_1273_ = v___y_1462_;
v___y_1274_ = v___y_1463_;
v___y_1275_ = v___y_1464_;
v___y_1276_ = v___y_1465_;
v___y_1277_ = v___y_1466_;
v___y_1278_ = v___y_1467_;
v___y_1279_ = v___y_1468_;
v___y_1280_ = v___y_1469_;
goto v___jp_1268_;
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec(v_a_1267_);
lean_dec(v_a_1264_);
lean_dec_ref(v___x_1262_);
lean_dec_ref(v_arg_1261_);
lean_dec_ref(v_arg_1260_);
lean_dec(v_a_1246_);
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_goal_1213_);
lean_dec_ref(v_val_1212_);
lean_dec(v_jp_1211_);
v_a_1483_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1481_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1481_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec_ref(v___x_1457_);
lean_dec(v_a_1267_);
lean_dec(v_a_1264_);
lean_dec_ref(v___x_1262_);
lean_dec_ref(v_arg_1261_);
lean_dec_ref(v_arg_1260_);
lean_dec(v_a_1246_);
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_goal_1213_);
lean_dec_ref(v_val_1212_);
lean_dec(v_jp_1211_);
v_a_1491_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1470_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1470_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
lean_dec(v_a_1264_);
lean_dec_ref(v___x_1262_);
lean_dec_ref(v_arg_1261_);
lean_dec_ref(v_arg_1260_);
lean_dec(v_a_1246_);
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_goal_1213_);
lean_dec_ref(v_val_1212_);
lean_dec(v_jp_1211_);
v_a_1517_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v___x_1266_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1266_);
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
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec_ref(v___x_1262_);
lean_dec_ref(v_arg_1261_);
lean_dec_ref(v_arg_1260_);
lean_dec(v_a_1246_);
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_goal_1213_);
lean_dec_ref(v_val_1212_);
lean_dec(v_jp_1211_);
v_a_1525_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1263_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1263_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
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
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_goal_1213_);
lean_dec_ref(v_val_1212_);
lean_dec(v_jp_1211_);
v_a_1533_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1245_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1245_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
}
}
v___jp_1237_:
{
lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1238_ = lean_box(0);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1238_);
v___x_1240_ = v___x_1235_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
lean_dec_ref(v_scope_1216_);
lean_dec_ref(v_info_1214_);
lean_dec(v_goal_1213_);
lean_dec_ref(v_val_1212_);
lean_dec(v_jp_1211_);
v_a_1542_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1232_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1232_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
v___jp_1229_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_box(0);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___boxed(lean_object** _args){
lean_object* v_jp_1550_ = _args[0];
lean_object* v_val_1551_ = _args[1];
lean_object* v_goal_1552_ = _args[2];
lean_object* v_info_1553_ = _args[3];
lean_object* v___x_1554_ = _args[4];
lean_object* v_scope_1555_ = _args[5];
lean_object* v___y_1556_ = _args[6];
lean_object* v___y_1557_ = _args[7];
lean_object* v___y_1558_ = _args[8];
lean_object* v___y_1559_ = _args[9];
lean_object* v___y_1560_ = _args[10];
lean_object* v___y_1561_ = _args[11];
lean_object* v___y_1562_ = _args[12];
lean_object* v___y_1563_ = _args[13];
lean_object* v___y_1564_ = _args[14];
lean_object* v___y_1565_ = _args[15];
lean_object* v___y_1566_ = _args[16];
lean_object* v___y_1567_ = _args[17];
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3(v_jp_1550_, v_val_1551_, v_goal_1552_, v_info_1553_, v___x_1554_, v_scope_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___x_1554_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint(lean_object* v_scope_1569_, lean_object* v_goal_1570_, lean_object* v_jp_1571_, lean_object* v_val_1572_, lean_object* v_info_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v___x_1586_; lean_object* v___f_1587_; lean_object* v___x_1588_; 
v___x_1586_ = lean_box(0);
lean_inc(v_goal_1570_);
v___f_1587_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___boxed), 18, 6);
lean_closure_set(v___f_1587_, 0, v_jp_1571_);
lean_closure_set(v___f_1587_, 1, v_val_1572_);
lean_closure_set(v___f_1587_, 2, v_goal_1570_);
lean_closure_set(v___f_1587_, 3, v_info_1573_);
lean_closure_set(v___f_1587_, 4, v___x_1586_);
lean_closure_set(v___f_1587_, 5, v_scope_1569_);
v___x_1588_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg(v_goal_1570_, v___f_1587_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint___boxed(lean_object** _args){
lean_object* v_scope_1589_ = _args[0];
lean_object* v_goal_1590_ = _args[1];
lean_object* v_jp_1591_ = _args[2];
lean_object* v_val_1592_ = _args[3];
lean_object* v_info_1593_ = _args[4];
lean_object* v_a_1594_ = _args[5];
lean_object* v_a_1595_ = _args[6];
lean_object* v_a_1596_ = _args[7];
lean_object* v_a_1597_ = _args[8];
lean_object* v_a_1598_ = _args[9];
lean_object* v_a_1599_ = _args[10];
lean_object* v_a_1600_ = _args[11];
lean_object* v_a_1601_ = _args[12];
lean_object* v_a_1602_ = _args[13];
lean_object* v_a_1603_ = _args[14];
lean_object* v_a_1604_ = _args[15];
lean_object* v_a_1605_ = _args[16];
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_Elab_Tactic_VCGen_registerJoinPoint(v_scope_1589_, v_goal_1590_, v_jp_1591_, v_val_1592_, v_info_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
lean_dec(v_a_1598_);
lean_dec_ref(v_a_1597_);
lean_dec(v_a_1596_);
lean_dec(v_a_1595_);
lean_dec_ref(v_a_1594_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2(lean_object* v_00_u03b1_1607_, lean_object* v_msg_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___redArg(v_msg_1608_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___boxed(lean_object* v_00_u03b1_1622_, lean_object* v_msg_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2(v_00_u03b1_1622_, v_msg_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5(lean_object* v_00_u03b2_1637_, lean_object* v_m_1638_, lean_object* v_a_1639_, lean_object* v_b_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5___redArg(v_m_1638_, v_a_1639_, v_b_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0_spec__0_spec__5(lean_object* v_f_1642_, lean_object* v_a_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0_spec__0_spec__5___redArg(v_f_1642_, v_a_1643_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0_spec__0_spec__5___boxed(lean_object* v_f_1657_, lean_object* v_a_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0_spec__0_spec__5(v_f_1657_, v_a_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
return v_res_1671_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__7(lean_object* v_00_u03b2_1672_, lean_object* v_a_1673_, lean_object* v_x_1674_){
_start:
{
uint8_t v___x_1675_; 
v___x_1675_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__7___redArg(v_a_1673_, v_x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__7___boxed(lean_object* v_00_u03b2_1676_, lean_object* v_a_1677_, lean_object* v_x_1678_){
_start:
{
uint8_t v_res_1679_; lean_object* v_r_1680_; 
v_res_1679_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__7(v_00_u03b2_1676_, v_a_1677_, v_x_1678_);
lean_dec(v_x_1678_);
lean_dec(v_a_1677_);
v_r_1680_ = lean_box(v_res_1679_);
return v_r_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__8(lean_object* v_00_u03b2_1681_, lean_object* v_data_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__8___redArg(v_data_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__9(lean_object* v_00_u03b2_1684_, lean_object* v_a_1685_, lean_object* v_b_1686_, lean_object* v_x_1687_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__9___redArg(v_a_1685_, v_b_1686_, v_x_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__8_spec__11(lean_object* v_00_u03b2_1689_, lean_object* v_i_1690_, lean_object* v_source_1691_, lean_object* v_target_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__8_spec__11___redArg(v_i_1690_, v_source_1691_, v_target_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_1694_, lean_object* v_x_1695_, lean_object* v_x_1696_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__8_spec__11_spec__12___redArg(v_x_1695_, v_x_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_, lean_object* v_x_1701_){
_start:
{
lean_object* v_ks_1702_; lean_object* v_vs_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1727_; 
v_ks_1702_ = lean_ctor_get(v_x_1698_, 0);
v_vs_1703_ = lean_ctor_get(v_x_1698_, 1);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1705_ = v_x_1698_;
v_isShared_1706_ = v_isSharedCheck_1727_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_vs_1703_);
lean_inc(v_ks_1702_);
lean_dec(v_x_1698_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1727_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1707_; uint8_t v___x_1708_; 
v___x_1707_ = lean_array_get_size(v_ks_1702_);
v___x_1708_ = lean_nat_dec_lt(v_x_1699_, v___x_1707_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1712_; 
lean_dec(v_x_1699_);
v___x_1709_ = lean_array_push(v_ks_1702_, v_x_1700_);
v___x_1710_ = lean_array_push(v_vs_1703_, v_x_1701_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 1, v___x_1710_);
lean_ctor_set(v___x_1705_, 0, v___x_1709_);
v___x_1712_ = v___x_1705_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
else
{
lean_object* v_k_x27_1714_; uint8_t v___x_1715_; 
v_k_x27_1714_ = lean_array_fget_borrowed(v_ks_1702_, v_x_1699_);
v___x_1715_ = l_Lean_instBEqMVarId_beq(v_x_1700_, v_k_x27_1714_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1717_; 
if (v_isShared_1706_ == 0)
{
v___x_1717_ = v___x_1705_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_ks_1702_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_vs_1703_);
v___x_1717_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = lean_unsigned_to_nat(1u);
v___x_1719_ = lean_nat_add(v_x_1699_, v___x_1718_);
lean_dec(v_x_1699_);
v_x_1698_ = v___x_1717_;
v_x_1699_ = v___x_1719_;
goto _start;
}
}
else
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1725_; 
v___x_1722_ = lean_array_fset(v_ks_1702_, v_x_1699_, v_x_1700_);
v___x_1723_ = lean_array_fset(v_vs_1703_, v_x_1699_, v_x_1701_);
lean_dec(v_x_1699_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 1, v___x_1723_);
lean_ctor_set(v___x_1705_, 0, v___x_1722_);
v___x_1725_ = v___x_1705_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v___x_1723_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_n_1728_, lean_object* v_k_1729_, lean_object* v_v_1730_){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = lean_unsigned_to_nat(0u);
v___x_1732_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(v_n_1728_, v___x_1731_, v_k_1729_, v_v_1730_);
return v___x_1732_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_x_1734_, size_t v_x_1735_, size_t v_x_1736_, lean_object* v_x_1737_, lean_object* v_x_1738_){
_start:
{
if (lean_obj_tag(v_x_1734_) == 0)
{
lean_object* v_es_1739_; size_t v___x_1740_; size_t v___x_1741_; lean_object* v_j_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
v_es_1739_ = lean_ctor_get(v_x_1734_, 0);
v___x_1740_ = ((size_t)31ULL);
v___x_1741_ = lean_usize_land(v_x_1735_, v___x_1740_);
v_j_1742_ = lean_usize_to_nat(v___x_1741_);
v___x_1743_ = lean_array_get_size(v_es_1739_);
v___x_1744_ = lean_nat_dec_lt(v_j_1742_, v___x_1743_);
if (v___x_1744_ == 0)
{
lean_dec(v_j_1742_);
lean_dec(v_x_1738_);
lean_dec(v_x_1737_);
return v_x_1734_;
}
else
{
lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1783_; 
lean_inc_ref(v_es_1739_);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_x_1734_);
if (v_isSharedCheck_1783_ == 0)
{
lean_object* v_unused_1784_; 
v_unused_1784_ = lean_ctor_get(v_x_1734_, 0);
lean_dec(v_unused_1784_);
v___x_1746_ = v_x_1734_;
v_isShared_1747_ = v_isSharedCheck_1783_;
goto v_resetjp_1745_;
}
else
{
lean_dec(v_x_1734_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1783_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v_v_1748_; lean_object* v___x_1749_; lean_object* v_xs_x27_1750_; lean_object* v___y_1752_; 
v_v_1748_ = lean_array_fget(v_es_1739_, v_j_1742_);
v___x_1749_ = lean_box(0);
v_xs_x27_1750_ = lean_array_fset(v_es_1739_, v_j_1742_, v___x_1749_);
switch(lean_obj_tag(v_v_1748_))
{
case 0:
{
lean_object* v_key_1757_; lean_object* v_val_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1768_; 
v_key_1757_ = lean_ctor_get(v_v_1748_, 0);
v_val_1758_ = lean_ctor_get(v_v_1748_, 1);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_v_1748_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1760_ = v_v_1748_;
v_isShared_1761_ = v_isSharedCheck_1768_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_val_1758_);
lean_inc(v_key_1757_);
lean_dec(v_v_1748_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1768_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
uint8_t v___x_1762_; 
v___x_1762_ = l_Lean_instBEqMVarId_beq(v_x_1737_, v_key_1757_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
lean_del_object(v___x_1760_);
v___x_1763_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1757_, v_val_1758_, v_x_1737_, v_x_1738_);
v___x_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1763_);
v___y_1752_ = v___x_1764_;
goto v___jp_1751_;
}
else
{
lean_object* v___x_1766_; 
lean_dec(v_val_1758_);
lean_dec(v_key_1757_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 1, v_x_1738_);
lean_ctor_set(v___x_1760_, 0, v_x_1737_);
v___x_1766_ = v___x_1760_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_x_1737_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_x_1738_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
v___y_1752_ = v___x_1766_;
goto v___jp_1751_;
}
}
}
}
case 1:
{
lean_object* v_node_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1781_; 
v_node_1769_ = lean_ctor_get(v_v_1748_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v_v_1748_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1771_ = v_v_1748_;
v_isShared_1772_ = v_isSharedCheck_1781_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_node_1769_);
lean_dec(v_v_1748_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1781_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
size_t v___x_1773_; size_t v___x_1774_; size_t v___x_1775_; size_t v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1773_ = ((size_t)5ULL);
v___x_1774_ = lean_usize_shift_right(v_x_1735_, v___x_1773_);
v___x_1775_ = ((size_t)1ULL);
v___x_1776_ = lean_usize_add(v_x_1736_, v___x_1775_);
v___x_1777_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2___redArg(v_node_1769_, v___x_1774_, v___x_1776_, v_x_1737_, v_x_1738_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1777_);
v___x_1779_ = v___x_1771_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
v___y_1752_ = v___x_1779_;
goto v___jp_1751_;
}
}
}
default: 
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1782_, 0, v_x_1737_);
lean_ctor_set(v___x_1782_, 1, v_x_1738_);
v___y_1752_ = v___x_1782_;
goto v___jp_1751_;
}
}
v___jp_1751_:
{
lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1753_ = lean_array_fset(v_xs_x27_1750_, v_j_1742_, v___y_1752_);
lean_dec(v_j_1742_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v___x_1753_);
v___x_1755_ = v___x_1746_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
}
else
{
lean_object* v_ks_1785_; lean_object* v_vs_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1804_; 
v_ks_1785_ = lean_ctor_get(v_x_1734_, 0);
v_vs_1786_ = lean_ctor_get(v_x_1734_, 1);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_x_1734_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1788_ = v_x_1734_;
v_isShared_1789_ = v_isSharedCheck_1804_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_vs_1786_);
lean_inc(v_ks_1785_);
lean_dec(v_x_1734_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1804_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_ks_1785_);
lean_ctor_set(v_reuseFailAlloc_1803_, 1, v_vs_1786_);
v___x_1791_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
lean_object* v_newNode_1792_; size_t v___x_1793_; uint8_t v___x_1794_; 
v_newNode_1792_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__4___redArg(v___x_1791_, v_x_1737_, v_x_1738_);
v___x_1793_ = ((size_t)7ULL);
v___x_1794_ = lean_usize_dec_le(v___x_1793_, v_x_1736_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1795_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1792_);
v___x_1796_ = lean_unsigned_to_nat(4u);
v___x_1797_ = lean_nat_dec_lt(v___x_1795_, v___x_1796_);
lean_dec(v___x_1795_);
if (v___x_1797_ == 0)
{
lean_object* v_ks_1798_; lean_object* v_vs_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v_ks_1798_ = lean_ctor_get(v_newNode_1792_, 0);
lean_inc_ref(v_ks_1798_);
v_vs_1799_ = lean_ctor_get(v_newNode_1792_, 1);
lean_inc_ref(v_vs_1799_);
lean_dec_ref(v_newNode_1792_);
v___x_1800_ = lean_unsigned_to_nat(0u);
v___x_1801_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_1802_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__5___redArg(v_x_1736_, v_ks_1798_, v_vs_1799_, v___x_1800_, v___x_1801_);
lean_dec_ref(v_vs_1799_);
lean_dec_ref(v_ks_1798_);
return v___x_1802_;
}
else
{
return v_newNode_1792_;
}
}
else
{
return v_newNode_1792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__5___redArg(size_t v_depth_1805_, lean_object* v_keys_1806_, lean_object* v_vals_1807_, lean_object* v_i_1808_, lean_object* v_entries_1809_){
_start:
{
lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = lean_array_get_size(v_keys_1806_);
v___x_1811_ = lean_nat_dec_lt(v_i_1808_, v___x_1810_);
if (v___x_1811_ == 0)
{
lean_dec(v_i_1808_);
return v_entries_1809_;
}
else
{
lean_object* v_k_1812_; lean_object* v_v_1813_; uint64_t v___x_1814_; size_t v_h_1815_; size_t v___x_1816_; lean_object* v___x_1817_; size_t v___x_1818_; size_t v___x_1819_; size_t v___x_1820_; size_t v_h_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v_k_1812_ = lean_array_fget_borrowed(v_keys_1806_, v_i_1808_);
v_v_1813_ = lean_array_fget_borrowed(v_vals_1807_, v_i_1808_);
v___x_1814_ = l_Lean_instHashableMVarId_hash(v_k_1812_);
v_h_1815_ = lean_uint64_to_usize(v___x_1814_);
v___x_1816_ = ((size_t)5ULL);
v___x_1817_ = lean_unsigned_to_nat(1u);
v___x_1818_ = ((size_t)1ULL);
v___x_1819_ = lean_usize_sub(v_depth_1805_, v___x_1818_);
v___x_1820_ = lean_usize_mul(v___x_1816_, v___x_1819_);
v_h_1821_ = lean_usize_shift_right(v_h_1815_, v___x_1820_);
v___x_1822_ = lean_nat_add(v_i_1808_, v___x_1817_);
lean_dec(v_i_1808_);
lean_inc(v_v_1813_);
lean_inc(v_k_1812_);
v___x_1823_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2___redArg(v_entries_1809_, v_h_1821_, v_depth_1805_, v_k_1812_, v_v_1813_);
v_i_1808_ = v___x_1822_;
v_entries_1809_ = v___x_1823_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1825_, lean_object* v_keys_1826_, lean_object* v_vals_1827_, lean_object* v_i_1828_, lean_object* v_entries_1829_){
_start:
{
size_t v_depth_boxed_1830_; lean_object* v_res_1831_; 
v_depth_boxed_1830_ = lean_unbox_usize(v_depth_1825_);
lean_dec(v_depth_1825_);
v_res_1831_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1830_, v_keys_1826_, v_vals_1827_, v_i_1828_, v_entries_1829_);
lean_dec_ref(v_vals_1827_);
lean_dec_ref(v_keys_1826_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_1832_, lean_object* v_x_1833_, lean_object* v_x_1834_, lean_object* v_x_1835_, lean_object* v_x_1836_){
_start:
{
size_t v_x_15839__boxed_1837_; size_t v_x_15840__boxed_1838_; lean_object* v_res_1839_; 
v_x_15839__boxed_1837_ = lean_unbox_usize(v_x_1833_);
lean_dec(v_x_1833_);
v_x_15840__boxed_1838_ = lean_unbox_usize(v_x_1834_);
lean_dec(v_x_1834_);
v_res_1839_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2___redArg(v_x_1832_, v_x_15839__boxed_1837_, v_x_15840__boxed_1838_, v_x_1835_, v_x_1836_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1___redArg(lean_object* v_x_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_){
_start:
{
uint64_t v___x_1843_; size_t v___x_1844_; size_t v___x_1845_; lean_object* v___x_1846_; 
v___x_1843_ = l_Lean_instHashableMVarId_hash(v_x_1841_);
v___x_1844_ = lean_uint64_to_usize(v___x_1843_);
v___x_1845_ = ((size_t)1ULL);
v___x_1846_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2___redArg(v_x_1840_, v___x_1844_, v___x_1845_, v_x_1841_, v_x_1842_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg(lean_object* v_mvarId_1847_, lean_object* v_val_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v___x_1851_; lean_object* v_mctx_1852_; lean_object* v_cache_1853_; lean_object* v_zetaDeltaFVarIds_1854_; lean_object* v_postponed_1855_; lean_object* v_diag_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1886_; 
v___x_1851_ = lean_st_ref_take(v___y_1849_);
v_mctx_1852_ = lean_ctor_get(v___x_1851_, 0);
v_cache_1853_ = lean_ctor_get(v___x_1851_, 1);
v_zetaDeltaFVarIds_1854_ = lean_ctor_get(v___x_1851_, 2);
v_postponed_1855_ = lean_ctor_get(v___x_1851_, 3);
v_diag_1856_ = lean_ctor_get(v___x_1851_, 4);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1858_ = v___x_1851_;
v_isShared_1859_ = v_isSharedCheck_1886_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_diag_1856_);
lean_inc(v_postponed_1855_);
lean_inc(v_zetaDeltaFVarIds_1854_);
lean_inc(v_cache_1853_);
lean_inc(v_mctx_1852_);
lean_dec(v___x_1851_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1886_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v_depth_1860_; lean_object* v_levelAssignDepth_1861_; lean_object* v_lmvarCounter_1862_; lean_object* v_mvarCounter_1863_; lean_object* v_lDecls_1864_; lean_object* v_decls_1865_; lean_object* v_userNames_1866_; lean_object* v_lAssignment_1867_; lean_object* v_eAssignment_1868_; lean_object* v_dAssignment_1869_; lean_object* v_instanceTypedMVars_1870_; lean_object* v_synthNormMemo_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1885_; 
v_depth_1860_ = lean_ctor_get(v_mctx_1852_, 0);
v_levelAssignDepth_1861_ = lean_ctor_get(v_mctx_1852_, 1);
v_lmvarCounter_1862_ = lean_ctor_get(v_mctx_1852_, 2);
v_mvarCounter_1863_ = lean_ctor_get(v_mctx_1852_, 3);
v_lDecls_1864_ = lean_ctor_get(v_mctx_1852_, 4);
v_decls_1865_ = lean_ctor_get(v_mctx_1852_, 5);
v_userNames_1866_ = lean_ctor_get(v_mctx_1852_, 6);
v_lAssignment_1867_ = lean_ctor_get(v_mctx_1852_, 7);
v_eAssignment_1868_ = lean_ctor_get(v_mctx_1852_, 8);
v_dAssignment_1869_ = lean_ctor_get(v_mctx_1852_, 9);
v_instanceTypedMVars_1870_ = lean_ctor_get(v_mctx_1852_, 10);
v_synthNormMemo_1871_ = lean_ctor_get(v_mctx_1852_, 11);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_mctx_1852_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1873_ = v_mctx_1852_;
v_isShared_1874_ = v_isSharedCheck_1885_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_synthNormMemo_1871_);
lean_inc(v_instanceTypedMVars_1870_);
lean_inc(v_dAssignment_1869_);
lean_inc(v_eAssignment_1868_);
lean_inc(v_lAssignment_1867_);
lean_inc(v_userNames_1866_);
lean_inc(v_decls_1865_);
lean_inc(v_lDecls_1864_);
lean_inc(v_mvarCounter_1863_);
lean_inc(v_lmvarCounter_1862_);
lean_inc(v_levelAssignDepth_1861_);
lean_inc(v_depth_1860_);
lean_dec(v_mctx_1852_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1885_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1875_ = lean_box(0);
v___x_1876_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1___redArg(v_eAssignment_1868_, v_mvarId_1847_, v_val_1848_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 8, v___x_1876_);
v___x_1878_ = v___x_1873_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_depth_1860_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_levelAssignDepth_1861_);
lean_ctor_set(v_reuseFailAlloc_1884_, 2, v_lmvarCounter_1862_);
lean_ctor_set(v_reuseFailAlloc_1884_, 3, v_mvarCounter_1863_);
lean_ctor_set(v_reuseFailAlloc_1884_, 4, v_lDecls_1864_);
lean_ctor_set(v_reuseFailAlloc_1884_, 5, v_decls_1865_);
lean_ctor_set(v_reuseFailAlloc_1884_, 6, v_userNames_1866_);
lean_ctor_set(v_reuseFailAlloc_1884_, 7, v_lAssignment_1867_);
lean_ctor_set(v_reuseFailAlloc_1884_, 8, v___x_1876_);
lean_ctor_set(v_reuseFailAlloc_1884_, 9, v_dAssignment_1869_);
lean_ctor_set(v_reuseFailAlloc_1884_, 10, v_instanceTypedMVars_1870_);
lean_ctor_set(v_reuseFailAlloc_1884_, 11, v_synthNormMemo_1871_);
v___x_1878_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1880_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1878_);
v___x_1880_ = v___x_1858_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_cache_1853_);
lean_ctor_set(v_reuseFailAlloc_1883_, 2, v_zetaDeltaFVarIds_1854_);
lean_ctor_set(v_reuseFailAlloc_1883_, 3, v_postponed_1855_);
lean_ctor_set(v_reuseFailAlloc_1883_, 4, v_diag_1856_);
v___x_1880_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = lean_st_ref_put(v___y_1849_, v___x_1880_);
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1875_);
return v___x_1882_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_1887_, lean_object* v_val_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg(v_mvarId_1887_, v_val_1888_, v___y_1889_);
lean_dec(v___y_1889_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__3(lean_object* v_a_1892_, lean_object* v_args_1893_, lean_object* v_a_1894_, lean_object* v_x_1895_){
_start:
{
if (lean_obj_tag(v_x_1895_) == 0)
{
lean_dec(v_a_1894_);
lean_dec_ref(v_args_1893_);
return v_x_1895_;
}
else
{
lean_object* v_key_1896_; lean_object* v_value_1897_; lean_object* v_tail_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1922_; 
v_key_1896_ = lean_ctor_get(v_x_1895_, 0);
v_value_1897_ = lean_ctor_get(v_x_1895_, 1);
v_tail_1898_ = lean_ctor_get(v_x_1895_, 2);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_x_1895_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1900_ = v_x_1895_;
v_isShared_1901_ = v_isSharedCheck_1922_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_tail_1898_);
lean_inc(v_value_1897_);
lean_inc(v_key_1896_);
lean_dec(v_x_1895_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1922_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
uint8_t v___x_1902_; 
v___x_1902_ = l_Lean_instBEqMVarId_beq(v_key_1896_, v_a_1894_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; lean_object* v___x_1905_; 
v___x_1903_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__3(v_a_1892_, v_args_1893_, v_a_1894_, v_tail_1898_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 2, v___x_1903_);
v___x_1905_ = v___x_1900_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_key_1896_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_value_1897_);
lean_ctor_set(v_reuseFailAlloc_1906_, 2, v___x_1903_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
else
{
lean_object* v_fst_1907_; lean_object* v_snd_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1921_; 
lean_dec(v_key_1896_);
v_fst_1907_ = lean_ctor_get(v_value_1897_, 0);
v_snd_1908_ = lean_ctor_get(v_value_1897_, 1);
v_isSharedCheck_1921_ = !lean_is_exclusive(v_value_1897_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1910_ = v_value_1897_;
v_isShared_1911_ = v_isSharedCheck_1921_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_snd_1908_);
lean_inc(v_fst_1907_);
lean_dec(v_value_1897_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1921_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1912_ = l_Lean_Expr_mvarId_x21(v_a_1892_);
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
lean_ctor_set(v___x_1913_, 1, v_args_1893_);
v___x_1914_ = lean_array_push(v_snd_1908_, v___x_1913_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 1, v___x_1914_);
v___x_1916_ = v___x_1910_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_fst_1907_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1918_; 
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 1, v___x_1916_);
lean_ctor_set(v___x_1900_, 0, v_a_1894_);
v___x_1918_ = v___x_1900_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1894_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1919_, 2, v_tail_1898_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__3___boxed(lean_object* v_a_1923_, lean_object* v_args_1924_, lean_object* v_a_1925_, lean_object* v_x_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__3(v_a_1923_, v_args_1924_, v_a_1925_, v_x_1926_);
lean_dec_ref(v_a_1923_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2(lean_object* v_a_1928_, lean_object* v_args_1929_, lean_object* v_m_1930_, lean_object* v_a_1931_){
_start:
{
lean_object* v_size_1932_; lean_object* v_buckets_1933_; lean_object* v___x_1934_; uint64_t v___x_1935_; uint64_t v___x_1936_; uint64_t v___x_1937_; uint64_t v_fold_1938_; uint64_t v___x_1939_; uint64_t v___x_1940_; uint64_t v___x_1941_; size_t v___x_1942_; size_t v___x_1943_; size_t v___x_1944_; size_t v___x_1945_; size_t v___x_1946_; lean_object* v_bucket_1947_; uint8_t v___x_1948_; 
v_size_1932_ = lean_ctor_get(v_m_1930_, 0);
v_buckets_1933_ = lean_ctor_get(v_m_1930_, 1);
v___x_1934_ = lean_array_get_size(v_buckets_1933_);
v___x_1935_ = l_Lean_instHashableMVarId_hash(v_a_1931_);
v___x_1936_ = 32ULL;
v___x_1937_ = lean_uint64_shift_right(v___x_1935_, v___x_1936_);
v_fold_1938_ = lean_uint64_xor(v___x_1935_, v___x_1937_);
v___x_1939_ = 16ULL;
v___x_1940_ = lean_uint64_shift_right(v_fold_1938_, v___x_1939_);
v___x_1941_ = lean_uint64_xor(v_fold_1938_, v___x_1940_);
v___x_1942_ = lean_uint64_to_usize(v___x_1941_);
v___x_1943_ = lean_usize_of_nat(v___x_1934_);
v___x_1944_ = ((size_t)1ULL);
v___x_1945_ = lean_usize_sub(v___x_1943_, v___x_1944_);
v___x_1946_ = lean_usize_land(v___x_1942_, v___x_1945_);
v_bucket_1947_ = lean_array_uget_borrowed(v_buckets_1933_, v___x_1946_);
v___x_1948_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__7___redArg(v_a_1931_, v_bucket_1947_);
if (v___x_1948_ == 0)
{
lean_dec(v_a_1931_);
lean_dec_ref(v_args_1929_);
return v_m_1930_;
}
else
{
lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1959_; 
lean_inc(v_bucket_1947_);
lean_inc_ref(v_buckets_1933_);
lean_inc(v_size_1932_);
v_isSharedCheck_1959_ = !lean_is_exclusive(v_m_1930_);
if (v_isSharedCheck_1959_ == 0)
{
lean_object* v_unused_1960_; lean_object* v_unused_1961_; 
v_unused_1960_ = lean_ctor_get(v_m_1930_, 1);
lean_dec(v_unused_1960_);
v_unused_1961_ = lean_ctor_get(v_m_1930_, 0);
lean_dec(v_unused_1961_);
v___x_1950_ = v_m_1930_;
v_isShared_1951_ = v_isSharedCheck_1959_;
goto v_resetjp_1949_;
}
else
{
lean_dec(v_m_1930_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1959_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; lean_object* v_buckets_1953_; lean_object* v_bucket_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1952_ = lean_box(0);
v_buckets_1953_ = lean_array_uset(v_buckets_1933_, v___x_1946_, v___x_1952_);
v_bucket_1954_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__3(v_a_1928_, v_args_1929_, v_a_1931_, v_bucket_1947_);
v___x_1955_ = lean_array_uset(v_buckets_1953_, v___x_1946_, v_bucket_1954_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 1, v___x_1955_);
v___x_1957_ = v___x_1950_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_size_1932_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___boxed(lean_object* v_a_1962_, lean_object* v_args_1963_, lean_object* v_m_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2(v_a_1962_, v_args_1963_, v_m_1964_, v_a_1965_);
lean_dec_ref(v_a_1962_);
return v_res_1966_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1967_; lean_object* v_dummy_1968_; 
v___x_1967_ = lean_box(0);
v_dummy_1968_ = l_Lean_Expr_sort___override(v___x_1967_);
return v_dummy_1968_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1972_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__2));
v___x_1973_ = l_Lean_stringToMessageData(v___x_1972_);
return v___x_1973_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__4));
v___x_1976_ = l_Lean_stringToMessageData(v___x_1975_);
return v___x_1976_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__6));
v___x_1979_ = l_Lean_stringToMessageData(v___x_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0(lean_object* v_info_1980_, lean_object* v_val_1981_, lean_object* v___x_1982_, lean_object* v_goal_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v___x_2075_; 
lean_inc(v_goal_1983_);
v___x_2075_ = l_Lean_MVarId_getType(v_goal_1983_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2122_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2122_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2122_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; uint8_t v___x_2081_; 
v___x_2080_ = l_Lean_Expr_cleanupAnnotations(v_a_2076_);
lean_dec(v_a_2076_);
v___x_2081_ = l_Lean_Expr_isApp(v___x_2080_);
if (v___x_2081_ == 0)
{
lean_dec_ref(v___x_2080_);
lean_del_object(v___x_2078_);
lean_dec(v_goal_1983_);
lean_dec_ref(v___x_1982_);
lean_dec_ref(v_val_1981_);
goto v___jp_1996_;
}
else
{
lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2082_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2080_);
lean_dec_ref(v___x_2080_);
v___x_2083_ = l_Lean_Expr_isApp(v___x_2082_);
if (v___x_2083_ == 0)
{
lean_dec_ref(v___x_2082_);
lean_del_object(v___x_2078_);
lean_dec(v_goal_1983_);
lean_dec_ref(v___x_1982_);
lean_dec_ref(v_val_1981_);
goto v___jp_1996_;
}
else
{
lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2084_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2082_);
v___x_2085_ = l_Lean_Expr_isApp(v___x_2084_);
if (v___x_2085_ == 0)
{
lean_dec_ref(v___x_2084_);
lean_dec_ref(v___x_2082_);
lean_del_object(v___x_2078_);
lean_dec(v_goal_1983_);
lean_dec_ref(v___x_1982_);
lean_dec_ref(v_val_1981_);
goto v___jp_1996_;
}
else
{
lean_object* v___x_2086_; uint8_t v___x_2087_; 
v___x_2086_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2084_);
lean_dec_ref(v___x_2084_);
v___x_2087_ = l_Lean_Expr_isApp(v___x_2086_);
if (v___x_2087_ == 0)
{
lean_dec_ref(v___x_2086_);
lean_dec_ref(v___x_2082_);
lean_del_object(v___x_2078_);
lean_dec(v_goal_1983_);
lean_dec_ref(v___x_1982_);
lean_dec_ref(v_val_1981_);
goto v___jp_1996_;
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2088_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2086_);
lean_dec_ref(v___x_2086_);
v___x_2089_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__2));
v___x_2090_ = l_Lean_Expr_isConstOf(v___x_2088_, v___x_2089_);
lean_dec_ref(v___x_2088_);
if (v___x_2090_ == 0)
{
lean_dec_ref(v___x_2082_);
lean_del_object(v___x_2078_);
lean_dec(v_goal_1983_);
lean_dec_ref(v___x_1982_);
lean_dec_ref(v_val_1981_);
goto v___jp_1996_;
}
else
{
lean_object* v_arg_2091_; lean_object* v_top_2092_; lean_object* v_numStates_2093_; uint8_t v___x_2094_; 
v_arg_2091_ = lean_ctor_get(v___x_2082_, 1);
lean_inc_ref(v_arg_2091_);
lean_dec_ref(v___x_2082_);
v_top_2092_ = lean_ctor_get(v_val_1981_, 1);
v_numStates_2093_ = lean_ctor_get(v_val_1981_, 4);
v___x_2094_ = lean_expr_eqv(v_arg_2091_, v_top_2092_);
lean_dec_ref(v_arg_2091_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; lean_object* v___x_2097_; 
lean_dec(v_goal_1983_);
lean_dec_ref(v___x_1982_);
lean_dec_ref(v_val_1981_);
v___x_2095_ = lean_box(0);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2095_);
v___x_2097_ = v___x_2078_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
else
{
lean_object* v_excessArgs_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; 
lean_del_object(v___x_2078_);
v_excessArgs_2099_ = lean_ctor_get(v_info_1980_, 3);
v___x_2100_ = lean_array_get_size(v_excessArgs_2099_);
v___x_2101_ = lean_nat_dec_eq(v___x_2100_, v_numStates_2093_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_inc(v_numStates_2093_);
lean_dec(v_goal_1983_);
lean_dec_ref(v_val_1981_);
v___x_2102_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__3, &l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__3);
v___x_2103_ = l_Lean_indentExpr(v___x_1982_);
v___x_2104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2102_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__5, &l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__5);
v___x_2106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2104_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
v___x_2107_ = l_Nat_reprFast(v_numStates_2093_);
v___x_2108_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
v___x_2109_ = l_Lean_MessageData_ofFormat(v___x_2108_);
v___x_2110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2106_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___x_2111_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__7, &l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__7);
v___x_2112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2110_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___redArg(v___x_2112_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2113_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2113_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
else
{
goto v___jp_1999_;
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
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec(v_goal_1983_);
lean_dec_ref(v___x_1982_);
lean_dec_ref(v_val_1981_);
v_a_2123_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2075_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2075_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
v___jp_1996_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_box(0);
v___x_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
return v___x_1998_;
}
v___jp_1999_:
{
lean_object* v_excessArgs_2000_; lean_object* v_spec_2001_; lean_object* v_hyp_2002_; lean_object* v_rhsGoal_2003_; lean_object* v_nargs_2004_; lean_object* v_dummy_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v_args_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_excessArgs_2000_ = lean_ctor_get(v_info_1980_, 3);
v_spec_2001_ = lean_ctor_get(v_val_1981_, 0);
lean_inc_ref(v_spec_2001_);
v_hyp_2002_ = lean_ctor_get(v_val_1981_, 2);
lean_inc(v_hyp_2002_);
v_rhsGoal_2003_ = lean_ctor_get(v_val_1981_, 3);
lean_inc(v_rhsGoal_2003_);
lean_dec_ref(v_val_1981_);
v_nargs_2004_ = l_Lean_Expr_getAppNumArgs(v___x_1982_);
v_dummy_2005_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__0, &l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__0);
lean_inc(v_nargs_2004_);
v___x_2006_ = lean_mk_array(v_nargs_2004_, v_dummy_2005_);
v___x_2007_ = lean_unsigned_to_nat(1u);
v___x_2008_ = lean_nat_sub(v_nargs_2004_, v___x_2007_);
lean_dec(v_nargs_2004_);
v___x_2009_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1982_, v___x_2006_, v___x_2008_);
v_args_2010_ = l_Array_append___redArg(v___x_2009_, v_excessArgs_2000_);
v___x_2011_ = l_Lean_Expr_mvar___override(v_hyp_2002_);
v___x_2012_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0(v___x_2011_, v_args_2010_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v___x_2012_, 1);
v___x_2014_ = lean_box(0);
v___x_2015_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2013_, v___x_2014_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc_n(v_a_2016_, 2);
lean_dec_ref_known(v___x_2015_, 1);
lean_inc_ref(v_args_2010_);
v___x_2017_ = lean_array_push(v_args_2010_, v_a_2016_);
v___x_2018_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0(v_spec_2001_, v___x_2017_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec_ref(v___x_2017_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2049_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
lean_dec_ref_known(v___x_2018_, 1);
v___x_2020_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg(v_goal_1983_, v_a_2019_, v___y_1992_);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2049_ == 0)
{
lean_object* v_unused_2050_; 
v_unused_2050_ = lean_ctor_get(v___x_2020_, 0);
lean_dec(v_unused_2050_);
v___x_2022_ = v___x_2020_;
v_isShared_2023_ = v_isSharedCheck_2049_;
goto v_resetjp_2021_;
}
else
{
lean_dec(v___x_2020_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2049_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v_specBackwardRuleCache_2025_; lean_object* v_splitBackwardRuleCache_2026_; lean_object* v_latticeBackwardRuleCache_2027_; lean_object* v_frameBackwardRuleCache_2028_; lean_object* v_frameDB_2029_; lean_object* v_invariants_2030_; lean_object* v_vcs_2031_; lean_object* v_simpState_2032_; lean_object* v_fuel_2033_; lean_object* v_inlineHandledInvariants_2034_; lean_object* v_pendingJoinPoints_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2048_; 
v___x_2024_ = lean_st_ref_take(v___y_1985_);
v_specBackwardRuleCache_2025_ = lean_ctor_get(v___x_2024_, 0);
v_splitBackwardRuleCache_2026_ = lean_ctor_get(v___x_2024_, 1);
v_latticeBackwardRuleCache_2027_ = lean_ctor_get(v___x_2024_, 2);
v_frameBackwardRuleCache_2028_ = lean_ctor_get(v___x_2024_, 3);
v_frameDB_2029_ = lean_ctor_get(v___x_2024_, 4);
v_invariants_2030_ = lean_ctor_get(v___x_2024_, 5);
v_vcs_2031_ = lean_ctor_get(v___x_2024_, 6);
v_simpState_2032_ = lean_ctor_get(v___x_2024_, 7);
v_fuel_2033_ = lean_ctor_get(v___x_2024_, 8);
v_inlineHandledInvariants_2034_ = lean_ctor_get(v___x_2024_, 9);
v_pendingJoinPoints_2035_ = lean_ctor_get(v___x_2024_, 10);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2037_ = v___x_2024_;
v_isShared_2038_ = v_isSharedCheck_2048_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_pendingJoinPoints_2035_);
lean_inc(v_inlineHandledInvariants_2034_);
lean_inc(v_fuel_2033_);
lean_inc(v_simpState_2032_);
lean_inc(v_vcs_2031_);
lean_inc(v_invariants_2030_);
lean_inc(v_frameDB_2029_);
lean_inc(v_frameBackwardRuleCache_2028_);
lean_inc(v_latticeBackwardRuleCache_2027_);
lean_inc(v_splitBackwardRuleCache_2026_);
lean_inc(v_specBackwardRuleCache_2025_);
lean_dec(v___x_2024_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2048_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2039_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2(v_a_2016_, v_args_2010_, v_pendingJoinPoints_2035_, v_rhsGoal_2003_);
lean_dec(v_a_2016_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 10, v___x_2039_);
v___x_2041_ = v___x_2037_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_specBackwardRuleCache_2025_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_splitBackwardRuleCache_2026_);
lean_ctor_set(v_reuseFailAlloc_2047_, 2, v_latticeBackwardRuleCache_2027_);
lean_ctor_set(v_reuseFailAlloc_2047_, 3, v_frameBackwardRuleCache_2028_);
lean_ctor_set(v_reuseFailAlloc_2047_, 4, v_frameDB_2029_);
lean_ctor_set(v_reuseFailAlloc_2047_, 5, v_invariants_2030_);
lean_ctor_set(v_reuseFailAlloc_2047_, 6, v_vcs_2031_);
lean_ctor_set(v_reuseFailAlloc_2047_, 7, v_simpState_2032_);
lean_ctor_set(v_reuseFailAlloc_2047_, 8, v_fuel_2033_);
lean_ctor_set(v_reuseFailAlloc_2047_, 9, v_inlineHandledInvariants_2034_);
lean_ctor_set(v_reuseFailAlloc_2047_, 10, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2045_; 
v___x_2042_ = lean_st_ref_put(v___y_1985_, v___x_2041_);
v___x_2043_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__1));
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2043_);
v___x_2045_ = v___x_2022_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v_a_2016_);
lean_dec_ref(v_args_2010_);
lean_dec(v_rhsGoal_2003_);
lean_dec(v_goal_1983_);
v_a_2051_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2018_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2018_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec_ref(v_args_2010_);
lean_dec(v_rhsGoal_2003_);
lean_dec_ref(v_spec_2001_);
lean_dec(v_goal_1983_);
v_a_2059_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2015_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2015_);
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
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec_ref(v_args_2010_);
lean_dec(v_rhsGoal_2003_);
lean_dec_ref(v_spec_2001_);
lean_dec(v_goal_1983_);
v_a_2067_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2012_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2012_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___boxed(lean_object* v_info_2131_, lean_object* v_val_2132_, lean_object* v___x_2133_, lean_object* v_goal_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0(v_info_2131_, v_val_2132_, v___x_2133_, v_goal_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec_ref(v_info_2131_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg(lean_object* v_t_2148_, lean_object* v_k_2149_){
_start:
{
if (lean_obj_tag(v_t_2148_) == 0)
{
lean_object* v_k_2150_; lean_object* v_v_2151_; lean_object* v_l_2152_; lean_object* v_r_2153_; uint8_t v___x_2154_; 
v_k_2150_ = lean_ctor_get(v_t_2148_, 1);
v_v_2151_ = lean_ctor_get(v_t_2148_, 2);
v_l_2152_ = lean_ctor_get(v_t_2148_, 3);
v_r_2153_ = lean_ctor_get(v_t_2148_, 4);
v___x_2154_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2149_, v_k_2150_);
switch(v___x_2154_)
{
case 0:
{
v_t_2148_ = v_l_2152_;
goto _start;
}
case 1:
{
lean_object* v___x_2156_; 
lean_inc(v_v_2151_);
v___x_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2156_, 0, v_v_2151_);
return v___x_2156_;
}
default: 
{
v_t_2148_ = v_r_2153_;
goto _start;
}
}
}
else
{
lean_object* v___x_2158_; 
v___x_2158_ = lean_box(0);
return v___x_2158_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg___boxed(lean_object* v_t_2159_, lean_object* v_k_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg(v_t_2159_, v_k_2160_);
lean_dec(v_k_2160_);
lean_dec(v_t_2159_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f(lean_object* v_scope_2162_, lean_object* v_goal_2163_, lean_object* v_info_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_2164_);
v___x_2178_ = l_Lean_Expr_getAppFn(v___x_2177_);
v___x_2179_ = l_Lean_Expr_fvarId_x3f(v___x_2178_);
lean_dec_ref(v___x_2178_);
if (lean_obj_tag(v___x_2179_) == 1)
{
lean_object* v_val_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2193_; 
v_val_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2193_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_val_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2193_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v_joinPoints_2184_; lean_object* v___x_2185_; 
v_joinPoints_2184_ = lean_ctor_get(v_scope_2162_, 3);
v___x_2185_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg(v_joinPoints_2184_, v_val_2180_);
lean_dec(v_val_2180_);
if (lean_obj_tag(v___x_2185_) == 1)
{
lean_object* v_val_2186_; lean_object* v___f_2187_; lean_object* v___x_2188_; 
lean_del_object(v___x_2182_);
v_val_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_val_2186_);
lean_dec_ref_known(v___x_2185_, 1);
lean_inc(v_goal_2163_);
v___f_2187_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___boxed), 16, 4);
lean_closure_set(v___f_2187_, 0, v_info_2164_);
lean_closure_set(v___f_2187_, 1, v_val_2186_);
lean_closure_set(v___f_2187_, 2, v___x_2177_);
lean_closure_set(v___f_2187_, 3, v_goal_2163_);
v___x_2188_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg(v_goal_2163_, v___f_2187_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
return v___x_2188_;
}
else
{
lean_object* v___x_2189_; lean_object* v___x_2191_; 
lean_dec(v___x_2185_);
lean_dec_ref(v___x_2177_);
lean_dec_ref(v_info_2164_);
lean_dec(v_goal_2163_);
v___x_2189_ = lean_box(0);
if (v_isShared_2183_ == 0)
{
lean_ctor_set_tag(v___x_2182_, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2189_);
v___x_2191_ = v___x_2182_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2189_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
lean_dec(v___x_2179_);
lean_dec_ref(v___x_2177_);
lean_dec_ref(v_info_2164_);
lean_dec(v_goal_2163_);
v___x_2194_ = lean_box(0);
v___x_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
return v___x_2195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___boxed(lean_object* v_scope_2196_, lean_object* v_goal_2197_, lean_object* v_info_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_Elab_Tactic_VCGen_wpJump_x3f(v_scope_2196_, v_goal_2197_, v_info_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_);
lean_dec(v_a_2209_);
lean_dec_ref(v_a_2208_);
lean_dec(v_a_2207_);
lean_dec_ref(v_a_2206_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
lean_dec(v_a_2201_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
lean_dec_ref(v_scope_2196_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0(lean_object* v_00_u03b4_2212_, lean_object* v_t_2213_, lean_object* v_k_2214_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg(v_t_2213_, v_k_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___boxed(lean_object* v_00_u03b4_2216_, lean_object* v_t_2217_, lean_object* v_k_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0(v_00_u03b4_2216_, v_t_2217_, v_k_2218_);
lean_dec(v_k_2218_);
lean_dec(v_t_2217_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1(lean_object* v_mvarId_2220_, lean_object* v_val_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg(v_mvarId_2220_, v_val_2221_, v___y_2230_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___boxed(lean_object* v_mvarId_2235_, lean_object* v_val_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1(v_mvarId_2235_, v_val_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1(lean_object* v_00_u03b2_2250_, lean_object* v_x_2251_, lean_object* v_x_2252_, lean_object* v_x_2253_){
_start:
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1___redArg(v_x_2251_, v_x_2252_, v_x_2253_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2255_, lean_object* v_x_2256_, size_t v_x_2257_, size_t v_x_2258_, lean_object* v_x_2259_, lean_object* v_x_2260_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2___redArg(v_x_2256_, v_x_2257_, v_x_2258_, v_x_2259_, v_x_2260_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2262_, lean_object* v_x_2263_, lean_object* v_x_2264_, lean_object* v_x_2265_, lean_object* v_x_2266_, lean_object* v_x_2267_){
_start:
{
size_t v_x_16588__boxed_2268_; size_t v_x_16589__boxed_2269_; lean_object* v_res_2270_; 
v_x_16588__boxed_2268_ = lean_unbox_usize(v_x_2264_);
lean_dec(v_x_2264_);
v_x_16589__boxed_2269_ = lean_unbox_usize(v_x_2265_);
lean_dec(v_x_2265_);
v_res_2270_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2(v_00_u03b2_2262_, v_x_2263_, v_x_16588__boxed_2268_, v_x_16589__boxed_2269_, v_x_2266_, v_x_2267_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2271_, lean_object* v_n_2272_, lean_object* v_k_2273_, lean_object* v_v_2274_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__4___redArg(v_n_2272_, v_k_2273_, v_v_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_2276_, size_t v_depth_2277_, lean_object* v_keys_2278_, lean_object* v_vals_2279_, lean_object* v_heq_2280_, lean_object* v_i_2281_, lean_object* v_entries_2282_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_2277_, v_keys_2278_, v_vals_2279_, v_i_2281_, v_entries_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2284_, lean_object* v_depth_2285_, lean_object* v_keys_2286_, lean_object* v_vals_2287_, lean_object* v_heq_2288_, lean_object* v_i_2289_, lean_object* v_entries_2290_){
_start:
{
size_t v_depth_boxed_2291_; lean_object* v_res_2292_; 
v_depth_boxed_2291_ = lean_unbox_usize(v_depth_2285_);
lean_dec(v_depth_2285_);
v_res_2292_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__5(v_00_u03b2_2284_, v_depth_boxed_2291_, v_keys_2286_, v_vals_2287_, v_heq_2288_, v_i_2289_, v_entries_2290_);
lean_dec_ref(v_vals_2287_);
lean_dec_ref(v_keys_2286_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_2293_, lean_object* v_x_2294_, lean_object* v_x_2295_, lean_object* v_x_2296_, lean_object* v_x_2297_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(v_x_2294_, v_x_2295_, v_x_2296_, v_x_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(lean_object* v_as_2299_, size_t v_i_2300_, size_t v_stop_2301_, lean_object* v_b_2302_){
_start:
{
lean_object* v___y_2304_; uint8_t v___x_2308_; 
v___x_2308_ = lean_usize_dec_eq(v_i_2300_, v_stop_2301_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; 
v___x_2309_ = lean_array_uget_borrowed(v_as_2299_, v_i_2300_);
if (lean_obj_tag(v___x_2309_) == 0)
{
v___y_2304_ = v_b_2302_;
goto v___jp_2303_;
}
else
{
lean_object* v_val_2310_; uint8_t v___x_2311_; 
v_val_2310_ = lean_ctor_get(v___x_2309_, 0);
v___x_2311_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2310_);
if (v___x_2311_ == 0)
{
lean_object* v___x_2312_; 
lean_inc(v_val_2310_);
v___x_2312_ = lean_array_push(v_b_2302_, v_val_2310_);
v___y_2304_ = v___x_2312_;
goto v___jp_2303_;
}
else
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_LocalDecl_value_x3f(v_val_2310_, v___x_2308_);
if (lean_obj_tag(v___x_2313_) == 0)
{
v___y_2304_ = v_b_2302_;
goto v___jp_2303_;
}
else
{
lean_object* v___x_2314_; 
lean_dec_ref_known(v___x_2313_, 1);
lean_inc(v_val_2310_);
v___x_2314_ = lean_array_push(v_b_2302_, v_val_2310_);
v___y_2304_ = v___x_2314_;
goto v___jp_2303_;
}
}
}
}
else
{
return v_b_2302_;
}
v___jp_2303_:
{
size_t v___x_2305_; size_t v___x_2306_; 
v___x_2305_ = ((size_t)1ULL);
v___x_2306_ = lean_usize_add(v_i_2300_, v___x_2305_);
v_i_2300_ = v___x_2306_;
v_b_2302_ = v___y_2304_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2___boxed(lean_object* v_as_2315_, lean_object* v_i_2316_, lean_object* v_stop_2317_, lean_object* v_b_2318_){
_start:
{
size_t v_i_boxed_2319_; size_t v_stop_boxed_2320_; lean_object* v_res_2321_; 
v_i_boxed_2319_ = lean_unbox_usize(v_i_2316_);
lean_dec(v_i_2316_);
v_stop_boxed_2320_ = lean_unbox_usize(v_stop_2317_);
lean_dec(v_stop_2317_);
v_res_2321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_as_2315_, v_i_boxed_2319_, v_stop_boxed_2320_, v_b_2318_);
lean_dec_ref(v_as_2315_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3(lean_object* v_x_2322_, lean_object* v_x_2323_){
_start:
{
if (lean_obj_tag(v_x_2322_) == 0)
{
lean_object* v_cs_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; uint8_t v___x_2327_; 
v_cs_2324_ = lean_ctor_get(v_x_2322_, 0);
v___x_2325_ = lean_unsigned_to_nat(0u);
v___x_2326_ = lean_array_get_size(v_cs_2324_);
v___x_2327_ = lean_nat_dec_lt(v___x_2325_, v___x_2326_);
if (v___x_2327_ == 0)
{
return v_x_2323_;
}
else
{
size_t v___x_2328_; size_t v___x_2329_; lean_object* v___x_2330_; 
v___x_2328_ = ((size_t)0ULL);
v___x_2329_ = lean_usize_of_nat(v___x_2326_);
v___x_2330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2(v_cs_2324_, v___x_2328_, v___x_2329_, v_x_2323_);
return v___x_2330_;
}
}
else
{
lean_object* v_vs_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; uint8_t v___x_2334_; 
v_vs_2331_ = lean_ctor_get(v_x_2322_, 0);
v___x_2332_ = lean_unsigned_to_nat(0u);
v___x_2333_ = lean_array_get_size(v_vs_2331_);
v___x_2334_ = lean_nat_dec_lt(v___x_2332_, v___x_2333_);
if (v___x_2334_ == 0)
{
return v_x_2323_;
}
else
{
size_t v___x_2335_; size_t v___x_2336_; lean_object* v___x_2337_; 
v___x_2335_ = ((size_t)0ULL);
v___x_2336_ = lean_usize_of_nat(v___x_2333_);
v___x_2337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_vs_2331_, v___x_2335_, v___x_2336_, v_x_2323_);
return v___x_2337_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_2338_, size_t v_i_2339_, size_t v_stop_2340_, lean_object* v_b_2341_){
_start:
{
uint8_t v___x_2342_; 
v___x_2342_ = lean_usize_dec_eq(v_i_2339_, v_stop_2340_);
if (v___x_2342_ == 0)
{
lean_object* v___x_2343_; lean_object* v___x_2344_; size_t v___x_2345_; size_t v___x_2346_; 
v___x_2343_ = lean_array_uget_borrowed(v_as_2338_, v_i_2339_);
v___x_2344_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3(v___x_2343_, v_b_2341_);
v___x_2345_ = ((size_t)1ULL);
v___x_2346_ = lean_usize_add(v_i_2339_, v___x_2345_);
v_i_2339_ = v___x_2346_;
v_b_2341_ = v___x_2344_;
goto _start;
}
else
{
return v_b_2341_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_2348_, lean_object* v_i_2349_, lean_object* v_stop_2350_, lean_object* v_b_2351_){
_start:
{
size_t v_i_boxed_2352_; size_t v_stop_boxed_2353_; lean_object* v_res_2354_; 
v_i_boxed_2352_ = lean_unbox_usize(v_i_2349_);
lean_dec(v_i_2349_);
v_stop_boxed_2353_ = lean_unbox_usize(v_stop_2350_);
lean_dec(v_stop_2350_);
v_res_2354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2(v_as_2348_, v_i_boxed_2352_, v_stop_boxed_2353_, v_b_2351_);
lean_dec_ref(v_as_2348_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3___boxed(lean_object* v_x_2355_, lean_object* v_x_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3(v_x_2355_, v_x_2356_);
lean_dec_ref(v_x_2355_);
return v_res_2357_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1(lean_object* v_x_2359_, size_t v_x_2360_, size_t v_x_2361_, lean_object* v_x_2362_){
_start:
{
if (lean_obj_tag(v_x_2359_) == 0)
{
lean_object* v_cs_2363_; lean_object* v___x_2364_; size_t v___x_2365_; lean_object* v_j_2366_; lean_object* v___x_2367_; size_t v___x_2368_; size_t v___x_2369_; size_t v___x_2370_; size_t v___x_2371_; size_t v___x_2372_; size_t v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; 
v_cs_2363_ = lean_ctor_get(v_x_2359_, 0);
v___x_2364_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___closed__0);
v___x_2365_ = lean_usize_shift_right(v_x_2360_, v_x_2361_);
v_j_2366_ = lean_usize_to_nat(v___x_2365_);
v___x_2367_ = lean_array_get_borrowed(v___x_2364_, v_cs_2363_, v_j_2366_);
v___x_2368_ = ((size_t)1ULL);
v___x_2369_ = lean_usize_shift_left(v___x_2368_, v_x_2361_);
v___x_2370_ = lean_usize_sub(v___x_2369_, v___x_2368_);
v___x_2371_ = lean_usize_land(v_x_2360_, v___x_2370_);
v___x_2372_ = ((size_t)5ULL);
v___x_2373_ = lean_usize_sub(v_x_2361_, v___x_2372_);
v___x_2374_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1(v___x_2367_, v___x_2371_, v___x_2373_, v_x_2362_);
v___x_2375_ = lean_unsigned_to_nat(1u);
v___x_2376_ = lean_nat_add(v_j_2366_, v___x_2375_);
lean_dec(v_j_2366_);
v___x_2377_ = lean_array_get_size(v_cs_2363_);
v___x_2378_ = lean_nat_dec_lt(v___x_2376_, v___x_2377_);
if (v___x_2378_ == 0)
{
lean_dec(v___x_2376_);
return v___x_2374_;
}
else
{
size_t v___x_2379_; size_t v___x_2380_; lean_object* v___x_2381_; 
v___x_2379_ = lean_usize_of_nat(v___x_2376_);
lean_dec(v___x_2376_);
v___x_2380_ = lean_usize_of_nat(v___x_2377_);
v___x_2381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2(v_cs_2363_, v___x_2379_, v___x_2380_, v___x_2374_);
return v___x_2381_;
}
}
else
{
lean_object* v_vs_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; 
v_vs_2382_ = lean_ctor_get(v_x_2359_, 0);
v___x_2383_ = lean_usize_to_nat(v_x_2360_);
v___x_2384_ = lean_array_get_size(v_vs_2382_);
v___x_2385_ = lean_nat_dec_lt(v___x_2383_, v___x_2384_);
if (v___x_2385_ == 0)
{
lean_dec(v___x_2383_);
return v_x_2362_;
}
else
{
size_t v___x_2386_; size_t v___x_2387_; lean_object* v___x_2388_; 
v___x_2386_ = lean_usize_of_nat(v___x_2383_);
lean_dec(v___x_2383_);
v___x_2387_ = lean_usize_of_nat(v___x_2384_);
v___x_2388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_vs_2382_, v___x_2386_, v___x_2387_, v_x_2362_);
return v___x_2388_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___boxed(lean_object* v_x_2389_, lean_object* v_x_2390_, lean_object* v_x_2391_, lean_object* v_x_2392_){
_start:
{
size_t v_x_1498__boxed_2393_; size_t v_x_1499__boxed_2394_; lean_object* v_res_2395_; 
v_x_1498__boxed_2393_ = lean_unbox_usize(v_x_2390_);
lean_dec(v_x_2390_);
v_x_1499__boxed_2394_ = lean_unbox_usize(v_x_2391_);
lean_dec(v_x_2391_);
v_res_2395_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1(v_x_2389_, v_x_1498__boxed_2393_, v_x_1499__boxed_2394_, v_x_2392_);
lean_dec_ref(v_x_2389_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0(lean_object* v_t_2396_, lean_object* v_init_2397_, lean_object* v_start_2398_){
_start:
{
lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2399_ = lean_unsigned_to_nat(0u);
v___x_2400_ = lean_nat_dec_eq(v_start_2398_, v___x_2399_);
if (v___x_2400_ == 0)
{
lean_object* v_root_2401_; lean_object* v_tail_2402_; size_t v_shift_2403_; lean_object* v_tailOff_2404_; uint8_t v___x_2405_; 
v_root_2401_ = lean_ctor_get(v_t_2396_, 0);
v_tail_2402_ = lean_ctor_get(v_t_2396_, 1);
v_shift_2403_ = lean_ctor_get_usize(v_t_2396_, 4);
v_tailOff_2404_ = lean_ctor_get(v_t_2396_, 3);
v___x_2405_ = lean_nat_dec_le(v_tailOff_2404_, v_start_2398_);
if (v___x_2405_ == 0)
{
size_t v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2406_ = lean_usize_of_nat(v_start_2398_);
v___x_2407_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1(v_root_2401_, v___x_2406_, v_shift_2403_, v_init_2397_);
v___x_2408_ = lean_array_get_size(v_tail_2402_);
v___x_2409_ = lean_nat_dec_lt(v___x_2399_, v___x_2408_);
if (v___x_2409_ == 0)
{
return v___x_2407_;
}
else
{
size_t v___x_2410_; size_t v___x_2411_; lean_object* v___x_2412_; 
v___x_2410_ = ((size_t)0ULL);
v___x_2411_ = lean_usize_of_nat(v___x_2408_);
v___x_2412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_tail_2402_, v___x_2410_, v___x_2411_, v___x_2407_);
return v___x_2412_;
}
}
else
{
lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v___x_2413_ = lean_nat_sub(v_start_2398_, v_tailOff_2404_);
v___x_2414_ = lean_array_get_size(v_tail_2402_);
v___x_2415_ = lean_nat_dec_lt(v___x_2413_, v___x_2414_);
if (v___x_2415_ == 0)
{
lean_dec(v___x_2413_);
return v_init_2397_;
}
else
{
size_t v___x_2416_; size_t v___x_2417_; lean_object* v___x_2418_; 
v___x_2416_ = lean_usize_of_nat(v___x_2413_);
lean_dec(v___x_2413_);
v___x_2417_ = lean_usize_of_nat(v___x_2414_);
v___x_2418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_tail_2402_, v___x_2416_, v___x_2417_, v_init_2397_);
return v___x_2418_;
}
}
}
else
{
lean_object* v_root_2419_; lean_object* v_tail_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; uint8_t v___x_2423_; 
v_root_2419_ = lean_ctor_get(v_t_2396_, 0);
v_tail_2420_ = lean_ctor_get(v_t_2396_, 1);
v___x_2421_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3(v_root_2419_, v_init_2397_);
v___x_2422_ = lean_array_get_size(v_tail_2420_);
v___x_2423_ = lean_nat_dec_lt(v___x_2399_, v___x_2422_);
if (v___x_2423_ == 0)
{
return v___x_2421_;
}
else
{
size_t v___x_2424_; size_t v___x_2425_; lean_object* v___x_2426_; 
v___x_2424_ = ((size_t)0ULL);
v___x_2425_ = lean_usize_of_nat(v___x_2422_);
v___x_2426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_tail_2420_, v___x_2424_, v___x_2425_, v___x_2421_);
return v___x_2426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0___boxed(lean_object* v_t_2427_, lean_object* v_init_2428_, lean_object* v_start_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0(v_t_2427_, v_init_2428_, v_start_2429_);
lean_dec(v_start_2429_);
lean_dec_ref(v_t_2427_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0(lean_object* v_lctx_2431_, lean_object* v_init_2432_, lean_object* v_start_2433_){
_start:
{
lean_object* v_decls_2434_; lean_object* v___x_2435_; 
v_decls_2434_ = lean_ctor_get(v_lctx_2431_, 1);
v___x_2435_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0(v_decls_2434_, v_init_2432_, v_start_2433_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0___boxed(lean_object* v_lctx_2436_, lean_object* v_init_2437_, lean_object* v_start_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0(v_lctx_2436_, v_init_2437_, v_start_2438_);
lean_dec(v_start_2438_);
lean_dec_ref(v_lctx_2436_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals(lean_object* v_jp_2442_, lean_object* v_jump_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v_proof_2449_; lean_object* v___x_2450_; 
v_proof_2449_ = lean_ctor_get(v_jump_2443_, 0);
lean_inc(v_proof_2449_);
lean_dec_ref(v_jump_2443_);
v___x_2450_ = l_Lean_MVarId_getDecl(v_proof_2449_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2467_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2467_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2467_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v_lctx_2455_; lean_object* v_spec_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2465_; 
v_lctx_2455_ = lean_ctor_get(v_a_2451_, 1);
lean_inc_ref_n(v_lctx_2455_, 2);
lean_dec(v_a_2451_);
v_spec_2456_ = lean_ctor_get(v_jp_2442_, 0);
v___x_2457_ = l_Lean_Expr_fvarId_x21(v_spec_2456_);
v___x_2458_ = l_Lean_LocalContext_get_x21(v_lctx_2455_, v___x_2457_);
v___x_2459_ = l_Lean_LocalDecl_index(v___x_2458_);
lean_dec_ref(v___x_2458_);
v___x_2460_ = lean_unsigned_to_nat(1u);
v___x_2461_ = lean_nat_add(v___x_2459_, v___x_2460_);
lean_dec(v___x_2459_);
v___x_2462_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals___closed__0));
v___x_2463_ = l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0(v_lctx_2455_, v___x_2462_, v___x_2461_);
lean_dec(v___x_2461_);
lean_dec_ref(v_lctx_2455_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2463_);
v___x_2465_ = v___x_2453_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
v_a_2468_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2450_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2450_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals___boxed(lean_object* v_jp_2476_, lean_object* v_jump_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals(v_jp_2476_, v_jump_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_);
lean_dec(v_a_2481_);
lean_dec_ref(v_a_2480_);
lean_dec(v_a_2479_);
lean_dec_ref(v_a_2478_);
lean_dec_ref(v_jp_2476_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg(lean_object* v_d_2487_, lean_object* v_00_u03c6_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_){
_start:
{
uint8_t v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = 0;
v___x_2497_ = l_Lean_LocalDecl_value_x3f(v_d_2487_, v___x_2496_);
if (lean_obj_tag(v___x_2497_) == 0)
{
uint8_t v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; lean_object* v___x_2504_; 
v___x_2498_ = 1;
lean_inc_ref(v_d_2487_);
v___x_2499_ = l_Lean_LocalDecl_toExpr(v_d_2487_);
v___x_2500_ = lean_unsigned_to_nat(1u);
v___x_2501_ = lean_mk_empty_array_with_capacity(v___x_2500_);
v___x_2502_ = lean_array_push(v___x_2501_, v___x_2499_);
v___x_2503_ = 1;
v___x_2504_ = l_Lean_Meta_mkLambdaFVars(v___x_2502_, v_00_u03c6_2488_, v___x_2496_, v___x_2498_, v___x_2496_, v___x_2498_, v___x_2503_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_);
lean_dec_ref(v___x_2502_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2504_, 1);
v___x_2506_ = l_Lean_LocalDecl_type(v_d_2487_);
lean_dec_ref(v_d_2487_);
lean_inc_ref(v___x_2506_);
v___x_2507_ = l_Lean_Meta_Sym_inferType(v___x_2506_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2542_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2510_ = v___x_2507_;
v_isShared_2511_ = v_isSharedCheck_2542_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2542_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
uint8_t v___x_2535_; 
v___x_2535_ = l_Lean_Expr_isProp(v_a_2508_);
lean_dec(v_a_2508_);
if (v___x_2535_ == 0)
{
lean_del_object(v___x_2510_);
goto v___jp_2512_;
}
else
{
lean_object* v___x_2536_; uint8_t v___x_2537_; 
v___x_2536_ = l_Lean_Expr_bindingBody_x21(v_a_2505_);
v___x_2537_ = l_Lean_Expr_hasLooseBVars(v___x_2536_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; lean_object* v___x_2540_; 
lean_dec(v_a_2505_);
v___x_2538_ = l_Lean_mkAnd(v___x_2506_, v___x_2536_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 0, v___x_2538_);
v___x_2540_ = v___x_2510_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2538_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
else
{
lean_dec_ref(v___x_2536_);
lean_del_object(v___x_2510_);
goto v___jp_2512_;
}
}
v___jp_2512_:
{
lean_object* v___x_2513_; 
lean_inc_ref(v___x_2506_);
v___x_2513_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_2506_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2526_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2516_ = v___x_2513_;
v_isShared_2517_ = v_isSharedCheck_2526_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2513_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2526_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2518_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___closed__1));
v___x_2519_ = lean_box(0);
v___x_2520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2520_, 0, v_a_2514_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
v___x_2521_ = l_Lean_mkConst(v___x_2518_, v___x_2520_);
v___x_2522_ = l_Lean_mkAppB(v___x_2521_, v___x_2506_, v_a_2505_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v___x_2522_);
v___x_2524_ = v___x_2516_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2522_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec_ref(v___x_2506_);
lean_dec(v_a_2505_);
v_a_2527_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2513_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2513_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2506_);
lean_dec(v_a_2505_);
return v___x_2507_;
}
}
else
{
lean_dec_ref(v_d_2487_);
return v___x_2504_;
}
}
else
{
uint8_t v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; lean_object* v___x_2549_; 
lean_dec_ref_known(v___x_2497_, 1);
v___x_2543_ = 1;
v___x_2544_ = l_Lean_LocalDecl_toExpr(v_d_2487_);
v___x_2545_ = lean_unsigned_to_nat(1u);
v___x_2546_ = lean_mk_empty_array_with_capacity(v___x_2545_);
v___x_2547_ = lean_array_push(v___x_2546_, v___x_2544_);
v___x_2548_ = 1;
v___x_2549_ = l_Lean_Meta_mkLetFVars(v___x_2547_, v_00_u03c6_2488_, v___x_2543_, v___x_2496_, v___x_2548_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_);
lean_dec_ref(v___x_2547_);
return v___x_2549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___boxed(lean_object* v_d_2550_, lean_object* v_00_u03c6_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg(v_d_2550_, v_00_u03c6_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal(lean_object* v_d_2560_, lean_object* v_00_u03c6_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v___x_2574_; 
v___x_2574_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg(v_d_2560_, v_00_u03c6_2561_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___boxed(lean_object* v_d_2575_, lean_object* v_00_u03c6_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal(v_d_2575_, v_00_u03c6_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
lean_dec(v_a_2583_);
lean_dec_ref(v_a_2582_);
lean_dec(v_a_2581_);
lean_dec_ref(v_a_2580_);
lean_dec(v_a_2579_);
lean_dec(v_a_2578_);
lean_dec_ref(v_a_2577_);
return v_res_2589_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__2(void){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = lean_box(0);
v___x_2594_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__1));
v___x_2595_ = l_Lean_mkConst(v___x_2594_, v___x_2593_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(lean_object* v_ps_2596_, lean_object* v_lo_2597_, lean_object* v_hi_2598_){
_start:
{
uint8_t v___x_2599_; 
v___x_2599_ = lean_nat_dec_eq(v_hi_2598_, v_lo_2597_);
if (v___x_2599_ == 0)
{
lean_object* v___x_2600_; lean_object* v___x_2601_; uint8_t v___x_2602_; 
v___x_2600_ = lean_unsigned_to_nat(1u);
v___x_2601_ = lean_nat_add(v_lo_2597_, v___x_2600_);
v___x_2602_ = lean_nat_dec_eq(v_hi_2598_, v___x_2601_);
lean_dec(v___x_2601_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; lean_object* v_mid_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2603_ = lean_nat_add(v_lo_2597_, v_hi_2598_);
v_mid_2604_ = lean_nat_shiftr(v___x_2603_, v___x_2600_);
lean_dec(v___x_2603_);
v___x_2605_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(v_ps_2596_, v_lo_2597_, v_mid_2604_);
v___x_2606_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(v_ps_2596_, v_mid_2604_, v_hi_2598_);
lean_dec(v_mid_2604_);
v___x_2607_ = l_Lean_mkOr(v___x_2605_, v___x_2606_);
return v___x_2607_;
}
else
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2608_ = l_Lean_instInhabitedExpr;
v___x_2609_ = lean_array_get_borrowed(v___x_2608_, v_ps_2596_, v_lo_2597_);
lean_inc(v___x_2609_);
return v___x_2609_;
}
}
else
{
lean_object* v___x_2610_; 
v___x_2610_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__2, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__2_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__2);
return v___x_2610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___boxed(lean_object* v_ps_2611_, lean_object* v_lo_2612_, lean_object* v_hi_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(v_ps_2611_, v_lo_2612_, v_hi_2613_);
lean_dec(v_hi_2613_);
lean_dec(v_lo_2612_);
lean_dec_ref(v_ps_2611_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(lean_object* v_msg_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_ref_2621_; lean_object* v___x_2622_; lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2631_; 
v_ref_2621_ = lean_ctor_get(v___y_2618_, 2);
v___x_2622_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2_spec__3(v_msg_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2625_ = v___x_2622_;
v_isShared_2626_ = v_isSharedCheck_2631_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2622_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2631_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2627_; lean_object* v___x_2629_; 
lean_inc(v_ref_2621_);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v_ref_2621_);
lean_ctor_set(v___x_2627_, 1, v_a_2623_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set_tag(v___x_2625_, 1);
lean_ctor_set(v___x_2625_, 0, v___x_2627_);
v___x_2629_ = v___x_2625_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2627_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg___boxed(lean_object* v_msg_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v_msg_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
return v_res_2638_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__1(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__0));
v___x_2641_ = l_Lean_stringToMessageData(v___x_2640_);
return v___x_2641_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__6(void){
_start:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2649_ = lean_box(0);
v___x_2650_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__5));
v___x_2651_ = l_Lean_mkConst(v___x_2650_, v___x_2649_);
return v___x_2651_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__9(void){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2656_ = lean_box(0);
v___x_2657_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__8));
v___x_2658_ = l_Lean_mkConst(v___x_2657_, v___x_2656_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(lean_object* v_00_u03c6_2659_, lean_object* v_i_2660_, lean_object* v_lo_2661_, lean_object* v_hi_2662_, lean_object* v_k_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_){
_start:
{
lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___x_2678_; lean_object* v___x_2679_; uint8_t v___x_2680_; 
v___x_2678_ = lean_unsigned_to_nat(1u);
v___x_2679_ = lean_nat_add(v_lo_2661_, v___x_2678_);
v___x_2680_ = lean_nat_dec_eq(v_hi_2662_, v___x_2679_);
lean_dec(v___x_2679_);
if (v___x_2680_ == 0)
{
lean_object* v___x_2681_; uint8_t v___x_2682_; 
v___x_2681_ = l_Lean_Expr_cleanupAnnotations(v_00_u03c6_2659_);
v___x_2682_ = l_Lean_Expr_isApp(v___x_2681_);
if (v___x_2682_ == 0)
{
lean_dec_ref(v___x_2681_);
lean_dec_ref(v_k_2663_);
v___y_2670_ = v_a_2664_;
v___y_2671_ = v_a_2665_;
v___y_2672_ = v_a_2666_;
v___y_2673_ = v_a_2667_;
goto v___jp_2669_;
}
else
{
lean_object* v___x_2683_; uint8_t v___x_2684_; 
v___x_2683_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2681_);
v___x_2684_ = l_Lean_Expr_isApp(v___x_2683_);
if (v___x_2684_ == 0)
{
lean_dec_ref(v___x_2683_);
lean_dec_ref(v___x_2681_);
lean_dec_ref(v_k_2663_);
v___y_2670_ = v_a_2664_;
v___y_2671_ = v_a_2665_;
v___y_2672_ = v_a_2666_;
v___y_2673_ = v_a_2667_;
goto v___jp_2669_;
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; 
v___x_2685_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2683_);
v___x_2686_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__3));
v___x_2687_ = l_Lean_Expr_isConstOf(v___x_2685_, v___x_2686_);
lean_dec_ref(v___x_2685_);
if (v___x_2687_ == 0)
{
lean_dec_ref(v___x_2683_);
lean_dec_ref(v___x_2681_);
lean_dec_ref(v_k_2663_);
v___y_2670_ = v_a_2664_;
v___y_2671_ = v_a_2665_;
v___y_2672_ = v_a_2666_;
v___y_2673_ = v_a_2667_;
goto v___jp_2669_;
}
else
{
lean_object* v_arg_2688_; lean_object* v_arg_2689_; lean_object* v___x_2690_; lean_object* v_mid_2691_; uint8_t v___x_2692_; 
lean_dec_ref(v_00_u03c6_2659_);
v_arg_2688_ = lean_ctor_get(v___x_2681_, 1);
lean_inc_ref(v_arg_2688_);
lean_dec_ref(v___x_2681_);
v_arg_2689_ = lean_ctor_get(v___x_2683_, 1);
lean_inc_ref(v_arg_2689_);
lean_dec_ref(v___x_2683_);
v___x_2690_ = lean_nat_add(v_lo_2661_, v_hi_2662_);
v_mid_2691_ = lean_nat_shiftr(v___x_2690_, v___x_2678_);
lean_dec(v___x_2690_);
v___x_2692_ = lean_nat_dec_lt(v_i_2660_, v_mid_2691_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; 
lean_inc_ref(v_arg_2688_);
v___x_2693_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(v_arg_2688_, v_i_2660_, v_mid_2691_, v_hi_2662_, v_k_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
lean_dec(v_mid_2691_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2703_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2696_ = v___x_2693_;
v_isShared_2697_ = v_isSharedCheck_2703_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2693_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2703_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2701_; 
v___x_2698_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__6, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__6_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__6);
v___x_2699_ = l_Lean_mkApp3(v___x_2698_, v_arg_2689_, v_arg_2688_, v_a_2694_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v___x_2699_);
v___x_2701_ = v___x_2696_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
else
{
lean_dec_ref(v_arg_2689_);
lean_dec_ref(v_arg_2688_);
return v___x_2693_;
}
}
else
{
lean_object* v___x_2704_; 
lean_inc_ref(v_arg_2689_);
v___x_2704_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(v_arg_2689_, v_i_2660_, v_lo_2661_, v_mid_2691_, v_k_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
lean_dec(v_mid_2691_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2714_; 
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2707_ = v___x_2704_;
v_isShared_2708_ = v_isSharedCheck_2714_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2704_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2714_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2712_; 
v___x_2709_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__9, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__9);
v___x_2710_ = l_Lean_mkApp3(v___x_2709_, v_arg_2689_, v_arg_2688_, v_a_2705_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v___x_2710_);
v___x_2712_ = v___x_2707_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2710_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
else
{
lean_dec_ref(v_arg_2689_);
lean_dec_ref(v_arg_2688_);
return v___x_2704_;
}
}
}
}
}
}
else
{
lean_object* v___x_2715_; 
lean_inc(v_a_2667_);
lean_inc_ref(v_a_2666_);
lean_inc(v_a_2665_);
lean_inc_ref(v_a_2664_);
v___x_2715_ = lean_apply_6(v_k_2663_, v_00_u03c6_2659_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, lean_box(0));
return v___x_2715_;
}
v___jp_2669_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2674_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__1, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__1);
v___x_2675_ = l_Lean_indentExpr(v_00_u03c6_2659_);
v___x_2676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2674_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
v___x_2677_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v___x_2676_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
return v___x_2677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___boxed(lean_object* v_00_u03c6_2716_, lean_object* v_i_2717_, lean_object* v_lo_2718_, lean_object* v_hi_2719_, lean_object* v_k_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(v_00_u03c6_2716_, v_i_2717_, v_lo_2718_, v_hi_2719_, v_k_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_);
lean_dec(v_a_2724_);
lean_dec_ref(v_a_2723_);
lean_dec(v_a_2722_);
lean_dec_ref(v_a_2721_);
lean_dec(v_hi_2719_);
lean_dec(v_lo_2718_);
lean_dec(v_i_2717_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0(lean_object* v_00_u03b1_2727_, lean_object* v_msg_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v_msg_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___boxed(lean_object* v_00_u03b1_2735_, lean_object* v_msg_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0(v_00_u03b1_2735_, v_msg_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(lean_object* v_lctx_2743_, lean_object* v_localInsts_2744_, lean_object* v_x_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v___f_2758_; lean_object* v___x_2759_; 
lean_inc(v___y_2752_);
lean_inc_ref(v___y_2751_);
lean_inc(v___y_2750_);
lean_inc_ref(v___y_2749_);
lean_inc(v___y_2748_);
lean_inc(v___y_2747_);
lean_inc_ref(v___y_2746_);
v___f_2758_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_2758_, 0, v_x_2745_);
lean_closure_set(v___f_2758_, 1, v___y_2746_);
lean_closure_set(v___f_2758_, 2, v___y_2747_);
lean_closure_set(v___f_2758_, 3, v___y_2748_);
lean_closure_set(v___f_2758_, 4, v___y_2749_);
lean_closure_set(v___f_2758_, 5, v___y_2750_);
lean_closure_set(v___f_2758_, 6, v___y_2751_);
lean_closure_set(v___f_2758_, 7, v___y_2752_);
v___x_2759_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2743_, v_localInsts_2744_, v___f_2758_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
if (lean_obj_tag(v___x_2759_) == 0)
{
return v___x_2759_;
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg___boxed(lean_object* v_lctx_2768_, lean_object* v_localInsts_2769_, lean_object* v_x_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(v_lctx_2768_, v_localInsts_2769_, v_x_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6(lean_object* v_00_u03b1_2784_, lean_object* v_lctx_2785_, lean_object* v_localInsts_2786_, lean_object* v_x_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(v_lctx_2785_, v_localInsts_2786_, v_x_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___boxed(lean_object* v_00_u03b1_2801_, lean_object* v_lctx_2802_, lean_object* v_localInsts_2803_, lean_object* v_x_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6(v_00_u03b1_2801_, v_lctx_2802_, v_localInsts_2803_, v_x_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg(lean_object* v_a_2818_, lean_object* v_x_2819_){
_start:
{
if (lean_obj_tag(v_x_2819_) == 0)
{
lean_object* v___x_2820_; 
v___x_2820_ = lean_box(0);
return v___x_2820_;
}
else
{
lean_object* v_key_2821_; lean_object* v_value_2822_; lean_object* v_tail_2823_; uint8_t v___x_2824_; 
v_key_2821_ = lean_ctor_get(v_x_2819_, 0);
v_value_2822_ = lean_ctor_get(v_x_2819_, 1);
v_tail_2823_ = lean_ctor_get(v_x_2819_, 2);
v___x_2824_ = l_Lean_instBEqFVarId_beq(v_key_2821_, v_a_2818_);
if (v___x_2824_ == 0)
{
v_x_2819_ = v_tail_2823_;
goto _start;
}
else
{
lean_object* v___x_2826_; 
lean_inc(v_value_2822_);
v___x_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2826_, 0, v_value_2822_);
return v___x_2826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg___boxed(lean_object* v_a_2827_, lean_object* v_x_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg(v_a_2827_, v_x_2828_);
lean_dec(v_x_2828_);
lean_dec(v_a_2827_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg(lean_object* v_m_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v_buckets_2832_; lean_object* v___x_2833_; uint64_t v___x_2834_; uint64_t v___x_2835_; uint64_t v___x_2836_; uint64_t v_fold_2837_; uint64_t v___x_2838_; uint64_t v___x_2839_; uint64_t v___x_2840_; size_t v___x_2841_; size_t v___x_2842_; size_t v___x_2843_; size_t v___x_2844_; size_t v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v_buckets_2832_ = lean_ctor_get(v_m_2830_, 1);
v___x_2833_ = lean_array_get_size(v_buckets_2832_);
v___x_2834_ = l_Lean_instHashableFVarId_hash(v_a_2831_);
v___x_2835_ = 32ULL;
v___x_2836_ = lean_uint64_shift_right(v___x_2834_, v___x_2835_);
v_fold_2837_ = lean_uint64_xor(v___x_2834_, v___x_2836_);
v___x_2838_ = 16ULL;
v___x_2839_ = lean_uint64_shift_right(v_fold_2837_, v___x_2838_);
v___x_2840_ = lean_uint64_xor(v_fold_2837_, v___x_2839_);
v___x_2841_ = lean_uint64_to_usize(v___x_2840_);
v___x_2842_ = lean_usize_of_nat(v___x_2833_);
v___x_2843_ = ((size_t)1ULL);
v___x_2844_ = lean_usize_sub(v___x_2842_, v___x_2843_);
v___x_2845_ = lean_usize_land(v___x_2841_, v___x_2844_);
v___x_2846_ = lean_array_uget_borrowed(v_buckets_2832_, v___x_2845_);
v___x_2847_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg(v_a_2831_, v___x_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg___boxed(lean_object* v_m_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg(v_m_2848_, v_a_2849_);
lean_dec(v_a_2849_);
lean_dec_ref(v_m_2848_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4___redArg(lean_object* v_a_2851_, lean_object* v_b_2852_, lean_object* v_x_2853_){
_start:
{
if (lean_obj_tag(v_x_2853_) == 0)
{
lean_dec(v_b_2852_);
lean_dec(v_a_2851_);
return v_x_2853_;
}
else
{
lean_object* v_key_2854_; lean_object* v_value_2855_; lean_object* v_tail_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2868_; 
v_key_2854_ = lean_ctor_get(v_x_2853_, 0);
v_value_2855_ = lean_ctor_get(v_x_2853_, 1);
v_tail_2856_ = lean_ctor_get(v_x_2853_, 2);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_x_2853_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2858_ = v_x_2853_;
v_isShared_2859_ = v_isSharedCheck_2868_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_tail_2856_);
lean_inc(v_value_2855_);
lean_inc(v_key_2854_);
lean_dec(v_x_2853_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2868_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
uint8_t v___x_2860_; 
v___x_2860_ = l_Lean_instBEqFVarId_beq(v_key_2854_, v_a_2851_);
if (v___x_2860_ == 0)
{
lean_object* v___x_2861_; lean_object* v___x_2863_; 
v___x_2861_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4___redArg(v_a_2851_, v_b_2852_, v_tail_2856_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 2, v___x_2861_);
v___x_2863_ = v___x_2858_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_key_2854_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v_value_2855_);
lean_ctor_set(v_reuseFailAlloc_2864_, 2, v___x_2861_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
else
{
lean_object* v___x_2866_; 
lean_dec(v_value_2855_);
lean_dec(v_key_2854_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 1, v_b_2852_);
lean_ctor_set(v___x_2858_, 0, v_a_2851_);
v___x_2866_ = v___x_2858_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2851_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v_b_2852_);
lean_ctor_set(v_reuseFailAlloc_2867_, 2, v_tail_2856_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg(lean_object* v_a_2869_, lean_object* v_x_2870_){
_start:
{
if (lean_obj_tag(v_x_2870_) == 0)
{
uint8_t v___x_2871_; 
v___x_2871_ = 0;
return v___x_2871_;
}
else
{
lean_object* v_key_2872_; lean_object* v_tail_2873_; uint8_t v___x_2874_; 
v_key_2872_ = lean_ctor_get(v_x_2870_, 0);
v_tail_2873_ = lean_ctor_get(v_x_2870_, 2);
v___x_2874_ = l_Lean_instBEqFVarId_beq(v_key_2872_, v_a_2869_);
if (v___x_2874_ == 0)
{
v_x_2870_ = v_tail_2873_;
goto _start;
}
else
{
return v___x_2874_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg___boxed(lean_object* v_a_2876_, lean_object* v_x_2877_){
_start:
{
uint8_t v_res_2878_; lean_object* v_r_2879_; 
v_res_2878_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg(v_a_2876_, v_x_2877_);
lean_dec(v_x_2877_);
lean_dec(v_a_2876_);
v_r_2879_ = lean_box(v_res_2878_);
return v_r_2879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5_spec__11___redArg(lean_object* v_x_2880_, lean_object* v_x_2881_){
_start:
{
if (lean_obj_tag(v_x_2881_) == 0)
{
return v_x_2880_;
}
else
{
lean_object* v_key_2882_; lean_object* v_value_2883_; lean_object* v_tail_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2907_; 
v_key_2882_ = lean_ctor_get(v_x_2881_, 0);
v_value_2883_ = lean_ctor_get(v_x_2881_, 1);
v_tail_2884_ = lean_ctor_get(v_x_2881_, 2);
v_isSharedCheck_2907_ = !lean_is_exclusive(v_x_2881_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2886_ = v_x_2881_;
v_isShared_2887_ = v_isSharedCheck_2907_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_tail_2884_);
lean_inc(v_value_2883_);
lean_inc(v_key_2882_);
lean_dec(v_x_2881_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2907_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2888_; uint64_t v___x_2889_; uint64_t v___x_2890_; uint64_t v___x_2891_; uint64_t v_fold_2892_; uint64_t v___x_2893_; uint64_t v___x_2894_; uint64_t v___x_2895_; size_t v___x_2896_; size_t v___x_2897_; size_t v___x_2898_; size_t v___x_2899_; size_t v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2903_; 
v___x_2888_ = lean_array_get_size(v_x_2880_);
v___x_2889_ = l_Lean_instHashableFVarId_hash(v_key_2882_);
v___x_2890_ = 32ULL;
v___x_2891_ = lean_uint64_shift_right(v___x_2889_, v___x_2890_);
v_fold_2892_ = lean_uint64_xor(v___x_2889_, v___x_2891_);
v___x_2893_ = 16ULL;
v___x_2894_ = lean_uint64_shift_right(v_fold_2892_, v___x_2893_);
v___x_2895_ = lean_uint64_xor(v_fold_2892_, v___x_2894_);
v___x_2896_ = lean_uint64_to_usize(v___x_2895_);
v___x_2897_ = lean_usize_of_nat(v___x_2888_);
v___x_2898_ = ((size_t)1ULL);
v___x_2899_ = lean_usize_sub(v___x_2897_, v___x_2898_);
v___x_2900_ = lean_usize_land(v___x_2896_, v___x_2899_);
v___x_2901_ = lean_array_uget_borrowed(v_x_2880_, v___x_2900_);
lean_inc(v___x_2901_);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 2, v___x_2901_);
v___x_2903_ = v___x_2886_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_key_2882_);
lean_ctor_set(v_reuseFailAlloc_2906_, 1, v_value_2883_);
lean_ctor_set(v_reuseFailAlloc_2906_, 2, v___x_2901_);
v___x_2903_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
lean_object* v___x_2904_; 
v___x_2904_ = lean_array_uset(v_x_2880_, v___x_2900_, v___x_2903_);
v_x_2880_ = v___x_2904_;
v_x_2881_ = v_tail_2884_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5___redArg(lean_object* v_i_2908_, lean_object* v_source_2909_, lean_object* v_target_2910_){
_start:
{
lean_object* v___x_2911_; uint8_t v___x_2912_; 
v___x_2911_ = lean_array_get_size(v_source_2909_);
v___x_2912_ = lean_nat_dec_lt(v_i_2908_, v___x_2911_);
if (v___x_2912_ == 0)
{
lean_dec_ref(v_source_2909_);
lean_dec(v_i_2908_);
return v_target_2910_;
}
else
{
lean_object* v_es_2913_; lean_object* v___x_2914_; lean_object* v_source_2915_; lean_object* v_target_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v_es_2913_ = lean_array_fget(v_source_2909_, v_i_2908_);
v___x_2914_ = lean_box(0);
v_source_2915_ = lean_array_fset(v_source_2909_, v_i_2908_, v___x_2914_);
v_target_2916_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5_spec__11___redArg(v_target_2910_, v_es_2913_);
v___x_2917_ = lean_unsigned_to_nat(1u);
v___x_2918_ = lean_nat_add(v_i_2908_, v___x_2917_);
lean_dec(v_i_2908_);
v_i_2908_ = v___x_2918_;
v_source_2909_ = v_source_2915_;
v_target_2910_ = v_target_2916_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3___redArg(lean_object* v_data_2920_){
_start:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v_nbuckets_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2921_ = lean_array_get_size(v_data_2920_);
v___x_2922_ = lean_unsigned_to_nat(2u);
v_nbuckets_2923_ = lean_nat_mul(v___x_2921_, v___x_2922_);
v___x_2924_ = lean_unsigned_to_nat(0u);
v___x_2925_ = lean_box(0);
v___x_2926_ = lean_mk_array(v_nbuckets_2923_, v___x_2925_);
v___x_2927_ = lean_array_propagate_mark(v_data_2920_, v___x_2926_);
v___x_2928_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5___redArg(v___x_2924_, v_data_2920_, v___x_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1___redArg(lean_object* v_m_2929_, lean_object* v_a_2930_, lean_object* v_b_2931_){
_start:
{
lean_object* v_size_2932_; lean_object* v_buckets_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2976_; 
v_size_2932_ = lean_ctor_get(v_m_2929_, 0);
v_buckets_2933_ = lean_ctor_get(v_m_2929_, 1);
v_isSharedCheck_2976_ = !lean_is_exclusive(v_m_2929_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2935_ = v_m_2929_;
v_isShared_2936_ = v_isSharedCheck_2976_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_buckets_2933_);
lean_inc(v_size_2932_);
lean_dec(v_m_2929_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2976_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2937_; uint64_t v___x_2938_; uint64_t v___x_2939_; uint64_t v___x_2940_; uint64_t v_fold_2941_; uint64_t v___x_2942_; uint64_t v___x_2943_; uint64_t v___x_2944_; size_t v___x_2945_; size_t v___x_2946_; size_t v___x_2947_; size_t v___x_2948_; size_t v___x_2949_; lean_object* v_bkt_2950_; uint8_t v___x_2951_; 
v___x_2937_ = lean_array_get_size(v_buckets_2933_);
v___x_2938_ = l_Lean_instHashableFVarId_hash(v_a_2930_);
v___x_2939_ = 32ULL;
v___x_2940_ = lean_uint64_shift_right(v___x_2938_, v___x_2939_);
v_fold_2941_ = lean_uint64_xor(v___x_2938_, v___x_2940_);
v___x_2942_ = 16ULL;
v___x_2943_ = lean_uint64_shift_right(v_fold_2941_, v___x_2942_);
v___x_2944_ = lean_uint64_xor(v_fold_2941_, v___x_2943_);
v___x_2945_ = lean_uint64_to_usize(v___x_2944_);
v___x_2946_ = lean_usize_of_nat(v___x_2937_);
v___x_2947_ = ((size_t)1ULL);
v___x_2948_ = lean_usize_sub(v___x_2946_, v___x_2947_);
v___x_2949_ = lean_usize_land(v___x_2945_, v___x_2948_);
v_bkt_2950_ = lean_array_uget_borrowed(v_buckets_2933_, v___x_2949_);
v___x_2951_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg(v_a_2930_, v_bkt_2950_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; lean_object* v_size_x27_2953_; lean_object* v___x_2954_; lean_object* v_buckets_x27_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; uint8_t v___x_2961_; 
v___x_2952_ = lean_unsigned_to_nat(1u);
v_size_x27_2953_ = lean_nat_add(v_size_2932_, v___x_2952_);
lean_dec(v_size_2932_);
lean_inc(v_bkt_2950_);
v___x_2954_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2954_, 0, v_a_2930_);
lean_ctor_set(v___x_2954_, 1, v_b_2931_);
lean_ctor_set(v___x_2954_, 2, v_bkt_2950_);
v_buckets_x27_2955_ = lean_array_uset(v_buckets_2933_, v___x_2949_, v___x_2954_);
v___x_2956_ = lean_unsigned_to_nat(4u);
v___x_2957_ = lean_nat_mul(v_size_x27_2953_, v___x_2956_);
v___x_2958_ = lean_unsigned_to_nat(3u);
v___x_2959_ = lean_nat_div(v___x_2957_, v___x_2958_);
lean_dec(v___x_2957_);
v___x_2960_ = lean_array_get_size(v_buckets_x27_2955_);
v___x_2961_ = lean_nat_dec_le(v___x_2959_, v___x_2960_);
lean_dec(v___x_2959_);
if (v___x_2961_ == 0)
{
lean_object* v_val_2962_; lean_object* v___x_2964_; 
v_val_2962_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3___redArg(v_buckets_x27_2955_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 1, v_val_2962_);
lean_ctor_set(v___x_2935_, 0, v_size_x27_2953_);
v___x_2964_ = v___x_2935_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_size_x27_2953_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_val_2962_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
else
{
lean_object* v___x_2967_; 
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 1, v_buckets_x27_2955_);
lean_ctor_set(v___x_2935_, 0, v_size_x27_2953_);
v___x_2967_ = v___x_2935_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_size_x27_2953_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_buckets_x27_2955_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
else
{
lean_object* v___x_2969_; lean_object* v_buckets_x27_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2974_; 
lean_inc(v_bkt_2950_);
v___x_2969_ = lean_box(0);
v_buckets_x27_2970_ = lean_array_uset(v_buckets_2933_, v___x_2949_, v___x_2969_);
v___x_2971_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4___redArg(v_a_2930_, v_b_2931_, v_bkt_2950_);
v___x_2972_ = lean_array_uset(v_buckets_x27_2970_, v___x_2949_, v___x_2971_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 1, v___x_2972_);
v___x_2974_ = v___x_2935_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_size_2932_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg(lean_object* v_jumps_2977_, lean_object* v_i_2978_, lean_object* v_range_2979_, lean_object* v_b_2980_, lean_object* v_i_2981_){
_start:
{
lean_object* v_stop_2983_; lean_object* v_step_2984_; lean_object* v_a_2986_; lean_object* v_groups_2990_; lean_object* v_byLocal_2991_; uint8_t v___x_2997_; 
v_stop_2983_ = lean_ctor_get(v_range_2979_, 1);
v_step_2984_ = lean_ctor_get(v_range_2979_, 2);
v___x_2997_ = lean_nat_dec_lt(v_i_2981_, v_stop_2983_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; 
lean_dec(v_i_2981_);
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v_b_2980_);
return v___x_2998_;
}
else
{
lean_object* v_fst_2999_; lean_object* v_snd_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3026_; 
v_fst_2999_ = lean_ctor_get(v_b_2980_, 0);
v_snd_3000_ = lean_ctor_get(v_b_2980_, 1);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_b_2980_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3002_ = v_b_2980_;
v_isShared_3003_ = v_isSharedCheck_3026_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_snd_3000_);
lean_inc(v_fst_2999_);
lean_dec(v_b_2980_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3026_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___y_3005_; lean_object* v___x_3009_; lean_object* v_snd_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___x_3009_ = lean_array_fget_borrowed(v_jumps_2977_, v_i_2981_);
v_snd_3010_ = lean_ctor_get(v___x_3009_, 1);
v___x_3011_ = lean_array_get_size(v_snd_3010_);
v___x_3012_ = lean_nat_dec_lt(v_i_2978_, v___x_3011_);
if (v___x_3012_ == 0)
{
lean_del_object(v___x_3002_);
v_groups_2990_ = v_fst_2999_;
v_byLocal_2991_ = v_snd_3000_;
goto v___jp_2989_;
}
else
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = lean_array_fget_borrowed(v_snd_3010_, v_i_2978_);
v___x_3014_ = l_Lean_LocalDecl_fvarId(v___x_3013_);
v___x_3015_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg(v_snd_3000_, v___x_3014_);
if (lean_obj_tag(v___x_3015_) == 1)
{
lean_object* v_val_3016_; lean_object* v___x_3017_; uint8_t v___x_3018_; 
lean_dec(v___x_3014_);
v_val_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_val_3016_);
lean_dec_ref_known(v___x_3015_, 1);
v___x_3017_ = lean_array_get_size(v_fst_2999_);
v___x_3018_ = lean_nat_dec_lt(v_val_3016_, v___x_3017_);
if (v___x_3018_ == 0)
{
lean_dec(v_val_3016_);
v___y_3005_ = v_fst_2999_;
goto v___jp_3004_;
}
else
{
lean_object* v_v_3019_; lean_object* v___x_3020_; lean_object* v_xs_x27_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v_v_3019_ = lean_array_fget(v_fst_2999_, v_val_3016_);
v___x_3020_ = lean_box(0);
v_xs_x27_3021_ = lean_array_fset(v_fst_2999_, v_val_3016_, v___x_3020_);
lean_inc(v_i_2981_);
v___x_3022_ = lean_array_push(v_v_3019_, v_i_2981_);
v___x_3023_ = lean_array_fset(v_xs_x27_3021_, v_val_3016_, v___x_3022_);
lean_dec(v_val_3016_);
v___y_3005_ = v___x_3023_;
goto v___jp_3004_;
}
}
else
{
lean_object* v___x_3024_; lean_object* v_byLocal_3025_; 
lean_dec(v___x_3015_);
lean_del_object(v___x_3002_);
v___x_3024_ = lean_array_get_size(v_fst_2999_);
v_byLocal_3025_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1___redArg(v_snd_3000_, v___x_3014_, v___x_3024_);
v_groups_2990_ = v_fst_2999_;
v_byLocal_2991_ = v_byLocal_3025_;
goto v___jp_2989_;
}
}
v___jp_3004_:
{
lean_object* v___x_3007_; 
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 0, v___y_3005_);
v___x_3007_ = v___x_3002_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___y_3005_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v_snd_3000_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
v_a_2986_ = v___x_3007_;
goto v___jp_2985_;
}
}
}
}
v___jp_2985_:
{
lean_object* v___x_2987_; 
v___x_2987_ = lean_nat_add(v_i_2981_, v_step_2984_);
lean_dec(v_i_2981_);
v_b_2980_ = v_a_2986_;
v_i_2981_ = v___x_2987_;
goto _start;
}
v___jp_2989_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v_groups_2995_; lean_object* v___x_2996_; 
v___x_2992_ = lean_unsigned_to_nat(1u);
v___x_2993_ = lean_mk_empty_array_with_capacity(v___x_2992_);
lean_inc(v_i_2981_);
v___x_2994_ = lean_array_push(v___x_2993_, v_i_2981_);
v_groups_2995_ = lean_array_push(v_groups_2990_, v___x_2994_);
v___x_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2996_, 0, v_groups_2995_);
lean_ctor_set(v___x_2996_, 1, v_byLocal_2991_);
v_a_2986_ = v___x_2996_;
goto v___jp_2985_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg___boxed(lean_object* v_jumps_3027_, lean_object* v_i_3028_, lean_object* v_range_3029_, lean_object* v_b_3030_, lean_object* v_i_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg(v_jumps_3027_, v_i_3028_, v_range_3029_, v_b_3030_, v_i_3031_);
lean_dec_ref(v_range_3029_);
lean_dec(v_i_3028_);
lean_dec_ref(v_jumps_3027_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(lean_object* v_g_3034_, lean_object* v___x_3035_, lean_object* v_as_3036_, size_t v_sz_3037_, size_t v_i_3038_, lean_object* v_b_3039_){
_start:
{
uint8_t v___x_3041_; 
v___x_3041_ = lean_usize_dec_lt(v_i_3038_, v_sz_3037_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3042_; 
lean_dec(v___x_3035_);
lean_dec(v_g_3034_);
v___x_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3042_, 0, v_b_3039_);
return v___x_3042_;
}
else
{
lean_object* v_a_3043_; lean_object* v_fst_3044_; lean_object* v_snd_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3057_; 
v_a_3043_ = lean_array_uget(v_as_3036_, v_i_3038_);
v_fst_3044_ = lean_ctor_get(v_a_3043_, 0);
v_snd_3045_ = lean_ctor_get(v_a_3043_, 1);
v_isSharedCheck_3057_ = !lean_is_exclusive(v_a_3043_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3047_ = v_a_3043_;
v_isShared_3048_ = v_isSharedCheck_3057_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_snd_3045_);
lean_inc(v_fst_3044_);
lean_dec(v_a_3043_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3057_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
lean_inc(v___x_3035_);
lean_inc(v_g_3034_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 1, v___x_3035_);
lean_ctor_set(v___x_3047_, 0, v_g_3034_);
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_g_3034_);
lean_ctor_set(v_reuseFailAlloc_3056_, 1, v___x_3035_);
v___x_3050_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; size_t v___x_3053_; size_t v___x_3054_; 
v___x_3051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
lean_ctor_set(v___x_3051_, 1, v_snd_3045_);
v___x_3052_ = lean_array_set(v_b_3039_, v_fst_3044_, v___x_3051_);
lean_dec(v_fst_3044_);
v___x_3053_ = ((size_t)1ULL);
v___x_3054_ = lean_usize_add(v_i_3038_, v___x_3053_);
v_i_3038_ = v___x_3054_;
v_b_3039_ = v___x_3052_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg___boxed(lean_object* v_g_3058_, lean_object* v___x_3059_, lean_object* v_as_3060_, lean_object* v_sz_3061_, lean_object* v_i_3062_, lean_object* v_b_3063_, lean_object* v___y_3064_){
_start:
{
size_t v_sz_boxed_3065_; size_t v_i_boxed_3066_; lean_object* v_res_3067_; 
v_sz_boxed_3065_ = lean_unbox_usize(v_sz_3061_);
lean_dec(v_sz_3061_);
v_i_boxed_3066_ = lean_unbox_usize(v_i_3062_);
lean_dec(v_i_3062_);
v_res_3067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(v_g_3058_, v___x_3059_, v_as_3060_, v_sz_boxed_3065_, v_i_boxed_3066_, v_b_3063_);
lean_dec_ref(v_as_3060_);
return v_res_3067_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_Array_instInhabited___redArg();
return v___x_3068_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1(void){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3069_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__0);
v___x_3070_ = l_Lean_Elab_Tactic_VCGen_instInhabitedJump_default;
v___x_3071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
lean_ctor_set(v___x_3071_, 1, v___x_3069_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5(lean_object* v_jumps_3072_, size_t v_sz_3073_, size_t v_i_3074_, lean_object* v_bs_3075_){
_start:
{
uint8_t v___x_3076_; 
v___x_3076_ = lean_usize_dec_lt(v_i_3074_, v_sz_3073_);
if (v___x_3076_ == 0)
{
return v_bs_3075_;
}
else
{
lean_object* v___x_3077_; lean_object* v_v_3078_; lean_object* v___x_3079_; lean_object* v_bs_x27_3080_; lean_object* v___x_3081_; size_t v___x_3082_; size_t v___x_3083_; lean_object* v___x_3084_; 
v___x_3077_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1);
v_v_3078_ = lean_array_uget(v_bs_3075_, v_i_3074_);
v___x_3079_ = lean_unsigned_to_nat(0u);
v_bs_x27_3080_ = lean_array_uset(v_bs_3075_, v_i_3074_, v___x_3079_);
v___x_3081_ = lean_array_get_borrowed(v___x_3077_, v_jumps_3072_, v_v_3078_);
lean_dec(v_v_3078_);
v___x_3082_ = ((size_t)1ULL);
v___x_3083_ = lean_usize_add(v_i_3074_, v___x_3082_);
lean_inc(v___x_3081_);
v___x_3084_ = lean_array_uset(v_bs_x27_3080_, v_i_3074_, v___x_3081_);
v_i_3074_ = v___x_3083_;
v_bs_3075_ = v___x_3084_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___boxed(lean_object* v_jumps_3086_, lean_object* v_sz_3087_, lean_object* v_i_3088_, lean_object* v_bs_3089_){
_start:
{
size_t v_sz_boxed_3090_; size_t v_i_boxed_3091_; lean_object* v_res_3092_; 
v_sz_boxed_3090_ = lean_unbox_usize(v_sz_3087_);
lean_dec(v_sz_3087_);
v_i_boxed_3091_ = lean_unbox_usize(v_i_3088_);
lean_dec(v_i_3088_);
v_res_3092_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5(v_jumps_3086_, v_sz_boxed_3090_, v_i_boxed_3091_, v_bs_3089_);
lean_dec_ref(v_jumps_3086_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(lean_object* v_fst_3096_, size_t v_sz_3097_, size_t v_i_3098_, lean_object* v_bs_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
uint8_t v___x_3107_; 
v___x_3107_ = lean_usize_dec_lt(v_i_3098_, v_sz_3097_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; 
v___x_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3108_, 0, v_bs_3099_);
return v___x_3108_;
}
else
{
lean_object* v___x_3109_; lean_object* v_v_3110_; lean_object* v___x_3111_; lean_object* v_bs_x27_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3109_ = l_Lean_instInhabitedExpr;
v_v_3110_ = lean_array_uget(v_bs_3099_, v_i_3098_);
v___x_3111_ = lean_unsigned_to_nat(0u);
v_bs_x27_3112_ = lean_array_uset(v_bs_3099_, v_i_3098_, v___x_3111_);
v___x_3113_ = lean_usize_to_nat(v_i_3098_);
lean_inc(v_v_3110_);
v___x_3114_ = l_Lean_Meta_Sym_inferType(v_v_3110_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3116_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc_n(v_a_3115_, 2);
lean_dec_ref_known(v___x_3114_, 1);
v___x_3116_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_3115_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; lean_object* v_args_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; size_t v___x_3125_; size_t v___x_3126_; lean_object* v___x_3127_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_a_3117_);
lean_dec_ref_known(v___x_3116_, 1);
v_args_3118_ = lean_ctor_get(v_fst_3096_, 1);
v___x_3119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__1));
v___x_3120_ = lean_box(0);
v___x_3121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3121_, 0, v_a_3117_);
lean_ctor_set(v___x_3121_, 1, v___x_3120_);
v___x_3122_ = l_Lean_mkConst(v___x_3119_, v___x_3121_);
v___x_3123_ = lean_array_get_borrowed(v___x_3109_, v_args_3118_, v___x_3113_);
lean_dec(v___x_3113_);
lean_inc(v___x_3123_);
v___x_3124_ = l_Lean_mkApp3(v___x_3122_, v_a_3115_, v_v_3110_, v___x_3123_);
v___x_3125_ = ((size_t)1ULL);
v___x_3126_ = lean_usize_add(v_i_3098_, v___x_3125_);
v___x_3127_ = lean_array_uset(v_bs_x27_3112_, v_i_3098_, v___x_3124_);
v_i_3098_ = v___x_3126_;
v_bs_3099_ = v___x_3127_;
goto _start;
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec(v_a_3115_);
lean_dec(v___x_3113_);
lean_dec_ref(v_bs_x27_3112_);
lean_dec(v_v_3110_);
v_a_3129_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3116_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3116_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_dec(v___x_3113_);
lean_dec_ref(v_bs_x27_3112_);
lean_dec(v_v_3110_);
v_a_3137_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3114_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3114_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___boxed(lean_object* v_fst_3145_, lean_object* v_sz_3146_, lean_object* v_i_3147_, lean_object* v_bs_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
size_t v_sz_boxed_3156_; size_t v_i_boxed_3157_; lean_object* v_res_3158_; 
v_sz_boxed_3156_ = lean_unbox_usize(v_sz_3146_);
lean_dec(v_sz_3146_);
v_i_boxed_3157_ = lean_unbox_usize(v_i_3147_);
lean_dec(v_i_3147_);
v_res_3158_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(v_fst_3145_, v_sz_boxed_3156_, v_i_boxed_3157_, v_bs_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec_ref(v_fst_3145_);
return v_res_3158_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__1(void){
_start:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3161_ = lean_box(0);
v___x_3162_ = lean_unsigned_to_nat(16u);
v___x_3163_ = lean_mk_array(v___x_3162_, v___x_3161_);
return v___x_3163_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__2(void){
_start:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v_byLocal_3166_; 
v___x_3164_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__1, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__1);
v___x_3165_ = lean_unsigned_to_nat(0u);
v_byLocal_3166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byLocal_3166_, 0, v___x_3165_);
lean_ctor_set(v_byLocal_3166_, 1, v___x_3164_);
return v_byLocal_3166_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__3(void){
_start:
{
lean_object* v_byLocal_3167_; lean_object* v_groups_3168_; lean_object* v___x_3169_; 
v_byLocal_3167_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__2, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__2_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__2);
v_groups_3168_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__0));
v___x_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3169_, 0, v_groups_3168_);
lean_ctor_set(v___x_3169_, 1, v_byLocal_3167_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg(lean_object* v___x_3174_, lean_object* v_jumps_3175_, lean_object* v___x_3176_, lean_object* v_i_3177_, lean_object* v_xs_3178_, lean_object* v_range_3179_, lean_object* v_b_3180_, lean_object* v_i_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v_stop_3194_; lean_object* v_step_3195_; uint8_t v___x_3196_; 
v_stop_3194_ = lean_ctor_get(v_range_3179_, 1);
v_step_3195_ = lean_ctor_get(v_range_3179_, 2);
v___x_3196_ = lean_nat_dec_lt(v_i_3181_, v_stop_3194_);
if (v___x_3196_ == 0)
{
lean_object* v___x_3197_; 
lean_dec(v_i_3181_);
lean_dec_ref(v_xs_3178_);
lean_dec(v___x_3176_);
v___x_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3197_, 0, v_b_3180_);
return v___x_3197_;
}
else
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v_fst_3203_; lean_object* v_snd_3204_; lean_object* v_fst_3205_; lean_object* v_snd_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3302_; 
v___x_3198_ = lean_unsigned_to_nat(0u);
v___x_3199_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1);
v___x_3200_ = lean_array_fget_borrowed(v___x_3174_, v_i_3181_);
v___x_3201_ = lean_array_get_borrowed(v___x_3198_, v___x_3200_, v___x_3198_);
v___x_3202_ = lean_array_get_borrowed(v___x_3199_, v_jumps_3175_, v___x_3201_);
v_fst_3203_ = lean_ctor_get(v___x_3202_, 0);
v_snd_3204_ = lean_ctor_get(v___x_3202_, 1);
v_fst_3205_ = lean_ctor_get(v_b_3180_, 0);
v_snd_3206_ = lean_ctor_get(v_b_3180_, 1);
v_isSharedCheck_3302_ = !lean_is_exclusive(v_b_3180_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3208_ = v_b_3180_;
v_isShared_3209_ = v_isSharedCheck_3302_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_snd_3206_);
lean_inc(v_fst_3205_);
lean_dec(v_b_3180_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3302_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v_fst_3211_; lean_object* v_snd_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___x_3243_; lean_object* v___x_3244_; uint8_t v___x_3245_; 
v___x_3243_ = lean_unsigned_to_nat(1u);
v___x_3244_ = lean_array_get_size(v_snd_3204_);
v___x_3245_ = lean_nat_dec_lt(v_i_3177_, v___x_3244_);
if (v___x_3245_ == 0)
{
size_t v_sz_3246_; size_t v___x_3247_; lean_object* v___x_3248_; 
v_sz_3246_ = lean_array_size(v_xs_3178_);
v___x_3247_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3178_);
v___x_3248_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(v_fst_3203_, v_sz_3246_, v___x_3247_, v_xs_3178_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v___x_3248_, 1);
v___x_3250_ = lean_array_to_list(v_a_3249_);
v___x_3251_ = l_Lean_mkAndN(v___x_3250_);
v___x_3252_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__0));
v_fst_3211_ = v___x_3251_;
v_snd_3212_ = v___x_3252_;
v___y_3213_ = v___y_3182_;
v___y_3214_ = v___y_3183_;
v___y_3215_ = v___y_3184_;
v___y_3216_ = v___y_3185_;
v___y_3217_ = v___y_3186_;
v___y_3218_ = v___y_3187_;
v___y_3219_ = v___y_3188_;
v___y_3220_ = v___y_3189_;
v___y_3221_ = v___y_3190_;
v___y_3222_ = v___y_3191_;
v___y_3223_ = v___y_3192_;
goto v___jp_3210_;
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_del_object(v___x_3208_);
lean_dec(v_snd_3206_);
lean_dec(v_fst_3205_);
lean_dec(v_i_3181_);
lean_dec_ref(v_xs_3178_);
lean_dec(v___x_3176_);
v_a_3253_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3248_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3248_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
else
{
lean_object* v___x_3261_; size_t v_sz_3262_; size_t v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3261_ = lean_array_fget_borrowed(v_snd_3204_, v_i_3177_);
v_sz_3262_ = lean_array_size(v___x_3200_);
v___x_3263_ = ((size_t)0ULL);
lean_inc(v___x_3200_);
v___x_3264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5(v_jumps_3175_, v_sz_3262_, v___x_3263_, v___x_3200_);
v___x_3265_ = lean_nat_add(v_i_3177_, v___x_3243_);
lean_inc_ref(v_xs_3178_);
v___x_3266_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(v_xs_3178_, v___x_3264_, v___x_3265_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
lean_dec(v___x_3265_);
lean_dec_ref(v___x_3264_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v_fst_3268_; lean_object* v_snd_3269_; lean_object* v_proof_3270_; lean_object* v___x_3271_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3267_);
lean_dec_ref_known(v___x_3266_, 1);
v_fst_3268_ = lean_ctor_get(v_a_3267_, 0);
lean_inc(v_fst_3268_);
v_snd_3269_ = lean_ctor_get(v_a_3267_, 1);
lean_inc(v_snd_3269_);
lean_dec(v_a_3267_);
v_proof_3270_ = lean_ctor_get(v_fst_3203_, 0);
lean_inc(v_proof_3270_);
v___x_3271_ = l_Lean_MVarId_getDecl(v_proof_3270_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v_lctx_3273_; lean_object* v_localInstances_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref_known(v___x_3271_, 1);
v_lctx_3273_ = lean_ctor_get(v_a_3272_, 1);
lean_inc_ref(v_lctx_3273_);
v_localInstances_3274_ = lean_ctor_get(v_a_3272_, 4);
lean_inc_ref(v_localInstances_3274_);
lean_dec(v_a_3272_);
lean_inc(v___x_3261_);
v___x_3275_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___boxed), 14, 2);
lean_closure_set(v___x_3275_, 0, v___x_3261_);
lean_closure_set(v___x_3275_, 1, v_fst_3268_);
v___x_3276_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(v_lctx_3273_, v_localInstances_3274_, v___x_3275_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3277_);
lean_dec_ref_known(v___x_3276_, 1);
v_fst_3211_ = v_a_3277_;
v_snd_3212_ = v_snd_3269_;
v___y_3213_ = v___y_3182_;
v___y_3214_ = v___y_3183_;
v___y_3215_ = v___y_3184_;
v___y_3216_ = v___y_3185_;
v___y_3217_ = v___y_3186_;
v___y_3218_ = v___y_3187_;
v___y_3219_ = v___y_3188_;
v___y_3220_ = v___y_3189_;
v___y_3221_ = v___y_3190_;
v___y_3222_ = v___y_3191_;
v___y_3223_ = v___y_3192_;
goto v___jp_3210_;
}
else
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3285_; 
lean_dec(v_snd_3269_);
lean_del_object(v___x_3208_);
lean_dec(v_snd_3206_);
lean_dec(v_fst_3205_);
lean_dec(v_i_3181_);
lean_dec_ref(v_xs_3178_);
lean_dec(v___x_3176_);
v_a_3278_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3280_ = v___x_3276_;
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3276_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3283_; 
if (v_isShared_3281_ == 0)
{
v___x_3283_ = v___x_3280_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
lean_dec(v_snd_3269_);
lean_dec(v_fst_3268_);
lean_del_object(v___x_3208_);
lean_dec(v_snd_3206_);
lean_dec(v_fst_3205_);
lean_dec(v_i_3181_);
lean_dec_ref(v_xs_3178_);
lean_dec(v___x_3176_);
v_a_3286_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3271_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3271_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
else
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
lean_del_object(v___x_3208_);
lean_dec(v_snd_3206_);
lean_dec(v_fst_3205_);
lean_dec(v_i_3181_);
lean_dec_ref(v_xs_3178_);
lean_dec(v___x_3176_);
v_a_3294_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3266_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3266_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
v___jp_3210_:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; size_t v_sz_3226_; size_t v___x_3227_; lean_object* v___x_3228_; 
v___x_3224_ = lean_array_push(v_fst_3205_, v_fst_3211_);
v___x_3225_ = l_Array_zip___redArg(v___x_3200_, v_snd_3212_);
lean_dec_ref(v_snd_3212_);
v_sz_3226_ = lean_array_size(v___x_3225_);
v___x_3227_ = ((size_t)0ULL);
lean_inc(v___x_3176_);
lean_inc(v_i_3181_);
v___x_3228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(v_i_3181_, v___x_3176_, v___x_3225_, v_sz_3226_, v___x_3227_, v_snd_3206_);
lean_dec_ref(v___x_3225_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; lean_object* v___x_3231_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3229_);
lean_dec_ref_known(v___x_3228_, 1);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 1, v_a_3229_);
lean_ctor_set(v___x_3208_, 0, v___x_3224_);
v___x_3231_ = v___x_3208_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3224_);
lean_ctor_set(v_reuseFailAlloc_3234_, 1, v_a_3229_);
v___x_3231_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
lean_object* v___x_3232_; 
v___x_3232_ = lean_nat_add(v_i_3181_, v_step_3195_);
lean_dec(v_i_3181_);
v_b_3180_ = v___x_3231_;
v_i_3181_ = v___x_3232_;
goto _start;
}
}
else
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
lean_dec_ref(v___x_3224_);
lean_del_object(v___x_3208_);
lean_dec(v_i_3181_);
lean_dec_ref(v_xs_3178_);
lean_dec(v___x_3176_);
v_a_3235_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3228_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3228_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg(lean_object* v___x_3303_, lean_object* v___x_3304_, lean_object* v_jumps_3305_, lean_object* v_i_3306_, lean_object* v_xs_3307_, lean_object* v_range_3308_, lean_object* v_b_3309_, lean_object* v_i_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v_stop_3323_; lean_object* v_step_3324_; uint8_t v___x_3325_; 
v_stop_3323_ = lean_ctor_get(v_range_3308_, 1);
v_step_3324_ = lean_ctor_get(v_range_3308_, 2);
v___x_3325_ = lean_nat_dec_lt(v_i_3310_, v_stop_3323_);
if (v___x_3325_ == 0)
{
lean_object* v___x_3326_; 
lean_dec(v_i_3310_);
lean_dec_ref(v_xs_3307_);
lean_dec(v___x_3303_);
v___x_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3326_, 0, v_b_3309_);
return v___x_3326_;
}
else
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v_fst_3332_; lean_object* v_snd_3333_; lean_object* v_fst_3334_; lean_object* v_snd_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3432_; 
v___x_3327_ = lean_unsigned_to_nat(0u);
v___x_3328_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1);
v___x_3329_ = lean_array_fget_borrowed(v___x_3304_, v_i_3310_);
v___x_3330_ = lean_array_get_borrowed(v___x_3327_, v___x_3329_, v___x_3327_);
v___x_3331_ = lean_array_get_borrowed(v___x_3328_, v_jumps_3305_, v___x_3330_);
v_fst_3332_ = lean_ctor_get(v___x_3331_, 0);
v_snd_3333_ = lean_ctor_get(v___x_3331_, 1);
v_fst_3334_ = lean_ctor_get(v_b_3309_, 0);
v_snd_3335_ = lean_ctor_get(v_b_3309_, 1);
v_isSharedCheck_3432_ = !lean_is_exclusive(v_b_3309_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3337_ = v_b_3309_;
v_isShared_3338_ = v_isSharedCheck_3432_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_snd_3335_);
lean_inc(v_fst_3334_);
lean_dec(v_b_3309_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3432_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v_fst_3340_; lean_object* v_snd_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___x_3372_; lean_object* v___x_3373_; uint8_t v___x_3374_; 
v___x_3372_ = lean_unsigned_to_nat(1u);
v___x_3373_ = lean_array_get_size(v_snd_3333_);
v___x_3374_ = lean_nat_dec_lt(v_i_3306_, v___x_3373_);
if (v___x_3374_ == 0)
{
size_t v_sz_3375_; size_t v___x_3376_; lean_object* v___x_3377_; 
v_sz_3375_ = lean_array_size(v_xs_3307_);
v___x_3376_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3307_);
v___x_3377_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(v_fst_3332_, v_sz_3375_, v___x_3376_, v_xs_3307_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3378_);
lean_dec_ref_known(v___x_3377_, 1);
v___x_3379_ = lean_array_to_list(v_a_3378_);
v___x_3380_ = l_Lean_mkAndN(v___x_3379_);
v___x_3381_ = lean_mk_empty_array_with_capacity(v___x_3372_);
lean_dec_ref(v___x_3381_);
v___x_3382_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__0));
v_fst_3340_ = v___x_3380_;
v_snd_3341_ = v___x_3382_;
v___y_3342_ = v___y_3311_;
v___y_3343_ = v___y_3312_;
v___y_3344_ = v___y_3313_;
v___y_3345_ = v___y_3314_;
v___y_3346_ = v___y_3315_;
v___y_3347_ = v___y_3316_;
v___y_3348_ = v___y_3317_;
v___y_3349_ = v___y_3318_;
v___y_3350_ = v___y_3319_;
v___y_3351_ = v___y_3320_;
v___y_3352_ = v___y_3321_;
goto v___jp_3339_;
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
lean_del_object(v___x_3337_);
lean_dec(v_snd_3335_);
lean_dec(v_fst_3334_);
lean_dec(v_i_3310_);
lean_dec_ref(v_xs_3307_);
lean_dec(v___x_3303_);
v_a_3383_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3377_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3377_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
else
{
lean_object* v___x_3391_; size_t v_sz_3392_; size_t v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3391_ = lean_array_fget_borrowed(v_snd_3333_, v_i_3306_);
v_sz_3392_ = lean_array_size(v___x_3329_);
v___x_3393_ = ((size_t)0ULL);
lean_inc(v___x_3329_);
v___x_3394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5(v_jumps_3305_, v_sz_3392_, v___x_3393_, v___x_3329_);
v___x_3395_ = lean_nat_add(v_i_3306_, v___x_3372_);
lean_inc_ref(v_xs_3307_);
v___x_3396_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(v_xs_3307_, v___x_3394_, v___x_3395_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___x_3395_);
lean_dec_ref(v___x_3394_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; lean_object* v_fst_3398_; lean_object* v_snd_3399_; lean_object* v_proof_3400_; lean_object* v___x_3401_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v___x_3396_, 1);
v_fst_3398_ = lean_ctor_get(v_a_3397_, 0);
lean_inc(v_fst_3398_);
v_snd_3399_ = lean_ctor_get(v_a_3397_, 1);
lean_inc(v_snd_3399_);
lean_dec(v_a_3397_);
v_proof_3400_ = lean_ctor_get(v_fst_3332_, 0);
lean_inc(v_proof_3400_);
v___x_3401_ = l_Lean_MVarId_getDecl(v_proof_3400_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; lean_object* v_lctx_3403_; lean_object* v_localInstances_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_a_3402_);
lean_dec_ref_known(v___x_3401_, 1);
v_lctx_3403_ = lean_ctor_get(v_a_3402_, 1);
lean_inc_ref(v_lctx_3403_);
v_localInstances_3404_ = lean_ctor_get(v_a_3402_, 4);
lean_inc_ref(v_localInstances_3404_);
lean_dec(v_a_3402_);
lean_inc(v___x_3391_);
v___x_3405_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___boxed), 14, 2);
lean_closure_set(v___x_3405_, 0, v___x_3391_);
lean_closure_set(v___x_3405_, 1, v_fst_3398_);
v___x_3406_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(v_lctx_3403_, v_localInstances_3404_, v___x_3405_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_a_3407_);
lean_dec_ref_known(v___x_3406_, 1);
v_fst_3340_ = v_a_3407_;
v_snd_3341_ = v_snd_3399_;
v___y_3342_ = v___y_3311_;
v___y_3343_ = v___y_3312_;
v___y_3344_ = v___y_3313_;
v___y_3345_ = v___y_3314_;
v___y_3346_ = v___y_3315_;
v___y_3347_ = v___y_3316_;
v___y_3348_ = v___y_3317_;
v___y_3349_ = v___y_3318_;
v___y_3350_ = v___y_3319_;
v___y_3351_ = v___y_3320_;
v___y_3352_ = v___y_3321_;
goto v___jp_3339_;
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_dec(v_snd_3399_);
lean_del_object(v___x_3337_);
lean_dec(v_snd_3335_);
lean_dec(v_fst_3334_);
lean_dec(v_i_3310_);
lean_dec_ref(v_xs_3307_);
lean_dec(v___x_3303_);
v_a_3408_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3406_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3406_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec(v_snd_3399_);
lean_dec(v_fst_3398_);
lean_del_object(v___x_3337_);
lean_dec(v_snd_3335_);
lean_dec(v_fst_3334_);
lean_dec(v_i_3310_);
lean_dec_ref(v_xs_3307_);
lean_dec(v___x_3303_);
v_a_3416_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3401_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3401_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_del_object(v___x_3337_);
lean_dec(v_snd_3335_);
lean_dec(v_fst_3334_);
lean_dec(v_i_3310_);
lean_dec_ref(v_xs_3307_);
lean_dec(v___x_3303_);
v_a_3424_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3396_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3396_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
v___jp_3339_:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; size_t v_sz_3355_; size_t v___x_3356_; lean_object* v___x_3357_; 
v___x_3353_ = lean_array_push(v_fst_3334_, v_fst_3340_);
v___x_3354_ = l_Array_zip___redArg(v___x_3329_, v_snd_3341_);
lean_dec_ref(v_snd_3341_);
v_sz_3355_ = lean_array_size(v___x_3354_);
v___x_3356_ = ((size_t)0ULL);
lean_inc(v___x_3303_);
lean_inc(v_i_3310_);
v___x_3357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(v_i_3310_, v___x_3303_, v___x_3354_, v_sz_3355_, v___x_3356_, v_snd_3335_);
lean_dec_ref(v___x_3354_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3360_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3358_);
lean_dec_ref_known(v___x_3357_, 1);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 1, v_a_3358_);
lean_ctor_set(v___x_3337_, 0, v___x_3353_);
v___x_3360_ = v___x_3337_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3353_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_a_3358_);
v___x_3360_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3361_ = lean_nat_add(v_i_3310_, v_step_3324_);
lean_dec(v_i_3310_);
v___x_3362_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg(v___x_3304_, v_jumps_3305_, v___x_3303_, v_i_3306_, v_xs_3307_, v_range_3308_, v___x_3360_, v___x_3361_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
return v___x_3362_;
}
}
else
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3371_; 
lean_dec_ref(v___x_3353_);
lean_del_object(v___x_3337_);
lean_dec(v_i_3310_);
lean_dec_ref(v_xs_3307_);
lean_dec(v___x_3303_);
v_a_3364_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3366_ = v___x_3357_;
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3357_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3367_ == 0)
{
v___x_3369_ = v___x_3366_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3364_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(lean_object* v_xs_3433_, lean_object* v_jumps_3434_, lean_object* v_i_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_){
_start:
{
lean_object* v___x_3448_; lean_object* v_groups_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; 
v___x_3448_ = lean_unsigned_to_nat(0u);
v_groups_3449_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__0));
v___x_3450_ = lean_array_get_size(v_jumps_3434_);
v___x_3451_ = lean_unsigned_to_nat(1u);
v___x_3452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3448_);
lean_ctor_set(v___x_3452_, 1, v___x_3450_);
lean_ctor_set(v___x_3452_, 2, v___x_3451_);
v___x_3453_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__3, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__3);
v___x_3454_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg(v_jumps_3434_, v_i_3435_, v___x_3452_, v___x_3453_, v___x_3448_);
lean_dec_ref_known(v___x_3452_, 3);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v_fst_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3495_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_a_3455_);
lean_dec_ref_known(v___x_3454_, 1);
v_fst_3456_ = lean_ctor_get(v_a_3455_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v_a_3455_);
if (v_isSharedCheck_3495_ == 0)
{
lean_object* v_unused_3496_; 
v_unused_3496_ = lean_ctor_get(v_a_3455_, 1);
lean_dec(v_unused_3496_);
v___x_3458_ = v_a_3455_;
v_isShared_3459_ = v_isSharedCheck_3495_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_fst_3456_);
lean_dec(v_a_3455_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3495_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3465_; 
v___x_3460_ = lean_box(0);
v___x_3461_ = lean_mk_array(v___x_3450_, v___x_3460_);
v___x_3462_ = lean_array_get_size(v_fst_3456_);
v___x_3463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3448_);
lean_ctor_set(v___x_3463_, 1, v___x_3462_);
lean_ctor_set(v___x_3463_, 2, v___x_3451_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 1, v___x_3461_);
lean_ctor_set(v___x_3458_, 0, v_groups_3449_);
v___x_3465_ = v___x_3458_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_groups_3449_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v___x_3461_);
v___x_3465_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
lean_object* v___x_3466_; 
v___x_3466_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg(v___x_3462_, v_fst_3456_, v_jumps_3434_, v_i_3435_, v_xs_3433_, v___x_3463_, v___x_3465_, v___x_3448_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_);
lean_dec_ref_known(v___x_3463_, 3);
lean_dec(v_fst_3456_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3485_; 
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3469_ = v___x_3466_;
v_isShared_3470_ = v_isSharedCheck_3485_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3466_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3485_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v_fst_3471_; lean_object* v_snd_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3484_; 
v_fst_3471_ = lean_ctor_get(v_a_3467_, 0);
v_snd_3472_ = lean_ctor_get(v_a_3467_, 1);
v_isSharedCheck_3484_ = !lean_is_exclusive(v_a_3467_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3474_ = v_a_3467_;
v_isShared_3475_ = v_isSharedCheck_3484_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_snd_3472_);
lean_inc(v_fst_3471_);
lean_dec(v_a_3467_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3484_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3479_; 
v___x_3476_ = lean_array_get_size(v_fst_3471_);
v___x_3477_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(v_fst_3471_, v___x_3448_, v___x_3476_);
lean_dec(v_fst_3471_);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v___x_3477_);
v___x_3479_ = v___x_3474_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3477_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_snd_3472_);
v___x_3479_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3481_; 
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v___x_3479_);
v___x_3481_ = v___x_3469_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3479_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
}
else
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
v_a_3486_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3466_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3466_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
}
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_dec_ref(v_xs_3433_);
v_a_3497_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3454_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3454_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___boxed(lean_object* v_xs_3505_, lean_object* v_jumps_3506_, lean_object* v_i_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(v_xs_3505_, v_jumps_3506_, v_i_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
lean_dec(v_a_3516_);
lean_dec_ref(v_a_3515_);
lean_dec(v_a_3514_);
lean_dec_ref(v_a_3513_);
lean_dec(v_a_3512_);
lean_dec_ref(v_a_3511_);
lean_dec(v_a_3510_);
lean_dec(v_a_3509_);
lean_dec_ref(v_a_3508_);
lean_dec(v_i_3507_);
lean_dec_ref(v_jumps_3506_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___boxed(lean_object** _args){
lean_object* v___x_3521_ = _args[0];
lean_object* v_jumps_3522_ = _args[1];
lean_object* v___x_3523_ = _args[2];
lean_object* v_i_3524_ = _args[3];
lean_object* v_xs_3525_ = _args[4];
lean_object* v_range_3526_ = _args[5];
lean_object* v_b_3527_ = _args[6];
lean_object* v_i_3528_ = _args[7];
lean_object* v___y_3529_ = _args[8];
lean_object* v___y_3530_ = _args[9];
lean_object* v___y_3531_ = _args[10];
lean_object* v___y_3532_ = _args[11];
lean_object* v___y_3533_ = _args[12];
lean_object* v___y_3534_ = _args[13];
lean_object* v___y_3535_ = _args[14];
lean_object* v___y_3536_ = _args[15];
lean_object* v___y_3537_ = _args[16];
lean_object* v___y_3538_ = _args[17];
lean_object* v___y_3539_ = _args[18];
lean_object* v___y_3540_ = _args[19];
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg(v___x_3521_, v_jumps_3522_, v___x_3523_, v_i_3524_, v_xs_3525_, v_range_3526_, v_b_3527_, v_i_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec_ref(v_range_3526_);
lean_dec(v_i_3524_);
lean_dec_ref(v_jumps_3522_);
lean_dec_ref(v___x_3521_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg___boxed(lean_object** _args){
lean_object* v___x_3542_ = _args[0];
lean_object* v___x_3543_ = _args[1];
lean_object* v_jumps_3544_ = _args[2];
lean_object* v_i_3545_ = _args[3];
lean_object* v_xs_3546_ = _args[4];
lean_object* v_range_3547_ = _args[5];
lean_object* v_b_3548_ = _args[6];
lean_object* v_i_3549_ = _args[7];
lean_object* v___y_3550_ = _args[8];
lean_object* v___y_3551_ = _args[9];
lean_object* v___y_3552_ = _args[10];
lean_object* v___y_3553_ = _args[11];
lean_object* v___y_3554_ = _args[12];
lean_object* v___y_3555_ = _args[13];
lean_object* v___y_3556_ = _args[14];
lean_object* v___y_3557_ = _args[15];
lean_object* v___y_3558_ = _args[16];
lean_object* v___y_3559_ = _args[17];
lean_object* v___y_3560_ = _args[18];
lean_object* v___y_3561_ = _args[19];
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg(v___x_3542_, v___x_3543_, v_jumps_3544_, v_i_3545_, v_xs_3546_, v_range_3547_, v_b_3548_, v_i_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3552_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec_ref(v_range_3547_);
lean_dec(v_i_3545_);
lean_dec_ref(v_jumps_3544_);
lean_dec_ref(v___x_3543_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0(lean_object* v_00_u03b2_3563_, lean_object* v_m_3564_, lean_object* v_a_3565_){
_start:
{
lean_object* v___x_3566_; 
v___x_3566_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg(v_m_3564_, v_a_3565_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___boxed(lean_object* v_00_u03b2_3567_, lean_object* v_m_3568_, lean_object* v_a_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0(v_00_u03b2_3567_, v_m_3568_, v_a_3569_);
lean_dec(v_a_3569_);
lean_dec_ref(v_m_3568_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1(lean_object* v_00_u03b2_3571_, lean_object* v_m_3572_, lean_object* v_a_3573_, lean_object* v_b_3574_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1___redArg(v_m_3572_, v_a_3573_, v_b_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2(lean_object* v_jumps_3576_, lean_object* v_i_3577_, lean_object* v_range_3578_, lean_object* v_b_3579_, lean_object* v_i_3580_, lean_object* v_hs_3581_, lean_object* v_hl_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v___x_3595_; 
v___x_3595_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg(v_jumps_3576_, v_i_3577_, v_range_3578_, v_b_3579_, v_i_3580_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___boxed(lean_object** _args){
lean_object* v_jumps_3596_ = _args[0];
lean_object* v_i_3597_ = _args[1];
lean_object* v_range_3598_ = _args[2];
lean_object* v_b_3599_ = _args[3];
lean_object* v_i_3600_ = _args[4];
lean_object* v_hs_3601_ = _args[5];
lean_object* v_hl_3602_ = _args[6];
lean_object* v___y_3603_ = _args[7];
lean_object* v___y_3604_ = _args[8];
lean_object* v___y_3605_ = _args[9];
lean_object* v___y_3606_ = _args[10];
lean_object* v___y_3607_ = _args[11];
lean_object* v___y_3608_ = _args[12];
lean_object* v___y_3609_ = _args[13];
lean_object* v___y_3610_ = _args[14];
lean_object* v___y_3611_ = _args[15];
lean_object* v___y_3612_ = _args[16];
lean_object* v___y_3613_ = _args[17];
lean_object* v___y_3614_ = _args[18];
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2(v_jumps_3596_, v_i_3597_, v_range_3598_, v_b_3599_, v_i_3600_, v_hs_3601_, v_hl_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec_ref(v_range_3598_);
lean_dec(v_i_3597_);
lean_dec_ref(v_jumps_3596_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3(lean_object* v_g_3616_, lean_object* v___x_3617_, lean_object* v_as_3618_, size_t v_sz_3619_, size_t v_i_3620_, lean_object* v_b_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v___x_3634_; 
v___x_3634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(v_g_3616_, v___x_3617_, v_as_3618_, v_sz_3619_, v_i_3620_, v_b_3621_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___boxed(lean_object** _args){
lean_object* v_g_3635_ = _args[0];
lean_object* v___x_3636_ = _args[1];
lean_object* v_as_3637_ = _args[2];
lean_object* v_sz_3638_ = _args[3];
lean_object* v_i_3639_ = _args[4];
lean_object* v_b_3640_ = _args[5];
lean_object* v___y_3641_ = _args[6];
lean_object* v___y_3642_ = _args[7];
lean_object* v___y_3643_ = _args[8];
lean_object* v___y_3644_ = _args[9];
lean_object* v___y_3645_ = _args[10];
lean_object* v___y_3646_ = _args[11];
lean_object* v___y_3647_ = _args[12];
lean_object* v___y_3648_ = _args[13];
lean_object* v___y_3649_ = _args[14];
lean_object* v___y_3650_ = _args[15];
lean_object* v___y_3651_ = _args[16];
lean_object* v___y_3652_ = _args[17];
_start:
{
size_t v_sz_boxed_3653_; size_t v_i_boxed_3654_; lean_object* v_res_3655_; 
v_sz_boxed_3653_ = lean_unbox_usize(v_sz_3638_);
lean_dec(v_sz_3638_);
v_i_boxed_3654_ = lean_unbox_usize(v_i_3639_);
lean_dec(v_i_3639_);
v_res_3655_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3(v_g_3635_, v___x_3636_, v_as_3637_, v_sz_boxed_3653_, v_i_boxed_3654_, v_b_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec(v___y_3643_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec_ref(v_as_3637_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4(lean_object* v_fst_3656_, lean_object* v_as_3657_, size_t v_sz_3658_, size_t v_i_3659_, lean_object* v_bs_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v___x_3673_; 
v___x_3673_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(v_fst_3656_, v_sz_3658_, v_i_3659_, v_bs_3660_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___boxed(lean_object** _args){
lean_object* v_fst_3674_ = _args[0];
lean_object* v_as_3675_ = _args[1];
lean_object* v_sz_3676_ = _args[2];
lean_object* v_i_3677_ = _args[3];
lean_object* v_bs_3678_ = _args[4];
lean_object* v___y_3679_ = _args[5];
lean_object* v___y_3680_ = _args[6];
lean_object* v___y_3681_ = _args[7];
lean_object* v___y_3682_ = _args[8];
lean_object* v___y_3683_ = _args[9];
lean_object* v___y_3684_ = _args[10];
lean_object* v___y_3685_ = _args[11];
lean_object* v___y_3686_ = _args[12];
lean_object* v___y_3687_ = _args[13];
lean_object* v___y_3688_ = _args[14];
lean_object* v___y_3689_ = _args[15];
lean_object* v___y_3690_ = _args[16];
_start:
{
size_t v_sz_boxed_3691_; size_t v_i_boxed_3692_; lean_object* v_res_3693_; 
v_sz_boxed_3691_ = lean_unbox_usize(v_sz_3676_);
lean_dec(v_sz_3676_);
v_i_boxed_3692_ = lean_unbox_usize(v_i_3677_);
lean_dec(v_i_3677_);
v_res_3693_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4(v_fst_3674_, v_as_3675_, v_sz_boxed_3691_, v_i_boxed_3692_, v_bs_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec(v___y_3681_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
lean_dec_ref(v_as_3675_);
lean_dec_ref(v_fst_3674_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7(lean_object* v___x_3694_, lean_object* v___x_3695_, lean_object* v_jumps_3696_, lean_object* v_i_3697_, lean_object* v_xs_3698_, lean_object* v_range_3699_, lean_object* v_b_3700_, lean_object* v_i_3701_, lean_object* v_hs_3702_, lean_object* v_hl_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
lean_object* v___x_3716_; 
v___x_3716_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg(v___x_3694_, v___x_3695_, v_jumps_3696_, v_i_3697_, v_xs_3698_, v_range_3699_, v_b_3700_, v_i_3701_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___boxed(lean_object** _args){
lean_object* v___x_3717_ = _args[0];
lean_object* v___x_3718_ = _args[1];
lean_object* v_jumps_3719_ = _args[2];
lean_object* v_i_3720_ = _args[3];
lean_object* v_xs_3721_ = _args[4];
lean_object* v_range_3722_ = _args[5];
lean_object* v_b_3723_ = _args[6];
lean_object* v_i_3724_ = _args[7];
lean_object* v_hs_3725_ = _args[8];
lean_object* v_hl_3726_ = _args[9];
lean_object* v___y_3727_ = _args[10];
lean_object* v___y_3728_ = _args[11];
lean_object* v___y_3729_ = _args[12];
lean_object* v___y_3730_ = _args[13];
lean_object* v___y_3731_ = _args[14];
lean_object* v___y_3732_ = _args[15];
lean_object* v___y_3733_ = _args[16];
lean_object* v___y_3734_ = _args[17];
lean_object* v___y_3735_ = _args[18];
lean_object* v___y_3736_ = _args[19];
lean_object* v___y_3737_ = _args[20];
lean_object* v___y_3738_ = _args[21];
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7(v___x_3717_, v___x_3718_, v_jumps_3719_, v_i_3720_, v_xs_3721_, v_range_3722_, v_b_3723_, v_i_3724_, v_hs_3725_, v_hl_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
lean_dec(v___y_3731_);
lean_dec_ref(v___y_3730_);
lean_dec(v___y_3729_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec_ref(v_range_3722_);
lean_dec(v_i_3720_);
lean_dec_ref(v_jumps_3719_);
lean_dec_ref(v___x_3718_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0(lean_object* v_00_u03b2_3740_, lean_object* v_a_3741_, lean_object* v_x_3742_){
_start:
{
lean_object* v___x_3743_; 
v___x_3743_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg(v_a_3741_, v_x_3742_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3744_, lean_object* v_a_3745_, lean_object* v_x_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0(v_00_u03b2_3744_, v_a_3745_, v_x_3746_);
lean_dec(v_x_3746_);
lean_dec(v_a_3745_);
return v_res_3747_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2(lean_object* v_00_u03b2_3748_, lean_object* v_a_3749_, lean_object* v_x_3750_){
_start:
{
uint8_t v___x_3751_; 
v___x_3751_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg(v_a_3749_, v_x_3750_);
return v___x_3751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3752_, lean_object* v_a_3753_, lean_object* v_x_3754_){
_start:
{
uint8_t v_res_3755_; lean_object* v_r_3756_; 
v_res_3755_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2(v_00_u03b2_3752_, v_a_3753_, v_x_3754_);
lean_dec(v_x_3754_);
lean_dec(v_a_3753_);
v_r_3756_ = lean_box(v_res_3755_);
return v_r_3756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3(lean_object* v_00_u03b2_3757_, lean_object* v_data_3758_){
_start:
{
lean_object* v___x_3759_; 
v___x_3759_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3___redArg(v_data_3758_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4(lean_object* v_00_u03b2_3760_, lean_object* v_a_3761_, lean_object* v_b_3762_, lean_object* v_x_3763_){
_start:
{
lean_object* v___x_3764_; 
v___x_3764_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4___redArg(v_a_3761_, v_b_3762_, v_x_3763_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11(lean_object* v___x_3765_, lean_object* v_jumps_3766_, lean_object* v___x_3767_, lean_object* v_i_3768_, lean_object* v_xs_3769_, lean_object* v_range_3770_, lean_object* v_b_3771_, lean_object* v_i_3772_, lean_object* v_hs_3773_, lean_object* v_hl_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
lean_object* v___x_3787_; 
v___x_3787_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg(v___x_3765_, v_jumps_3766_, v___x_3767_, v_i_3768_, v_xs_3769_, v_range_3770_, v_b_3771_, v_i_3772_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
return v___x_3787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___boxed(lean_object** _args){
lean_object* v___x_3788_ = _args[0];
lean_object* v_jumps_3789_ = _args[1];
lean_object* v___x_3790_ = _args[2];
lean_object* v_i_3791_ = _args[3];
lean_object* v_xs_3792_ = _args[4];
lean_object* v_range_3793_ = _args[5];
lean_object* v_b_3794_ = _args[6];
lean_object* v_i_3795_ = _args[7];
lean_object* v_hs_3796_ = _args[8];
lean_object* v_hl_3797_ = _args[9];
lean_object* v___y_3798_ = _args[10];
lean_object* v___y_3799_ = _args[11];
lean_object* v___y_3800_ = _args[12];
lean_object* v___y_3801_ = _args[13];
lean_object* v___y_3802_ = _args[14];
lean_object* v___y_3803_ = _args[15];
lean_object* v___y_3804_ = _args[16];
lean_object* v___y_3805_ = _args[17];
lean_object* v___y_3806_ = _args[18];
lean_object* v___y_3807_ = _args[19];
lean_object* v___y_3808_ = _args[20];
lean_object* v___y_3809_ = _args[21];
_start:
{
lean_object* v_res_3810_; 
v_res_3810_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11(v___x_3788_, v_jumps_3789_, v___x_3790_, v_i_3791_, v_xs_3792_, v_range_3793_, v_b_3794_, v_i_3795_, v_hs_3796_, v_hl_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v___y_3800_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec_ref(v_range_3793_);
lean_dec(v_i_3791_);
lean_dec_ref(v_jumps_3789_);
lean_dec_ref(v___x_3788_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_3811_, lean_object* v_i_3812_, lean_object* v_source_3813_, lean_object* v_target_3814_){
_start:
{
lean_object* v___x_3815_; 
v___x_3815_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5___redArg(v_i_3812_, v_source_3813_, v_target_3814_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_3816_, lean_object* v_x_3817_, lean_object* v_x_3818_){
_start:
{
lean_object* v___x_3819_; 
v___x_3819_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5_spec__11___redArg(v_x_3817_, v_x_3818_);
return v___x_3819_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__1(void){
_start:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3821_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__0));
v___x_3822_ = l_Lean_stringToMessageData(v___x_3821_);
return v___x_3822_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10(void){
_start:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3837_ = lean_box(0);
v___x_3838_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__9));
v___x_3839_ = l_Lean_mkConst(v___x_3838_, v___x_3837_);
return v___x_3839_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__12(void){
_start:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3843_ = lean_box(0);
v___x_3844_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__11));
v___x_3845_ = l_Lean_mkConst(v___x_3844_, v___x_3843_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(lean_object* v_00_u03c6_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_){
_start:
{
lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___x_3861_; 
lean_inc_ref(v_00_u03c6_3846_);
v___x_3861_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_00_u03c6_3846_, v_a_3848_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3907_; 
v_a_3862_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3864_ = v___x_3861_;
v_isShared_3865_ = v_isSharedCheck_3907_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3861_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3907_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; uint8_t v___x_3868_; 
v___x_3866_ = l_Lean_Expr_cleanupAnnotations(v_a_3862_);
lean_dec(v_a_3862_);
v___x_3867_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__3));
v___x_3868_ = l_Lean_Expr_isConstOf(v___x_3866_, v___x_3867_);
if (v___x_3868_ == 0)
{
uint8_t v___x_3869_; 
v___x_3869_ = l_Lean_Expr_isApp(v___x_3866_);
if (v___x_3869_ == 0)
{
lean_dec_ref(v___x_3866_);
lean_del_object(v___x_3864_);
v___y_3853_ = v_a_3847_;
v___y_3854_ = v_a_3848_;
v___y_3855_ = v_a_3849_;
v___y_3856_ = v_a_3850_;
goto v___jp_3852_;
}
else
{
lean_object* v___x_3870_; uint8_t v___x_3871_; 
v___x_3870_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3866_);
v___x_3871_ = l_Lean_Expr_isApp(v___x_3870_);
if (v___x_3871_ == 0)
{
lean_dec_ref(v___x_3870_);
lean_dec_ref(v___x_3866_);
lean_del_object(v___x_3864_);
v___y_3853_ = v_a_3847_;
v___y_3854_ = v_a_3848_;
v___y_3855_ = v_a_3849_;
v___y_3856_ = v_a_3850_;
goto v___jp_3852_;
}
else
{
lean_object* v_arg_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; uint8_t v___x_3875_; 
v_arg_3872_ = lean_ctor_get(v___x_3870_, 1);
lean_inc_ref(v_arg_3872_);
v___x_3873_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3870_);
lean_dec_ref(v___x_3870_);
v___x_3874_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__5));
v___x_3875_ = l_Lean_Expr_isConstOf(v___x_3873_, v___x_3874_);
if (v___x_3875_ == 0)
{
uint8_t v___x_3876_; 
lean_dec_ref(v___x_3866_);
v___x_3876_ = l_Lean_Expr_isApp(v___x_3873_);
if (v___x_3876_ == 0)
{
lean_dec_ref(v___x_3873_);
lean_dec_ref(v_arg_3872_);
lean_del_object(v___x_3864_);
v___y_3853_ = v_a_3847_;
v___y_3854_ = v_a_3848_;
v___y_3855_ = v_a_3849_;
v___y_3856_ = v_a_3850_;
goto v___jp_3852_;
}
else
{
lean_object* v___x_3877_; lean_object* v___x_3878_; uint8_t v___x_3879_; 
v___x_3877_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3873_);
v___x_3878_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__1));
v___x_3879_ = l_Lean_Expr_isConstOf(v___x_3877_, v___x_3878_);
lean_dec_ref(v___x_3877_);
if (v___x_3879_ == 0)
{
lean_dec_ref(v___x_3873_);
lean_dec_ref(v_arg_3872_);
lean_del_object(v___x_3864_);
v___y_3853_ = v_a_3847_;
v___y_3854_ = v_a_3848_;
v___y_3855_ = v_a_3849_;
v___y_3856_ = v_a_3850_;
goto v___jp_3852_;
}
else
{
lean_object* v_arg_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3887_; 
v_arg_3880_ = lean_ctor_get(v___x_3873_, 1);
lean_inc_ref(v_arg_3880_);
lean_dec_ref(v___x_3873_);
v___x_3881_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__7));
v___x_3882_ = l_Lean_Expr_getAppFn(v_00_u03c6_3846_);
lean_dec_ref(v_00_u03c6_3846_);
v___x_3883_ = l_Lean_Expr_constLevels_x21(v___x_3882_);
lean_dec_ref(v___x_3882_);
v___x_3884_ = l_Lean_mkConst(v___x_3881_, v___x_3883_);
v___x_3885_ = l_Lean_mkAppB(v___x_3884_, v_arg_3880_, v_arg_3872_);
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 0, v___x_3885_);
v___x_3887_ = v___x_3864_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3885_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
}
else
{
lean_object* v_arg_3889_; lean_object* v___x_3890_; 
lean_dec_ref(v___x_3873_);
lean_del_object(v___x_3864_);
lean_dec_ref(v_00_u03c6_3846_);
v_arg_3889_ = lean_ctor_get(v___x_3866_, 1);
lean_inc_ref(v_arg_3889_);
lean_dec_ref(v___x_3866_);
lean_inc_ref(v_arg_3872_);
v___x_3890_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(v_arg_3872_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; lean_object* v___x_3892_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_a_3891_);
lean_dec_ref_known(v___x_3890_, 1);
lean_inc_ref(v_arg_3889_);
v___x_3892_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(v_arg_3889_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3902_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3895_ = v___x_3892_;
v_isShared_3896_ = v_isSharedCheck_3902_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3892_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3902_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3900_; 
v___x_3897_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10);
v___x_3898_ = l_Lean_mkApp4(v___x_3897_, v_arg_3872_, v_arg_3889_, v_a_3891_, v_a_3893_);
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 0, v___x_3898_);
v___x_3900_ = v___x_3895_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3898_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
return v___x_3900_;
}
}
}
else
{
lean_dec(v_a_3891_);
lean_dec_ref(v_arg_3889_);
lean_dec_ref(v_arg_3872_);
return v___x_3892_;
}
}
else
{
lean_dec_ref(v_arg_3889_);
lean_dec_ref(v_arg_3872_);
return v___x_3890_;
}
}
}
}
}
else
{
lean_object* v___x_3903_; lean_object* v___x_3905_; 
lean_dec_ref(v___x_3866_);
lean_dec_ref(v_00_u03c6_3846_);
v___x_3903_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__12, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__12_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__12);
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 0, v___x_3903_);
v___x_3905_ = v___x_3864_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v___x_3903_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
}
else
{
lean_dec_ref(v_00_u03c6_3846_);
return v___x_3861_;
}
v___jp_3852_:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3857_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__1, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__1);
v___x_3858_ = l_Lean_indentExpr(v_00_u03c6_3846_);
v___x_3859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3857_);
lean_ctor_set(v___x_3859_, 1, v___x_3858_);
v___x_3860_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v___x_3859_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
return v___x_3860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___boxed(lean_object* v_00_u03c6_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(v_00_u03c6_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_);
lean_dec(v_a_3912_);
lean_dec_ref(v_a_3911_);
lean_dec(v_a_3910_);
lean_dec_ref(v_a_3909_);
return v_res_3914_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__1(void){
_start:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; 
v___x_3916_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__0));
v___x_3917_ = l_Lean_stringToMessageData(v___x_3916_);
return v___x_3917_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3919_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__0));
v___x_3920_ = l_Lean_stringToMessageData(v___x_3919_);
return v___x_3920_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3925_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__3));
v___x_3926_ = l_Lean_stringToMessageData(v___x_3925_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0(lean_object* v_tail_3927_, lean_object* v_ws_3928_, lean_object* v_00_u03c6_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; uint8_t v___x_3944_; 
v___x_3944_ = l_List_isEmpty___redArg(v_tail_3927_);
if (v___x_3944_ == 0)
{
if (lean_obj_tag(v_00_u03c6_3929_) == 8)
{
lean_object* v_value_3945_; lean_object* v_body_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v_value_3945_ = lean_ctor_get(v_00_u03c6_3929_, 2);
lean_inc_ref(v_value_3945_);
v_body_3946_ = lean_ctor_get(v_00_u03c6_3929_, 3);
lean_inc_ref(v_body_3946_);
lean_dec_ref_known(v_00_u03c6_3929_, 4);
v___x_3947_ = lean_expr_instantiate1(v_body_3946_, v_value_3945_);
lean_dec_ref(v_value_3945_);
lean_dec_ref(v_body_3946_);
v___x_3948_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v___x_3947_, v_tail_3927_, v_ws_3928_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
return v___x_3948_;
}
else
{
if (lean_obj_tag(v_ws_3928_) == 1)
{
lean_object* v_head_3949_; lean_object* v_tail_3950_; lean_object* v___x_3951_; 
v_head_3949_ = lean_ctor_get(v_ws_3928_, 0);
lean_inc(v_head_3949_);
v_tail_3950_ = lean_ctor_get(v_ws_3928_, 1);
lean_inc(v_tail_3950_);
lean_dec_ref_known(v_ws_3928_, 2);
lean_inc_ref(v_00_u03c6_3929_);
v___x_3951_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_00_u03c6_3929_, v___y_3931_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v_a_3952_; lean_object* v___x_3953_; uint8_t v___x_3954_; 
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_a_3952_);
lean_dec_ref_known(v___x_3951_, 1);
v___x_3953_ = l_Lean_Expr_cleanupAnnotations(v_a_3952_);
lean_dec(v_a_3952_);
v___x_3954_ = l_Lean_Expr_isApp(v___x_3953_);
if (v___x_3954_ == 0)
{
lean_dec_ref(v___x_3953_);
lean_dec(v_tail_3950_);
lean_dec(v_head_3949_);
lean_dec(v_tail_3927_);
v___y_3936_ = v___y_3930_;
v___y_3937_ = v___y_3931_;
v___y_3938_ = v___y_3932_;
v___y_3939_ = v___y_3933_;
goto v___jp_3935_;
}
else
{
lean_object* v___x_3955_; uint8_t v___x_3956_; 
v___x_3955_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3953_);
v___x_3956_ = l_Lean_Expr_isApp(v___x_3955_);
if (v___x_3956_ == 0)
{
lean_dec_ref(v___x_3955_);
lean_dec_ref(v___x_3953_);
lean_dec(v_tail_3950_);
lean_dec(v_head_3949_);
lean_dec(v_tail_3927_);
v___y_3936_ = v___y_3930_;
v___y_3937_ = v___y_3931_;
v___y_3938_ = v___y_3932_;
v___y_3939_ = v___y_3933_;
goto v___jp_3935_;
}
else
{
lean_object* v_arg_3957_; lean_object* v_arg_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; uint8_t v___x_3961_; 
v_arg_3957_ = lean_ctor_get(v___x_3953_, 1);
lean_inc_ref(v_arg_3957_);
lean_dec_ref(v___x_3953_);
v_arg_3958_ = lean_ctor_get(v___x_3955_, 1);
lean_inc_ref(v_arg_3958_);
v___x_3959_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3955_);
lean_dec_ref(v___x_3955_);
v___x_3960_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__5));
v___x_3961_ = l_Lean_Expr_isConstOf(v___x_3959_, v___x_3960_);
if (v___x_3961_ == 0)
{
lean_object* v___x_3962_; uint8_t v___x_3963_; 
v___x_3962_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___closed__1));
v___x_3963_ = l_Lean_Expr_isConstOf(v___x_3959_, v___x_3962_);
lean_dec_ref(v___x_3959_);
if (v___x_3963_ == 0)
{
lean_dec_ref(v_arg_3958_);
lean_dec_ref(v_arg_3957_);
lean_dec(v_tail_3950_);
lean_dec(v_head_3949_);
lean_dec(v_tail_3927_);
v___y_3936_ = v___y_3930_;
v___y_3937_ = v___y_3931_;
v___y_3938_ = v___y_3932_;
v___y_3939_ = v___y_3933_;
goto v___jp_3935_;
}
else
{
lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3964_ = lean_unsigned_to_nat(1u);
v___x_3965_ = lean_mk_empty_array_with_capacity(v___x_3964_);
lean_inc(v_head_3949_);
v___x_3966_ = lean_array_push(v___x_3965_, v_head_3949_);
lean_inc_ref(v_arg_3957_);
v___x_3967_ = l_Lean_Expr_beta(v_arg_3957_, v___x_3966_);
v___x_3968_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v___x_3967_, v_tail_3927_, v_tail_3950_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3981_; 
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3971_ = v___x_3968_;
v_isShared_3972_ = v_isSharedCheck_3981_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3968_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3981_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3979_; 
v___x_3973_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__2));
v___x_3974_ = l_Lean_Expr_getAppFn(v_00_u03c6_3929_);
lean_dec_ref(v_00_u03c6_3929_);
v___x_3975_ = l_Lean_Expr_constLevels_x21(v___x_3974_);
lean_dec_ref(v___x_3974_);
v___x_3976_ = l_Lean_mkConst(v___x_3973_, v___x_3975_);
v___x_3977_ = l_Lean_mkApp4(v___x_3976_, v_arg_3958_, v_arg_3957_, v_head_3949_, v_a_3969_);
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 0, v___x_3977_);
v___x_3979_ = v___x_3971_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v___x_3977_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
else
{
lean_dec_ref(v_arg_3958_);
lean_dec_ref(v_arg_3957_);
lean_dec(v_head_3949_);
lean_dec_ref(v_00_u03c6_3929_);
return v___x_3968_;
}
}
}
else
{
lean_object* v___x_3982_; 
lean_dec_ref(v___x_3959_);
lean_dec_ref(v_00_u03c6_3929_);
lean_inc_ref(v_arg_3957_);
v___x_3982_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v_arg_3957_, v_tail_3927_, v_tail_3950_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v_a_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_3992_; 
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3985_ = v___x_3982_;
v_isShared_3986_ = v_isSharedCheck_3992_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_a_3983_);
lean_dec(v___x_3982_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_3992_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3990_; 
v___x_3987_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10);
v___x_3988_ = l_Lean_mkApp4(v___x_3987_, v_arg_3958_, v_arg_3957_, v_head_3949_, v_a_3983_);
if (v_isShared_3986_ == 0)
{
lean_ctor_set(v___x_3985_, 0, v___x_3988_);
v___x_3990_ = v___x_3985_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v___x_3988_);
v___x_3990_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
return v___x_3990_;
}
}
}
else
{
lean_dec_ref(v_arg_3958_);
lean_dec_ref(v_arg_3957_);
lean_dec(v_head_3949_);
return v___x_3982_;
}
}
}
}
}
else
{
lean_dec(v_tail_3950_);
lean_dec(v_head_3949_);
lean_dec_ref(v_00_u03c6_3929_);
lean_dec(v_tail_3927_);
return v___x_3951_;
}
}
else
{
lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
lean_dec(v_ws_3928_);
lean_dec(v_tail_3927_);
v___x_3993_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__4, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__4_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__4);
v___x_3994_ = l_Lean_indentExpr(v_00_u03c6_3929_);
v___x_3995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3993_);
lean_ctor_set(v___x_3995_, 1, v___x_3994_);
v___x_3996_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v___x_3995_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
return v___x_3996_;
}
}
}
else
{
lean_object* v___x_3997_; 
lean_dec(v_ws_3928_);
lean_dec(v_tail_3927_);
v___x_3997_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(v_00_u03c6_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
return v___x_3997_;
}
v___jp_3935_:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v___x_3940_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__1, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__1);
v___x_3941_ = l_Lean_indentExpr(v_00_u03c6_3929_);
v___x_3942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3940_);
lean_ctor_set(v___x_3942_, 1, v___x_3941_);
v___x_3943_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v___x_3942_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
return v___x_3943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___boxed(lean_object* v_tail_3998_, lean_object* v_ws_3999_, lean_object* v_00_u03c6_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0(v_tail_3998_, v_ws_3999_, v_00_u03c6_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
return v_res_4006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(lean_object* v_00_u03c6_4007_, lean_object* v_path_4008_, lean_object* v_ws_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_){
_start:
{
if (lean_obj_tag(v_path_4008_) == 1)
{
lean_object* v_head_4015_; lean_object* v_tail_4016_; lean_object* v_fst_4017_; lean_object* v_snd_4018_; lean_object* v___f_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v_head_4015_ = lean_ctor_get(v_path_4008_, 0);
lean_inc(v_head_4015_);
v_tail_4016_ = lean_ctor_get(v_path_4008_, 1);
lean_inc(v_tail_4016_);
lean_dec_ref_known(v_path_4008_, 2);
v_fst_4017_ = lean_ctor_get(v_head_4015_, 0);
lean_inc(v_fst_4017_);
v_snd_4018_ = lean_ctor_get(v_head_4015_, 1);
lean_inc(v_snd_4018_);
lean_dec(v_head_4015_);
v___f_4019_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4019_, 0, v_tail_4016_);
lean_closure_set(v___f_4019_, 1, v_ws_4009_);
v___x_4020_ = lean_unsigned_to_nat(0u);
v___x_4021_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(v_00_u03c6_4007_, v_fst_4017_, v___x_4020_, v_snd_4018_, v___f_4019_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
lean_dec(v_snd_4018_);
lean_dec(v_fst_4017_);
return v___x_4021_;
}
else
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
lean_dec(v_ws_4009_);
lean_dec(v_path_4008_);
v___x_4022_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__1, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__1);
v___x_4023_ = l_Lean_indentExpr(v_00_u03c6_4007_);
v___x_4024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4022_);
lean_ctor_set(v___x_4024_, 1, v___x_4023_);
v___x_4025_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v___x_4024_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
return v___x_4025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___boxed(lean_object* v_00_u03c6_4026_, lean_object* v_path_4027_, lean_object* v_ws_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_){
_start:
{
lean_object* v_res_4034_; 
v_res_4034_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v_00_u03c6_4026_, v_path_4027_, v_ws_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
lean_dec(v_a_4032_);
lean_dec_ref(v_a_4031_);
lean_dec(v_a_4030_);
lean_dec_ref(v_a_4029_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg(lean_object* v_type_4035_, lean_object* v_k_4036_, uint8_t v_cleanupAnnotations_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v___f_4050_; uint8_t v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
lean_inc(v___y_4044_);
lean_inc_ref(v___y_4043_);
lean_inc(v___y_4042_);
lean_inc_ref(v___y_4041_);
lean_inc(v___y_4040_);
lean_inc(v___y_4039_);
lean_inc_ref(v___y_4038_);
v___f_4050_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___redArg___lam__0___boxed), 15, 8);
lean_closure_set(v___f_4050_, 0, v_k_4036_);
lean_closure_set(v___f_4050_, 1, v___y_4038_);
lean_closure_set(v___f_4050_, 2, v___y_4039_);
lean_closure_set(v___f_4050_, 3, v___y_4040_);
lean_closure_set(v___f_4050_, 4, v___y_4041_);
lean_closure_set(v___f_4050_, 5, v___y_4042_);
lean_closure_set(v___f_4050_, 6, v___y_4043_);
lean_closure_set(v___f_4050_, 7, v___y_4044_);
v___x_4051_ = 0;
v___x_4052_ = lean_box(0);
v___x_4053_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_4051_, v___x_4052_, v_type_4035_, v___f_4050_, v_cleanupAnnotations_4037_, v___x_4051_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
if (lean_obj_tag(v___x_4053_) == 0)
{
return v___x_4053_;
}
else
{
lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4061_; 
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4056_ = v___x_4053_;
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_4053_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4059_; 
if (v_isShared_4057_ == 0)
{
v___x_4059_ = v___x_4056_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_a_4054_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg___boxed(lean_object* v_type_4062_, lean_object* v_k_4063_, lean_object* v_cleanupAnnotations_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4077_; lean_object* v_res_4078_; 
v_cleanupAnnotations_boxed_4077_ = lean_unbox(v_cleanupAnnotations_4064_);
v_res_4078_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg(v_type_4062_, v_k_4063_, v_cleanupAnnotations_boxed_4077_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_);
lean_dec(v___y_4075_);
lean_dec_ref(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec_ref(v___y_4072_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1(lean_object* v_00_u03b1_4079_, lean_object* v_type_4080_, lean_object* v_k_4081_, uint8_t v_cleanupAnnotations_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_){
_start:
{
lean_object* v___x_4095_; 
v___x_4095_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg(v_type_4080_, v_k_4081_, v_cleanupAnnotations_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___boxed(lean_object* v_00_u03b1_4096_, lean_object* v_type_4097_, lean_object* v_k_4098_, lean_object* v_cleanupAnnotations_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4112_; lean_object* v_res_4113_; 
v_cleanupAnnotations_boxed_4112_ = lean_unbox(v_cleanupAnnotations_4099_);
v_res_4113_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1(v_00_u03b1_4096_, v_type_4097_, v_k_4098_, v_cleanupAnnotations_boxed_4112_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
return v_res_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___redArg(lean_object* v_e_4114_, lean_object* v___y_4115_){
_start:
{
uint8_t v___x_4117_; 
v___x_4117_ = l_Lean_Expr_hasMVar(v_e_4114_);
if (v___x_4117_ == 0)
{
lean_object* v___x_4118_; 
v___x_4118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4118_, 0, v_e_4114_);
return v___x_4118_;
}
else
{
lean_object* v___x_4119_; lean_object* v_mctx_4120_; lean_object* v___x_4121_; lean_object* v_fst_4122_; lean_object* v_snd_4123_; lean_object* v___x_4124_; lean_object* v_cache_4125_; lean_object* v_zetaDeltaFVarIds_4126_; lean_object* v_postponed_4127_; lean_object* v_diag_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4137_; 
v___x_4119_ = lean_st_ref_get(v___y_4115_);
v_mctx_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc_ref(v_mctx_4120_);
lean_dec(v___x_4119_);
v___x_4121_ = l_Lean_instantiateMVarsCore(v_mctx_4120_, v_e_4114_);
v_fst_4122_ = lean_ctor_get(v___x_4121_, 0);
lean_inc(v_fst_4122_);
v_snd_4123_ = lean_ctor_get(v___x_4121_, 1);
lean_inc(v_snd_4123_);
lean_dec_ref(v___x_4121_);
v___x_4124_ = lean_st_ref_take(v___y_4115_);
v_cache_4125_ = lean_ctor_get(v___x_4124_, 1);
v_zetaDeltaFVarIds_4126_ = lean_ctor_get(v___x_4124_, 2);
v_postponed_4127_ = lean_ctor_get(v___x_4124_, 3);
v_diag_4128_ = lean_ctor_get(v___x_4124_, 4);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4137_ == 0)
{
lean_object* v_unused_4138_; 
v_unused_4138_ = lean_ctor_get(v___x_4124_, 0);
lean_dec(v_unused_4138_);
v___x_4130_ = v___x_4124_;
v_isShared_4131_ = v_isSharedCheck_4137_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_diag_4128_);
lean_inc(v_postponed_4127_);
lean_inc(v_zetaDeltaFVarIds_4126_);
lean_inc(v_cache_4125_);
lean_dec(v___x_4124_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4137_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4133_; 
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 0, v_snd_4123_);
v___x_4133_ = v___x_4130_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_snd_4123_);
lean_ctor_set(v_reuseFailAlloc_4136_, 1, v_cache_4125_);
lean_ctor_set(v_reuseFailAlloc_4136_, 2, v_zetaDeltaFVarIds_4126_);
lean_ctor_set(v_reuseFailAlloc_4136_, 3, v_postponed_4127_);
lean_ctor_set(v_reuseFailAlloc_4136_, 4, v_diag_4128_);
v___x_4133_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4134_ = lean_st_ref_put(v___y_4115_, v___x_4133_);
v___x_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4135_, 0, v_fst_4122_);
return v___x_4135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___redArg___boxed(lean_object* v_e_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___redArg(v_e_4139_, v___y_4140_);
lean_dec(v___y_4140_);
return v_res_4142_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3(lean_object* v_e_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
lean_object* v___x_4156_; 
v___x_4156_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___redArg(v_e_4143_, v___y_4152_);
return v___x_4156_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___boxed(lean_object* v_e_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3(v_e_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec(v___y_4160_);
lean_dec(v___y_4159_);
lean_dec_ref(v___y_4158_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___lam__0(lean_object* v_a_4171_, lean_object* v_hyp_4172_, lean_object* v_xs_4173_, lean_object* v_x_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4187_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_xs_4173_);
v___x_4188_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(v_xs_4173_, v_a_4171_, v___x_4187_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_);
if (lean_obj_tag(v___x_4188_) == 0)
{
lean_object* v_a_4189_; lean_object* v_fst_4190_; lean_object* v_snd_4191_; uint8_t v___x_4192_; uint8_t v___x_4193_; uint8_t v___x_4194_; lean_object* v___x_4195_; 
v_a_4189_ = lean_ctor_get(v___x_4188_, 0);
lean_inc(v_a_4189_);
lean_dec_ref_known(v___x_4188_, 1);
v_fst_4190_ = lean_ctor_get(v_a_4189_, 0);
lean_inc(v_fst_4190_);
v_snd_4191_ = lean_ctor_get(v_a_4189_, 1);
lean_inc(v_snd_4191_);
lean_dec(v_a_4189_);
v___x_4192_ = 0;
v___x_4193_ = 1;
v___x_4194_ = 1;
v___x_4195_ = l_Lean_Meta_mkLambdaFVars(v_xs_4173_, v_fst_4190_, v___x_4192_, v___x_4193_, v___x_4192_, v___x_4193_, v___x_4194_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_);
lean_dec_ref(v_xs_4173_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; lean_object* v___x_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4204_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
lean_inc(v_a_4196_);
lean_dec_ref_known(v___x_4195_, 1);
v___x_4197_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg(v_hyp_4172_, v_a_4196_, v___y_4183_);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4204_ == 0)
{
lean_object* v_unused_4205_; 
v_unused_4205_ = lean_ctor_get(v___x_4197_, 0);
lean_dec(v_unused_4205_);
v___x_4199_ = v___x_4197_;
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
else
{
lean_dec(v___x_4197_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___x_4202_; 
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 0, v_snd_4191_);
v___x_4202_ = v___x_4199_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_snd_4191_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
else
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
lean_dec(v_snd_4191_);
lean_dec(v_hyp_4172_);
v_a_4206_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___x_4195_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4195_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
}
else
{
lean_object* v_a_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4221_; 
lean_dec_ref(v_xs_4173_);
lean_dec(v_hyp_4172_);
v_a_4214_ = lean_ctor_get(v___x_4188_, 0);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4188_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4216_ = v___x_4188_;
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_a_4214_);
lean_dec(v___x_4188_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4219_; 
if (v_isShared_4217_ == 0)
{
v___x_4219_ = v___x_4216_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4214_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___lam__0___boxed(lean_object* v_a_4222_, lean_object* v_hyp_4223_, lean_object* v_xs_4224_, lean_object* v_x_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_){
_start:
{
lean_object* v_res_4238_; 
v_res_4238_ = l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___lam__0(v_a_4222_, v_hyp_4223_, v_xs_4224_, v_x_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
lean_dec(v___y_4232_);
lean_dec_ref(v___y_4231_);
lean_dec(v___y_4230_);
lean_dec_ref(v___y_4229_);
lean_dec(v___y_4228_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
lean_dec_ref(v_x_4225_);
lean_dec_ref(v_a_4222_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg(lean_object* v_jp_4239_, size_t v_sz_4240_, size_t v_i_4241_, lean_object* v_bs_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
uint8_t v___x_4248_; 
v___x_4248_ = lean_usize_dec_lt(v_i_4241_, v_sz_4240_);
if (v___x_4248_ == 0)
{
lean_object* v___x_4249_; 
v___x_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4249_, 0, v_bs_4242_);
return v___x_4249_;
}
else
{
lean_object* v_v_4250_; lean_object* v___x_4251_; lean_object* v_bs_x27_4252_; lean_object* v___x_4253_; 
v_v_4250_ = lean_array_uget(v_bs_4242_, v_i_4241_);
v___x_4251_ = lean_unsigned_to_nat(0u);
v_bs_x27_4252_ = lean_array_uset(v_bs_4242_, v_i_4241_, v___x_4251_);
lean_inc(v_v_4250_);
v___x_4253_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals(v_jp_4239_, v_v_4250_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; lean_object* v___x_4255_; size_t v___x_4256_; size_t v___x_4257_; lean_object* v___x_4258_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4254_);
lean_dec_ref_known(v___x_4253_, 1);
v___x_4255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4255_, 0, v_v_4250_);
lean_ctor_set(v___x_4255_, 1, v_a_4254_);
v___x_4256_ = ((size_t)1ULL);
v___x_4257_ = lean_usize_add(v_i_4241_, v___x_4256_);
v___x_4258_ = lean_array_uset(v_bs_x27_4252_, v_i_4241_, v___x_4255_);
v_i_4241_ = v___x_4257_;
v_bs_4242_ = v___x_4258_;
goto _start;
}
else
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4267_; 
lean_dec_ref(v_bs_x27_4252_);
lean_dec(v_v_4250_);
v_a_4260_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4262_ = v___x_4253_;
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4253_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4265_; 
if (v_isShared_4263_ == 0)
{
v___x_4265_ = v___x_4262_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_a_4260_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg___boxed(lean_object* v_jp_4268_, lean_object* v_sz_4269_, lean_object* v_i_4270_, lean_object* v_bs_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
size_t v_sz_boxed_4277_; size_t v_i_boxed_4278_; lean_object* v_res_4279_; 
v_sz_boxed_4277_ = lean_unbox_usize(v_sz_4269_);
lean_dec(v_sz_4269_);
v_i_boxed_4278_ = lean_unbox_usize(v_i_4270_);
lean_dec(v_i_4270_);
v_res_4279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg(v_jp_4268_, v_sz_boxed_4277_, v_i_boxed_4278_, v_bs_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec(v___y_4273_);
lean_dec_ref(v___y_4272_);
lean_dec_ref(v_jp_4268_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2(size_t v_sz_4280_, size_t v_i_4281_, lean_object* v_bs_4282_){
_start:
{
uint8_t v___x_4283_; 
v___x_4283_ = lean_usize_dec_lt(v_i_4281_, v_sz_4280_);
if (v___x_4283_ == 0)
{
return v_bs_4282_;
}
else
{
lean_object* v_v_4284_; lean_object* v___x_4285_; lean_object* v_bs_x27_4286_; lean_object* v___x_4287_; size_t v___x_4288_; size_t v___x_4289_; lean_object* v___x_4290_; 
v_v_4284_ = lean_array_uget(v_bs_4282_, v_i_4281_);
v___x_4285_ = lean_unsigned_to_nat(0u);
v_bs_x27_4286_ = lean_array_uset(v_bs_4282_, v_i_4281_, v___x_4285_);
v___x_4287_ = l_Lean_LocalDecl_toExpr(v_v_4284_);
v___x_4288_ = ((size_t)1ULL);
v___x_4289_ = lean_usize_add(v_i_4281_, v___x_4288_);
v___x_4290_ = lean_array_uset(v_bs_x27_4286_, v_i_4281_, v___x_4287_);
v_i_4281_ = v___x_4289_;
v_bs_4282_ = v___x_4290_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___boxed(lean_object* v_sz_4292_, lean_object* v_i_4293_, lean_object* v_bs_4294_){
_start:
{
size_t v_sz_boxed_4295_; size_t v_i_boxed_4296_; lean_object* v_res_4297_; 
v_sz_boxed_4295_ = lean_unbox_usize(v_sz_4292_);
lean_dec(v_sz_4292_);
v_i_boxed_4296_ = lean_unbox_usize(v_i_4293_);
lean_dec(v_i_4293_);
v_res_4297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2(v_sz_boxed_4295_, v_i_boxed_4296_, v_bs_4294_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__4(lean_object* v_as_4298_, size_t v_i_4299_, size_t v_stop_4300_, lean_object* v_b_4301_){
_start:
{
lean_object* v___y_4303_; uint8_t v___x_4307_; 
v___x_4307_ = lean_usize_dec_eq(v_i_4299_, v_stop_4300_);
if (v___x_4307_ == 0)
{
lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4308_ = lean_array_uget_borrowed(v_as_4298_, v_i_4299_);
v___x_4309_ = l_Lean_LocalDecl_value_x3f(v___x_4308_, v___x_4307_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v___x_4310_; 
lean_inc(v___x_4308_);
v___x_4310_ = lean_array_push(v_b_4301_, v___x_4308_);
v___y_4303_ = v___x_4310_;
goto v___jp_4302_;
}
else
{
lean_dec_ref_known(v___x_4309_, 1);
v___y_4303_ = v_b_4301_;
goto v___jp_4302_;
}
}
else
{
return v_b_4301_;
}
v___jp_4302_:
{
size_t v___x_4304_; size_t v___x_4305_; 
v___x_4304_ = ((size_t)1ULL);
v___x_4305_ = lean_usize_add(v_i_4299_, v___x_4304_);
v_i_4299_ = v___x_4305_;
v_b_4301_ = v___y_4303_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__4___boxed(lean_object* v_as_4311_, lean_object* v_i_4312_, lean_object* v_stop_4313_, lean_object* v_b_4314_){
_start:
{
size_t v_i_boxed_4315_; size_t v_stop_boxed_4316_; lean_object* v_res_4317_; 
v_i_boxed_4315_ = lean_unbox_usize(v_i_4312_);
lean_dec(v_i_4312_);
v_stop_boxed_4316_ = lean_unbox_usize(v_stop_4313_);
lean_dec(v_stop_4313_);
v_res_4317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__4(v_as_4311_, v_i_boxed_4315_, v_stop_boxed_4316_, v_b_4314_);
lean_dec_ref(v_as_4311_);
return v_res_4317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__5___lam__0(lean_object* v_proof_4318_, lean_object* v___x_4319_, lean_object* v_snd_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_){
_start:
{
lean_object* v___x_4333_; 
lean_inc(v_proof_4318_);
v___x_4333_ = l_Lean_MVarId_getType(v_proof_4318_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v_a_4334_; lean_object* v___x_4335_; 
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_a_4334_);
lean_dec_ref_known(v___x_4333_, 1);
v___x_4335_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___redArg(v_a_4334_, v___y_4329_);
if (lean_obj_tag(v___x_4335_) == 0)
{
lean_object* v_a_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
v_a_4336_ = lean_ctor_get(v___x_4335_, 0);
lean_inc(v_a_4336_);
lean_dec_ref_known(v___x_4335_, 1);
v___x_4337_ = lean_array_to_list(v___x_4319_);
v___x_4338_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v_a_4336_, v_snd_4320_, v___x_4337_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_object* v_a_4339_; lean_object* v___x_4340_; 
v_a_4339_ = lean_ctor_get(v___x_4338_, 0);
lean_inc(v_a_4339_);
lean_dec_ref_known(v___x_4338_, 1);
v___x_4340_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg(v_proof_4318_, v_a_4339_, v___y_4329_);
return v___x_4340_;
}
else
{
lean_object* v_a_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4348_; 
lean_dec(v_proof_4318_);
v_a_4341_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4348_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4343_ = v___x_4338_;
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_a_4341_);
lean_dec(v___x_4338_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4346_; 
if (v_isShared_4344_ == 0)
{
v___x_4346_ = v___x_4343_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_a_4341_);
v___x_4346_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
return v___x_4346_;
}
}
}
}
else
{
lean_object* v_a_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4356_; 
lean_dec(v_snd_4320_);
lean_dec_ref(v___x_4319_);
lean_dec(v_proof_4318_);
v_a_4349_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4356_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4351_ = v___x_4335_;
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_a_4349_);
lean_dec(v___x_4335_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
lean_object* v___x_4354_; 
if (v_isShared_4352_ == 0)
{
v___x_4354_ = v___x_4351_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_a_4349_);
v___x_4354_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
return v___x_4354_;
}
}
}
}
else
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
lean_dec(v_snd_4320_);
lean_dec_ref(v___x_4319_);
lean_dec(v_proof_4318_);
v_a_4357_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4359_ = v___x_4333_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4333_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__5___lam__0___boxed(lean_object* v_proof_4365_, lean_object* v___x_4366_, lean_object* v_snd_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_){
_start:
{
lean_object* v_res_4380_; 
v_res_4380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__5___lam__0(v_proof_4365_, v___x_4366_, v_snd_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
lean_dec(v___y_4378_);
lean_dec_ref(v___y_4377_);
lean_dec(v___y_4376_);
lean_dec_ref(v___y_4375_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
lean_dec(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
return v_res_4380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__5(lean_object* v_as_4381_, size_t v_sz_4382_, size_t v_i_4383_, lean_object* v_b_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_){
_start:
{
uint8_t v___x_4397_; 
v___x_4397_ = lean_usize_dec_lt(v_i_4383_, v_sz_4382_);
if (v___x_4397_ == 0)
{
lean_object* v___x_4398_; 
v___x_4398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4398_, 0, v_b_4384_);
return v___x_4398_;
}
else
{
lean_object* v_a_4399_; lean_object* v_fst_4400_; lean_object* v_fst_4401_; lean_object* v_snd_4402_; lean_object* v_snd_4403_; lean_object* v_proof_4404_; lean_object* v___x_4405_; lean_object* v___y_4407_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; uint8_t v___x_4419_; 
v_a_4399_ = lean_array_uget_borrowed(v_as_4381_, v_i_4383_);
v_fst_4400_ = lean_ctor_get(v_a_4399_, 0);
v_fst_4401_ = lean_ctor_get(v_fst_4400_, 0);
v_snd_4402_ = lean_ctor_get(v_a_4399_, 1);
v_snd_4403_ = lean_ctor_get(v_fst_4400_, 1);
v_proof_4404_ = lean_ctor_get(v_fst_4401_, 0);
v___x_4405_ = lean_box(0);
v___x_4416_ = lean_unsigned_to_nat(0u);
v___x_4417_ = lean_array_get_size(v_snd_4403_);
v___x_4418_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals___closed__0));
v___x_4419_ = lean_nat_dec_lt(v___x_4416_, v___x_4417_);
if (v___x_4419_ == 0)
{
v___y_4407_ = v___x_4418_;
goto v___jp_4406_;
}
else
{
size_t v___x_4420_; size_t v___x_4421_; lean_object* v___x_4422_; 
v___x_4420_ = ((size_t)0ULL);
v___x_4421_ = lean_usize_of_nat(v___x_4417_);
v___x_4422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__4(v_snd_4403_, v___x_4420_, v___x_4421_, v___x_4418_);
v___y_4407_ = v___x_4422_;
goto v___jp_4406_;
}
v___jp_4406_:
{
size_t v_sz_4408_; size_t v___x_4409_; lean_object* v___x_4410_; lean_object* v___f_4411_; lean_object* v___x_4412_; 
v_sz_4408_ = lean_array_size(v___y_4407_);
v___x_4409_ = ((size_t)0ULL);
v___x_4410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2(v_sz_4408_, v___x_4409_, v___y_4407_);
lean_inc(v_snd_4402_);
lean_inc_n(v_proof_4404_, 2);
v___f_4411_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__5___lam__0___boxed), 15, 3);
lean_closure_set(v___f_4411_, 0, v_proof_4404_);
lean_closure_set(v___f_4411_, 1, v___x_4410_);
lean_closure_set(v___f_4411_, 2, v_snd_4402_);
v___x_4412_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg(v_proof_4404_, v___f_4411_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
if (lean_obj_tag(v___x_4412_) == 0)
{
size_t v___x_4413_; size_t v___x_4414_; 
lean_dec_ref_known(v___x_4412_, 1);
v___x_4413_ = ((size_t)1ULL);
v___x_4414_ = lean_usize_add(v_i_4383_, v___x_4413_);
v_i_4383_ = v___x_4414_;
v_b_4384_ = v___x_4405_;
goto _start;
}
else
{
return v___x_4412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__5___boxed(lean_object* v_as_4423_, lean_object* v_sz_4424_, lean_object* v_i_4425_, lean_object* v_b_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
size_t v_sz_boxed_4439_; size_t v_i_boxed_4440_; lean_object* v_res_4441_; 
v_sz_boxed_4439_ = lean_unbox_usize(v_sz_4424_);
lean_dec(v_sz_4424_);
v_i_boxed_4440_ = lean_unbox_usize(v_i_4425_);
lean_dec(v_i_4425_);
v_res_4441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__5(v_as_4423_, v_sz_boxed_4439_, v_i_boxed_4440_, v_b_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
lean_dec_ref(v_as_4423_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint(lean_object* v_jp_4442_, lean_object* v_jumps_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_){
_start:
{
size_t v_sz_4456_; size_t v___x_4457_; lean_object* v___x_4458_; 
v_sz_4456_ = lean_array_size(v_jumps_4443_);
v___x_4457_ = ((size_t)0ULL);
v___x_4458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg(v_jp_4442_, v_sz_4456_, v___x_4457_, v_jumps_4443_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
if (lean_obj_tag(v___x_4458_) == 0)
{
lean_object* v_a_4459_; lean_object* v_hyp_4460_; lean_object* v___f_4461_; lean_object* v___x_4462_; 
v_a_4459_ = lean_ctor_get(v___x_4458_, 0);
lean_inc_n(v_a_4459_, 2);
lean_dec_ref_known(v___x_4458_, 1);
v_hyp_4460_ = lean_ctor_get(v_jp_4442_, 2);
lean_inc_n(v_hyp_4460_, 2);
lean_dec_ref(v_jp_4442_);
v___f_4461_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___lam__0___boxed), 16, 2);
lean_closure_set(v___f_4461_, 0, v_a_4459_);
lean_closure_set(v___f_4461_, 1, v_hyp_4460_);
v___x_4462_ = l_Lean_MVarId_getType(v_hyp_4460_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
if (lean_obj_tag(v___x_4462_) == 0)
{
lean_object* v_a_4463_; uint8_t v___x_4464_; lean_object* v___x_4465_; 
v_a_4463_ = lean_ctor_get(v___x_4462_, 0);
lean_inc(v_a_4463_);
lean_dec_ref_known(v___x_4462_, 1);
v___x_4464_ = 0;
v___x_4465_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg(v_a_4463_, v___f_4461_, v___x_4464_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
if (lean_obj_tag(v___x_4465_) == 0)
{
lean_object* v_a_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; size_t v_sz_4469_; lean_object* v___x_4470_; 
v_a_4466_ = lean_ctor_get(v___x_4465_, 0);
lean_inc(v_a_4466_);
lean_dec_ref_known(v___x_4465_, 1);
v___x_4467_ = l_Array_zip___redArg(v_a_4459_, v_a_4466_);
lean_dec(v_a_4466_);
lean_dec(v_a_4459_);
v___x_4468_ = lean_box(0);
v_sz_4469_ = lean_array_size(v___x_4467_);
v___x_4470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__5(v___x_4467_, v_sz_4469_, v___x_4457_, v___x_4468_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
lean_dec_ref(v___x_4467_);
if (lean_obj_tag(v___x_4470_) == 0)
{
lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4477_; 
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4477_ == 0)
{
lean_object* v_unused_4478_; 
v_unused_4478_ = lean_ctor_get(v___x_4470_, 0);
lean_dec(v_unused_4478_);
v___x_4472_ = v___x_4470_;
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
else
{
lean_dec(v___x_4470_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4475_; 
if (v_isShared_4473_ == 0)
{
lean_ctor_set(v___x_4472_, 0, v___x_4468_);
v___x_4475_ = v___x_4472_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v___x_4468_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
}
else
{
return v___x_4470_;
}
}
else
{
lean_object* v_a_4479_; lean_object* v___x_4481_; uint8_t v_isShared_4482_; uint8_t v_isSharedCheck_4486_; 
lean_dec(v_a_4459_);
v_a_4479_ = lean_ctor_get(v___x_4465_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v___x_4465_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4481_ = v___x_4465_;
v_isShared_4482_ = v_isSharedCheck_4486_;
goto v_resetjp_4480_;
}
else
{
lean_inc(v_a_4479_);
lean_dec(v___x_4465_);
v___x_4481_ = lean_box(0);
v_isShared_4482_ = v_isSharedCheck_4486_;
goto v_resetjp_4480_;
}
v_resetjp_4480_:
{
lean_object* v___x_4484_; 
if (v_isShared_4482_ == 0)
{
v___x_4484_ = v___x_4481_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v_a_4479_);
v___x_4484_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
return v___x_4484_;
}
}
}
}
else
{
lean_object* v_a_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4494_; 
lean_dec_ref(v___f_4461_);
lean_dec(v_a_4459_);
v_a_4487_ = lean_ctor_get(v___x_4462_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4462_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4489_ = v___x_4462_;
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_a_4487_);
lean_dec(v___x_4462_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4492_; 
if (v_isShared_4490_ == 0)
{
v___x_4492_ = v___x_4489_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v_a_4487_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
}
else
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4502_; 
lean_dec_ref(v_jp_4442_);
v_a_4495_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4497_ = v___x_4458_;
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4458_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4500_; 
if (v_isShared_4498_ == 0)
{
v___x_4500_ = v___x_4497_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_a_4495_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___boxed(lean_object* v_jp_4503_, lean_object* v_jumps_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint(v_jp_4503_, v_jumps_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_);
lean_dec(v_a_4515_);
lean_dec_ref(v_a_4514_);
lean_dec(v_a_4513_);
lean_dec_ref(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec_ref(v_a_4510_);
lean_dec(v_a_4509_);
lean_dec_ref(v_a_4508_);
lean_dec(v_a_4507_);
lean_dec(v_a_4506_);
lean_dec_ref(v_a_4505_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0(lean_object* v_jp_4518_, size_t v_sz_4519_, size_t v_i_4520_, lean_object* v_bs_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
lean_object* v___x_4534_; 
v___x_4534_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg(v_jp_4518_, v_sz_4519_, v_i_4520_, v_bs_4521_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_);
return v___x_4534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___boxed(lean_object* v_jp_4535_, lean_object* v_sz_4536_, lean_object* v_i_4537_, lean_object* v_bs_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_){
_start:
{
size_t v_sz_boxed_4551_; size_t v_i_boxed_4552_; lean_object* v_res_4553_; 
v_sz_boxed_4551_ = lean_unbox_usize(v_sz_4536_);
lean_dec(v_sz_4536_);
v_i_boxed_4552_ = lean_unbox_usize(v_i_4537_);
lean_dec(v_i_4537_);
v_res_4553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0(v_jp_4535_, v_sz_boxed_4551_, v_i_boxed_4552_, v_bs_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
lean_dec(v___y_4541_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
lean_dec_ref(v_jp_4535_);
return v_res_4553_;
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
