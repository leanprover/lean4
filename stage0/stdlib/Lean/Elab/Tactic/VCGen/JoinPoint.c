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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_betaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
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
lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__1___redArg(lean_object* v_x_166_, uint8_t v_bi_167_, lean_object* v_t_168_, lean_object* v_b_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___y_178_; lean_object* v___x_181_; uint8_t v_debug_182_; 
v___x_181_ = lean_st_ref_get(v___y_171_);
v_debug_182_ = lean_ctor_get_uint8(v___x_181_, sizeof(void*)*13);
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
v_debug_385_ = lean_ctor_get_uint8(v___x_384_, sizeof(void*)*13);
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
v_debug_577_ = lean_ctor_get_uint8(v___x_576_, sizeof(void*)*13);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_x_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_, lean_object* v_x_1701_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__5___redArg(lean_object* v_n_1728_, lean_object* v_k_1729_, lean_object* v_v_1730_){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = lean_unsigned_to_nat(0u);
v___x_1732_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__5_spec__7___redArg(v_n_1728_, v___x_1731_, v_k_1729_, v_v_1730_);
return v___x_1732_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3___redArg(lean_object* v_x_1734_, size_t v_x_1735_, size_t v_x_1736_, lean_object* v_x_1737_, lean_object* v_x_1738_){
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
v___x_1777_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3___redArg(v_node_1769_, v___x_1774_, v___x_1776_, v_x_1737_, v_x_1738_);
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
v_newNode_1792_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__5___redArg(v___x_1791_, v_x_1737_, v_x_1738_);
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
v___x_1801_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3___redArg___closed__0);
v___x_1802_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__6___redArg(v_x_1736_, v_ks_1798_, v_vs_1799_, v___x_1800_, v___x_1801_);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__6___redArg(size_t v_depth_1805_, lean_object* v_keys_1806_, lean_object* v_vals_1807_, lean_object* v_i_1808_, lean_object* v_entries_1809_){
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
v___x_1823_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3___redArg(v_entries_1809_, v_h_1821_, v_depth_1805_, v_k_1812_, v_v_1813_);
v_i_1808_ = v___x_1822_;
v_entries_1809_ = v___x_1823_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_1825_, lean_object* v_keys_1826_, lean_object* v_vals_1827_, lean_object* v_i_1828_, lean_object* v_entries_1829_){
_start:
{
size_t v_depth_boxed_1830_; lean_object* v_res_1831_; 
v_depth_boxed_1830_ = lean_unbox_usize(v_depth_1825_);
lean_dec(v_depth_1825_);
v_res_1831_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__6___redArg(v_depth_boxed_1830_, v_keys_1826_, v_vals_1827_, v_i_1828_, v_entries_1829_);
lean_dec_ref(v_vals_1827_);
lean_dec_ref(v_keys_1826_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_x_1832_, lean_object* v_x_1833_, lean_object* v_x_1834_, lean_object* v_x_1835_, lean_object* v_x_1836_){
_start:
{
size_t v_x_19583__boxed_1837_; size_t v_x_19584__boxed_1838_; lean_object* v_res_1839_; 
v_x_19583__boxed_1837_ = lean_unbox_usize(v_x_1833_);
lean_dec(v_x_1833_);
v_x_19584__boxed_1838_ = lean_unbox_usize(v_x_1834_);
lean_dec(v_x_1834_);
v_res_1839_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3___redArg(v_x_1832_, v_x_19583__boxed_1837_, v_x_19584__boxed_1838_, v_x_1835_, v_x_1836_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2___redArg(lean_object* v_x_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_){
_start:
{
uint64_t v___x_1843_; size_t v___x_1844_; size_t v___x_1845_; lean_object* v___x_1846_; 
v___x_1843_ = l_Lean_instHashableMVarId_hash(v_x_1841_);
v___x_1844_ = lean_uint64_to_usize(v___x_1843_);
v___x_1845_ = ((size_t)1ULL);
v___x_1846_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3___redArg(v_x_1840_, v___x_1844_, v___x_1845_, v_x_1841_, v_x_1842_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg(lean_object* v_mvarId_1847_, lean_object* v_val_1848_, lean_object* v___y_1849_){
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
v___x_1876_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2___redArg(v_eAssignment_1868_, v_mvarId_1847_, v_val_1848_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg___boxed(lean_object* v_mvarId_1887_, lean_object* v_val_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg(v_mvarId_1887_, v_val_1888_, v___y_1889_);
lean_dec(v___y_1889_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__4(lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_x_1895_){
_start:
{
if (lean_obj_tag(v_x_1895_) == 0)
{
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
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
v___x_1903_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__4(v_a_1892_, v_a_1893_, v_a_1894_, v_tail_1898_);
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
lean_ctor_set(v___x_1913_, 1, v_a_1893_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__4___boxed(lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_x_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__4(v_a_1923_, v_a_1924_, v_a_1925_, v_x_1926_);
lean_dec_ref(v_a_1923_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3(lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_m_1930_, lean_object* v_a_1931_){
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
lean_dec_ref(v_a_1929_);
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
v_bucket_1954_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__4(v_a_1928_, v_a_1929_, v_a_1931_, v_bucket_1947_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3___boxed(lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_m_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3(v_a_1962_, v_a_1963_, v_m_1964_, v_a_1965_);
lean_dec_ref(v_a_1962_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg(size_t v_sz_1967_, size_t v_i_1968_, lean_object* v_bs_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
uint8_t v___x_1977_; 
v___x_1977_ = lean_usize_dec_lt(v_i_1968_, v_sz_1967_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v_bs_1969_);
return v___x_1978_;
}
else
{
lean_object* v_v_1979_; lean_object* v___x_1980_; lean_object* v_bs_x27_1981_; lean_object* v___x_1982_; 
v_v_1979_ = lean_array_uget(v_bs_1969_, v_i_1968_);
v___x_1980_ = lean_unsigned_to_nat(0u);
v_bs_x27_1981_ = lean_array_uset(v_bs_1969_, v_i_1968_, v___x_1980_);
v___x_1982_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v_v_1979_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; size_t v___x_1984_; size_t v___x_1985_; lean_object* v___x_1986_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1983_);
lean_dec_ref_known(v___x_1982_, 1);
v___x_1984_ = ((size_t)1ULL);
v___x_1985_ = lean_usize_add(v_i_1968_, v___x_1984_);
v___x_1986_ = lean_array_uset(v_bs_x27_1981_, v_i_1968_, v_a_1983_);
v_i_1968_ = v___x_1985_;
v_bs_1969_ = v___x_1986_;
goto _start;
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec_ref(v_bs_x27_1981_);
v_a_1988_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1982_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1982_);
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
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg___boxed(lean_object* v_sz_1996_, lean_object* v_i_1997_, lean_object* v_bs_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
size_t v_sz_boxed_2006_; size_t v_i_boxed_2007_; lean_object* v_res_2008_; 
v_sz_boxed_2006_ = lean_unbox_usize(v_sz_1996_);
lean_dec(v_sz_1996_);
v_i_boxed_2007_ = lean_unbox_usize(v_i_1997_);
lean_dec(v_i_1997_);
v_res_2008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg(v_sz_boxed_2006_, v_i_boxed_2007_, v_bs_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
return v_res_2008_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2009_; lean_object* v_dummy_2010_; 
v___x_2009_ = lean_box(0);
v_dummy_2010_ = l_Lean_Expr_sort___override(v___x_2009_);
return v_dummy_2010_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__2));
v___x_2015_ = l_Lean_stringToMessageData(v___x_2014_);
return v___x_2015_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__4));
v___x_2018_ = l_Lean_stringToMessageData(v___x_2017_);
return v___x_2018_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__6));
v___x_2021_ = l_Lean_stringToMessageData(v___x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0(lean_object* v_info_2022_, lean_object* v___x_2023_, lean_object* v_val_2024_, lean_object* v_goal_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v___x_2129_; 
lean_inc(v_goal_2025_);
v___x_2129_ = l_Lean_MVarId_getType(v_goal_2025_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2176_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2132_ = v___x_2129_;
v_isShared_2133_ = v_isSharedCheck_2176_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2129_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2176_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2134_ = l_Lean_Expr_cleanupAnnotations(v_a_2130_);
lean_dec(v_a_2130_);
v___x_2135_ = l_Lean_Expr_isApp(v___x_2134_);
if (v___x_2135_ == 0)
{
lean_dec_ref(v___x_2134_);
lean_del_object(v___x_2132_);
lean_dec(v_goal_2025_);
lean_dec_ref(v_val_2024_);
lean_dec_ref(v___x_2023_);
goto v___jp_2038_;
}
else
{
lean_object* v___x_2136_; uint8_t v___x_2137_; 
v___x_2136_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2134_);
lean_dec_ref(v___x_2134_);
v___x_2137_ = l_Lean_Expr_isApp(v___x_2136_);
if (v___x_2137_ == 0)
{
lean_dec_ref(v___x_2136_);
lean_del_object(v___x_2132_);
lean_dec(v_goal_2025_);
lean_dec_ref(v_val_2024_);
lean_dec_ref(v___x_2023_);
goto v___jp_2038_;
}
else
{
lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2138_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2136_);
v___x_2139_ = l_Lean_Expr_isApp(v___x_2138_);
if (v___x_2139_ == 0)
{
lean_dec_ref(v___x_2138_);
lean_dec_ref(v___x_2136_);
lean_del_object(v___x_2132_);
lean_dec(v_goal_2025_);
lean_dec_ref(v_val_2024_);
lean_dec_ref(v___x_2023_);
goto v___jp_2038_;
}
else
{
lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2140_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2138_);
lean_dec_ref(v___x_2138_);
v___x_2141_ = l_Lean_Expr_isApp(v___x_2140_);
if (v___x_2141_ == 0)
{
lean_dec_ref(v___x_2140_);
lean_dec_ref(v___x_2136_);
lean_del_object(v___x_2132_);
lean_dec(v_goal_2025_);
lean_dec_ref(v_val_2024_);
lean_dec_ref(v___x_2023_);
goto v___jp_2038_;
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v___x_2142_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2140_);
lean_dec_ref(v___x_2140_);
v___x_2143_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__2));
v___x_2144_ = l_Lean_Expr_isConstOf(v___x_2142_, v___x_2143_);
lean_dec_ref(v___x_2142_);
if (v___x_2144_ == 0)
{
lean_dec_ref(v___x_2136_);
lean_del_object(v___x_2132_);
lean_dec(v_goal_2025_);
lean_dec_ref(v_val_2024_);
lean_dec_ref(v___x_2023_);
goto v___jp_2038_;
}
else
{
lean_object* v_arg_2145_; lean_object* v_top_2146_; lean_object* v_numStates_2147_; uint8_t v___x_2148_; 
v_arg_2145_ = lean_ctor_get(v___x_2136_, 1);
lean_inc_ref(v_arg_2145_);
lean_dec_ref(v___x_2136_);
v_top_2146_ = lean_ctor_get(v_val_2024_, 1);
v_numStates_2147_ = lean_ctor_get(v_val_2024_, 4);
v___x_2148_ = lean_expr_eqv(v_arg_2145_, v_top_2146_);
lean_dec_ref(v_arg_2145_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2151_; 
lean_dec(v_goal_2025_);
lean_dec_ref(v_val_2024_);
lean_dec_ref(v___x_2023_);
v___x_2149_ = lean_box(0);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 0, v___x_2149_);
v___x_2151_ = v___x_2132_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2149_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
else
{
lean_object* v_excessArgs_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; 
lean_del_object(v___x_2132_);
v_excessArgs_2153_ = lean_ctor_get(v_info_2022_, 3);
v___x_2154_ = lean_array_get_size(v_excessArgs_2153_);
v___x_2155_ = lean_nat_dec_eq(v___x_2154_, v_numStates_2147_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_inc(v_numStates_2147_);
lean_dec(v_goal_2025_);
lean_dec_ref(v_val_2024_);
v___x_2156_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__3, &l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__3);
v___x_2157_ = l_Lean_indentExpr(v___x_2023_);
v___x_2158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2156_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__5, &l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__5);
v___x_2160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2158_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = l_Nat_reprFast(v_numStates_2147_);
v___x_2162_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
v___x_2163_ = l_Lean_MessageData_ofFormat(v___x_2162_);
v___x_2164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2160_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__7, &l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__7);
v___x_2166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2164_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
v___x_2167_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___redArg(v___x_2166_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2167_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2167_);
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
else
{
goto v___jp_2041_;
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
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec(v_goal_2025_);
lean_dec_ref(v_val_2024_);
lean_dec_ref(v___x_2023_);
v_a_2177_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2129_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2129_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
v___jp_2038_:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = lean_box(0);
v___x_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
return v___x_2040_;
}
v___jp_2041_:
{
lean_object* v_excessArgs_2042_; lean_object* v_nargs_2043_; lean_object* v_dummy_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; size_t v_sz_2050_; size_t v___x_2051_; lean_object* v___x_2052_; 
v_excessArgs_2042_ = lean_ctor_get(v_info_2022_, 3);
v_nargs_2043_ = l_Lean_Expr_getAppNumArgs(v___x_2023_);
v_dummy_2044_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__0, &l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__0);
lean_inc(v_nargs_2043_);
v___x_2045_ = lean_mk_array(v_nargs_2043_, v_dummy_2044_);
v___x_2046_ = lean_unsigned_to_nat(1u);
v___x_2047_ = lean_nat_sub(v_nargs_2043_, v___x_2046_);
lean_dec(v_nargs_2043_);
v___x_2048_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_2023_, v___x_2045_, v___x_2047_);
v___x_2049_ = l_Array_append___redArg(v___x_2048_, v_excessArgs_2042_);
v_sz_2050_ = lean_array_size(v___x_2049_);
v___x_2051_ = ((size_t)0ULL);
v___x_2052_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg(v_sz_2050_, v___x_2051_, v___x_2049_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v_spec_2054_; lean_object* v_hyp_2055_; lean_object* v_rhsGoal_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref_known(v___x_2052_, 1);
v_spec_2054_ = lean_ctor_get(v_val_2024_, 0);
lean_inc_ref(v_spec_2054_);
v_hyp_2055_ = lean_ctor_get(v_val_2024_, 2);
lean_inc(v_hyp_2055_);
v_rhsGoal_2056_ = lean_ctor_get(v_val_2024_, 3);
lean_inc(v_rhsGoal_2056_);
lean_dec_ref(v_val_2024_);
v___x_2057_ = l_Lean_Expr_mvar___override(v_hyp_2055_);
v___x_2058_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0(v___x_2057_, v_a_2053_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v___x_2060_ = lean_box(0);
v___x_2061_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2059_, v___x_2060_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc_n(v_a_2062_, 2);
lean_dec_ref_known(v___x_2061_, 1);
lean_inc(v_a_2053_);
v___x_2063_ = lean_array_push(v_a_2053_, v_a_2062_);
v___x_2064_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0(v_spec_2054_, v___x_2063_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
lean_dec_ref(v___x_2063_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v___x_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2095_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref_known(v___x_2064_, 1);
v___x_2066_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg(v_goal_2025_, v_a_2065_, v___y_2034_);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2095_ == 0)
{
lean_object* v_unused_2096_; 
v_unused_2096_ = lean_ctor_get(v___x_2066_, 0);
lean_dec(v_unused_2096_);
v___x_2068_ = v___x_2066_;
v_isShared_2069_ = v_isSharedCheck_2095_;
goto v_resetjp_2067_;
}
else
{
lean_dec(v___x_2066_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2095_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; lean_object* v_specBackwardRuleCache_2071_; lean_object* v_splitBackwardRuleCache_2072_; lean_object* v_latticeBackwardRuleCache_2073_; lean_object* v_frameBackwardRuleCache_2074_; lean_object* v_frameDB_2075_; lean_object* v_invariants_2076_; lean_object* v_vcs_2077_; lean_object* v_simpState_2078_; lean_object* v_fuel_2079_; lean_object* v_inlineHandledInvariants_2080_; lean_object* v_pendingJoinPoints_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2094_; 
v___x_2070_ = lean_st_ref_take(v___y_2027_);
v_specBackwardRuleCache_2071_ = lean_ctor_get(v___x_2070_, 0);
v_splitBackwardRuleCache_2072_ = lean_ctor_get(v___x_2070_, 1);
v_latticeBackwardRuleCache_2073_ = lean_ctor_get(v___x_2070_, 2);
v_frameBackwardRuleCache_2074_ = lean_ctor_get(v___x_2070_, 3);
v_frameDB_2075_ = lean_ctor_get(v___x_2070_, 4);
v_invariants_2076_ = lean_ctor_get(v___x_2070_, 5);
v_vcs_2077_ = lean_ctor_get(v___x_2070_, 6);
v_simpState_2078_ = lean_ctor_get(v___x_2070_, 7);
v_fuel_2079_ = lean_ctor_get(v___x_2070_, 8);
v_inlineHandledInvariants_2080_ = lean_ctor_get(v___x_2070_, 9);
v_pendingJoinPoints_2081_ = lean_ctor_get(v___x_2070_, 10);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2083_ = v___x_2070_;
v_isShared_2084_ = v_isSharedCheck_2094_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_pendingJoinPoints_2081_);
lean_inc(v_inlineHandledInvariants_2080_);
lean_inc(v_fuel_2079_);
lean_inc(v_simpState_2078_);
lean_inc(v_vcs_2077_);
lean_inc(v_invariants_2076_);
lean_inc(v_frameDB_2075_);
lean_inc(v_frameBackwardRuleCache_2074_);
lean_inc(v_latticeBackwardRuleCache_2073_);
lean_inc(v_splitBackwardRuleCache_2072_);
lean_inc(v_specBackwardRuleCache_2071_);
lean_dec(v___x_2070_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2094_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2085_; lean_object* v___x_2087_; 
v___x_2085_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3(v_a_2062_, v_a_2053_, v_pendingJoinPoints_2081_, v_rhsGoal_2056_);
lean_dec(v_a_2062_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 10, v___x_2085_);
v___x_2087_ = v___x_2083_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_specBackwardRuleCache_2071_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_splitBackwardRuleCache_2072_);
lean_ctor_set(v_reuseFailAlloc_2093_, 2, v_latticeBackwardRuleCache_2073_);
lean_ctor_set(v_reuseFailAlloc_2093_, 3, v_frameBackwardRuleCache_2074_);
lean_ctor_set(v_reuseFailAlloc_2093_, 4, v_frameDB_2075_);
lean_ctor_set(v_reuseFailAlloc_2093_, 5, v_invariants_2076_);
lean_ctor_set(v_reuseFailAlloc_2093_, 6, v_vcs_2077_);
lean_ctor_set(v_reuseFailAlloc_2093_, 7, v_simpState_2078_);
lean_ctor_set(v_reuseFailAlloc_2093_, 8, v_fuel_2079_);
lean_ctor_set(v_reuseFailAlloc_2093_, 9, v_inlineHandledInvariants_2080_);
lean_ctor_set(v_reuseFailAlloc_2093_, 10, v___x_2085_);
v___x_2087_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2088_ = lean_st_ref_put(v___y_2027_, v___x_2087_);
v___x_2089_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__1));
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 0, v___x_2089_);
v___x_2091_ = v___x_2068_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec(v_a_2062_);
lean_dec(v_rhsGoal_2056_);
lean_dec(v_a_2053_);
lean_dec(v_goal_2025_);
v_a_2097_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2064_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2064_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec(v_rhsGoal_2056_);
lean_dec_ref(v_spec_2054_);
lean_dec(v_a_2053_);
lean_dec(v_goal_2025_);
v_a_2105_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2061_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2061_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec(v_rhsGoal_2056_);
lean_dec_ref(v_spec_2054_);
lean_dec(v_a_2053_);
lean_dec(v_goal_2025_);
v_a_2113_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2058_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2058_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
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
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec(v_goal_2025_);
lean_dec_ref(v_val_2024_);
v_a_2121_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2052_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2052_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___boxed(lean_object* v_info_2185_, lean_object* v___x_2186_, lean_object* v_val_2187_, lean_object* v_goal_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0(v_info_2185_, v___x_2186_, v_val_2187_, v_goal_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec_ref(v_info_2185_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg(lean_object* v_t_2202_, lean_object* v_k_2203_){
_start:
{
if (lean_obj_tag(v_t_2202_) == 0)
{
lean_object* v_k_2204_; lean_object* v_v_2205_; lean_object* v_l_2206_; lean_object* v_r_2207_; uint8_t v___x_2208_; 
v_k_2204_ = lean_ctor_get(v_t_2202_, 1);
v_v_2205_ = lean_ctor_get(v_t_2202_, 2);
v_l_2206_ = lean_ctor_get(v_t_2202_, 3);
v_r_2207_ = lean_ctor_get(v_t_2202_, 4);
v___x_2208_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2203_, v_k_2204_);
switch(v___x_2208_)
{
case 0:
{
v_t_2202_ = v_l_2206_;
goto _start;
}
case 1:
{
lean_object* v___x_2210_; 
lean_inc(v_v_2205_);
v___x_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2210_, 0, v_v_2205_);
return v___x_2210_;
}
default: 
{
v_t_2202_ = v_r_2207_;
goto _start;
}
}
}
else
{
lean_object* v___x_2212_; 
v___x_2212_ = lean_box(0);
return v___x_2212_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg___boxed(lean_object* v_t_2213_, lean_object* v_k_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg(v_t_2213_, v_k_2214_);
lean_dec(v_k_2214_);
lean_dec(v_t_2213_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f(lean_object* v_scope_2216_, lean_object* v_goal_2217_, lean_object* v_info_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_2218_);
v___x_2232_ = l_Lean_Expr_getAppFn(v___x_2231_);
v___x_2233_ = l_Lean_Expr_fvarId_x3f(v___x_2232_);
lean_dec_ref(v___x_2232_);
if (lean_obj_tag(v___x_2233_) == 1)
{
lean_object* v_val_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2247_; 
v_val_2234_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2236_ = v___x_2233_;
v_isShared_2237_ = v_isSharedCheck_2247_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_val_2234_);
lean_dec(v___x_2233_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2247_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v_joinPoints_2238_; lean_object* v___x_2239_; 
v_joinPoints_2238_ = lean_ctor_get(v_scope_2216_, 3);
v___x_2239_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg(v_joinPoints_2238_, v_val_2234_);
lean_dec(v_val_2234_);
if (lean_obj_tag(v___x_2239_) == 1)
{
lean_object* v_val_2240_; lean_object* v___f_2241_; lean_object* v___x_2242_; 
lean_del_object(v___x_2236_);
v_val_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_val_2240_);
lean_dec_ref_known(v___x_2239_, 1);
lean_inc(v_goal_2217_);
v___f_2241_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___boxed), 16, 4);
lean_closure_set(v___f_2241_, 0, v_info_2218_);
lean_closure_set(v___f_2241_, 1, v___x_2231_);
lean_closure_set(v___f_2241_, 2, v_val_2240_);
lean_closure_set(v___f_2241_, 3, v_goal_2217_);
v___x_2242_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg(v_goal_2217_, v___f_2241_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
return v___x_2242_;
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2245_; 
lean_dec(v___x_2239_);
lean_dec_ref(v___x_2231_);
lean_dec_ref(v_info_2218_);
lean_dec(v_goal_2217_);
v___x_2243_ = lean_box(0);
if (v_isShared_2237_ == 0)
{
lean_ctor_set_tag(v___x_2236_, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2243_);
v___x_2245_ = v___x_2236_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2243_);
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
lean_object* v___x_2248_; lean_object* v___x_2249_; 
lean_dec(v___x_2233_);
lean_dec_ref(v___x_2231_);
lean_dec_ref(v_info_2218_);
lean_dec(v_goal_2217_);
v___x_2248_ = lean_box(0);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
return v___x_2249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___boxed(lean_object* v_scope_2250_, lean_object* v_goal_2251_, lean_object* v_info_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Lean_Elab_Tactic_VCGen_wpJump_x3f(v_scope_2250_, v_goal_2251_, v_info_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_);
lean_dec(v_a_2263_);
lean_dec_ref(v_a_2262_);
lean_dec(v_a_2261_);
lean_dec_ref(v_a_2260_);
lean_dec(v_a_2259_);
lean_dec_ref(v_a_2258_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
lean_dec(v_a_2255_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
lean_dec_ref(v_scope_2250_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0(lean_object* v_00_u03b4_2266_, lean_object* v_t_2267_, lean_object* v_k_2268_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg(v_t_2267_, v_k_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___boxed(lean_object* v_00_u03b4_2270_, lean_object* v_t_2271_, lean_object* v_k_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0(v_00_u03b4_2270_, v_t_2271_, v_k_2272_);
lean_dec(v_k_2272_);
lean_dec(v_t_2271_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1(size_t v_sz_2274_, size_t v_i_2275_, lean_object* v_bs_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg(v_sz_2274_, v_i_2275_, v_bs_2276_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___boxed(lean_object* v_sz_2290_, lean_object* v_i_2291_, lean_object* v_bs_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
size_t v_sz_boxed_2305_; size_t v_i_boxed_2306_; lean_object* v_res_2307_; 
v_sz_boxed_2305_ = lean_unbox_usize(v_sz_2290_);
lean_dec(v_sz_2290_);
v_i_boxed_2306_ = lean_unbox_usize(v_i_2291_);
lean_dec(v_i_2291_);
v_res_2307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1(v_sz_boxed_2305_, v_i_boxed_2306_, v_bs_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2(lean_object* v_mvarId_2308_, lean_object* v_val_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg(v_mvarId_2308_, v_val_2309_, v___y_2318_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___boxed(lean_object* v_mvarId_2323_, lean_object* v_val_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2(v_mvarId_2323_, v_val_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2(lean_object* v_00_u03b2_2338_, lean_object* v_x_2339_, lean_object* v_x_2340_, lean_object* v_x_2341_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2___redArg(v_x_2339_, v_x_2340_, v_x_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_2343_, lean_object* v_x_2344_, size_t v_x_2345_, size_t v_x_2346_, lean_object* v_x_2347_, lean_object* v_x_2348_){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3___redArg(v_x_2344_, v_x_2345_, v_x_2346_, v_x_2347_, v_x_2348_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2350_, lean_object* v_x_2351_, lean_object* v_x_2352_, lean_object* v_x_2353_, lean_object* v_x_2354_, lean_object* v_x_2355_){
_start:
{
size_t v_x_20455__boxed_2356_; size_t v_x_20456__boxed_2357_; lean_object* v_res_2358_; 
v_x_20455__boxed_2356_ = lean_unbox_usize(v_x_2352_);
lean_dec(v_x_2352_);
v_x_20456__boxed_2357_ = lean_unbox_usize(v_x_2353_);
lean_dec(v_x_2353_);
v_res_2358_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3(v_00_u03b2_2350_, v_x_2351_, v_x_20455__boxed_2356_, v_x_20456__boxed_2357_, v_x_2354_, v_x_2355_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_2359_, lean_object* v_n_2360_, lean_object* v_k_2361_, lean_object* v_v_2362_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__5___redArg(v_n_2360_, v_k_2361_, v_v_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_2364_, size_t v_depth_2365_, lean_object* v_keys_2366_, lean_object* v_vals_2367_, lean_object* v_heq_2368_, lean_object* v_i_2369_, lean_object* v_entries_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__6___redArg(v_depth_2365_, v_keys_2366_, v_vals_2367_, v_i_2369_, v_entries_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2372_, lean_object* v_depth_2373_, lean_object* v_keys_2374_, lean_object* v_vals_2375_, lean_object* v_heq_2376_, lean_object* v_i_2377_, lean_object* v_entries_2378_){
_start:
{
size_t v_depth_boxed_2379_; lean_object* v_res_2380_; 
v_depth_boxed_2379_ = lean_unbox_usize(v_depth_2373_);
lean_dec(v_depth_2373_);
v_res_2380_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__6(v_00_u03b2_2372_, v_depth_boxed_2379_, v_keys_2374_, v_vals_2375_, v_heq_2376_, v_i_2377_, v_entries_2378_);
lean_dec_ref(v_vals_2375_);
lean_dec_ref(v_keys_2374_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_2381_, lean_object* v_x_2382_, lean_object* v_x_2383_, lean_object* v_x_2384_, lean_object* v_x_2385_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__5_spec__7___redArg(v_x_2382_, v_x_2383_, v_x_2384_, v_x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(lean_object* v_as_2387_, size_t v_i_2388_, size_t v_stop_2389_, lean_object* v_b_2390_){
_start:
{
lean_object* v___y_2392_; uint8_t v___x_2396_; 
v___x_2396_ = lean_usize_dec_eq(v_i_2388_, v_stop_2389_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; 
v___x_2397_ = lean_array_uget_borrowed(v_as_2387_, v_i_2388_);
if (lean_obj_tag(v___x_2397_) == 0)
{
v___y_2392_ = v_b_2390_;
goto v___jp_2391_;
}
else
{
lean_object* v_val_2398_; uint8_t v___x_2399_; 
v_val_2398_ = lean_ctor_get(v___x_2397_, 0);
v___x_2399_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2398_);
if (v___x_2399_ == 0)
{
lean_object* v___x_2400_; 
lean_inc(v_val_2398_);
v___x_2400_ = lean_array_push(v_b_2390_, v_val_2398_);
v___y_2392_ = v___x_2400_;
goto v___jp_2391_;
}
else
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Lean_LocalDecl_value_x3f(v_val_2398_, v___x_2396_);
if (lean_obj_tag(v___x_2401_) == 0)
{
v___y_2392_ = v_b_2390_;
goto v___jp_2391_;
}
else
{
lean_object* v___x_2402_; 
lean_dec_ref_known(v___x_2401_, 1);
lean_inc(v_val_2398_);
v___x_2402_ = lean_array_push(v_b_2390_, v_val_2398_);
v___y_2392_ = v___x_2402_;
goto v___jp_2391_;
}
}
}
}
else
{
return v_b_2390_;
}
v___jp_2391_:
{
size_t v___x_2393_; size_t v___x_2394_; 
v___x_2393_ = ((size_t)1ULL);
v___x_2394_ = lean_usize_add(v_i_2388_, v___x_2393_);
v_i_2388_ = v___x_2394_;
v_b_2390_ = v___y_2392_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2___boxed(lean_object* v_as_2403_, lean_object* v_i_2404_, lean_object* v_stop_2405_, lean_object* v_b_2406_){
_start:
{
size_t v_i_boxed_2407_; size_t v_stop_boxed_2408_; lean_object* v_res_2409_; 
v_i_boxed_2407_ = lean_unbox_usize(v_i_2404_);
lean_dec(v_i_2404_);
v_stop_boxed_2408_ = lean_unbox_usize(v_stop_2405_);
lean_dec(v_stop_2405_);
v_res_2409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_as_2403_, v_i_boxed_2407_, v_stop_boxed_2408_, v_b_2406_);
lean_dec_ref(v_as_2403_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3(lean_object* v_x_2410_, lean_object* v_x_2411_){
_start:
{
if (lean_obj_tag(v_x_2410_) == 0)
{
lean_object* v_cs_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v_cs_2412_ = lean_ctor_get(v_x_2410_, 0);
v___x_2413_ = lean_unsigned_to_nat(0u);
v___x_2414_ = lean_array_get_size(v_cs_2412_);
v___x_2415_ = lean_nat_dec_lt(v___x_2413_, v___x_2414_);
if (v___x_2415_ == 0)
{
return v_x_2411_;
}
else
{
size_t v___x_2416_; size_t v___x_2417_; lean_object* v___x_2418_; 
v___x_2416_ = ((size_t)0ULL);
v___x_2417_ = lean_usize_of_nat(v___x_2414_);
v___x_2418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2(v_cs_2412_, v___x_2416_, v___x_2417_, v_x_2411_);
return v___x_2418_;
}
}
else
{
lean_object* v_vs_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; uint8_t v___x_2422_; 
v_vs_2419_ = lean_ctor_get(v_x_2410_, 0);
v___x_2420_ = lean_unsigned_to_nat(0u);
v___x_2421_ = lean_array_get_size(v_vs_2419_);
v___x_2422_ = lean_nat_dec_lt(v___x_2420_, v___x_2421_);
if (v___x_2422_ == 0)
{
return v_x_2411_;
}
else
{
size_t v___x_2423_; size_t v___x_2424_; lean_object* v___x_2425_; 
v___x_2423_ = ((size_t)0ULL);
v___x_2424_ = lean_usize_of_nat(v___x_2421_);
v___x_2425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_vs_2419_, v___x_2423_, v___x_2424_, v_x_2411_);
return v___x_2425_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_2426_, size_t v_i_2427_, size_t v_stop_2428_, lean_object* v_b_2429_){
_start:
{
uint8_t v___x_2430_; 
v___x_2430_ = lean_usize_dec_eq(v_i_2427_, v_stop_2428_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; lean_object* v___x_2432_; size_t v___x_2433_; size_t v___x_2434_; 
v___x_2431_ = lean_array_uget_borrowed(v_as_2426_, v_i_2427_);
v___x_2432_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3(v___x_2431_, v_b_2429_);
v___x_2433_ = ((size_t)1ULL);
v___x_2434_ = lean_usize_add(v_i_2427_, v___x_2433_);
v_i_2427_ = v___x_2434_;
v_b_2429_ = v___x_2432_;
goto _start;
}
else
{
return v_b_2429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_2436_, lean_object* v_i_2437_, lean_object* v_stop_2438_, lean_object* v_b_2439_){
_start:
{
size_t v_i_boxed_2440_; size_t v_stop_boxed_2441_; lean_object* v_res_2442_; 
v_i_boxed_2440_ = lean_unbox_usize(v_i_2437_);
lean_dec(v_i_2437_);
v_stop_boxed_2441_ = lean_unbox_usize(v_stop_2438_);
lean_dec(v_stop_2438_);
v_res_2442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2(v_as_2436_, v_i_boxed_2440_, v_stop_boxed_2441_, v_b_2439_);
lean_dec_ref(v_as_2436_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3___boxed(lean_object* v_x_2443_, lean_object* v_x_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3(v_x_2443_, v_x_2444_);
lean_dec_ref(v_x_2443_);
return v_res_2445_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1(lean_object* v_x_2447_, size_t v_x_2448_, size_t v_x_2449_, lean_object* v_x_2450_){
_start:
{
if (lean_obj_tag(v_x_2447_) == 0)
{
lean_object* v_cs_2451_; lean_object* v___x_2452_; size_t v___x_2453_; lean_object* v_j_2454_; lean_object* v___x_2455_; size_t v___x_2456_; size_t v___x_2457_; size_t v___x_2458_; size_t v___x_2459_; size_t v___x_2460_; size_t v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; uint8_t v___x_2466_; 
v_cs_2451_ = lean_ctor_get(v_x_2447_, 0);
v___x_2452_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___closed__0);
v___x_2453_ = lean_usize_shift_right(v_x_2448_, v_x_2449_);
v_j_2454_ = lean_usize_to_nat(v___x_2453_);
v___x_2455_ = lean_array_get_borrowed(v___x_2452_, v_cs_2451_, v_j_2454_);
v___x_2456_ = ((size_t)1ULL);
v___x_2457_ = lean_usize_shift_left(v___x_2456_, v_x_2449_);
v___x_2458_ = lean_usize_sub(v___x_2457_, v___x_2456_);
v___x_2459_ = lean_usize_land(v_x_2448_, v___x_2458_);
v___x_2460_ = ((size_t)5ULL);
v___x_2461_ = lean_usize_sub(v_x_2449_, v___x_2460_);
v___x_2462_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1(v___x_2455_, v___x_2459_, v___x_2461_, v_x_2450_);
v___x_2463_ = lean_unsigned_to_nat(1u);
v___x_2464_ = lean_nat_add(v_j_2454_, v___x_2463_);
lean_dec(v_j_2454_);
v___x_2465_ = lean_array_get_size(v_cs_2451_);
v___x_2466_ = lean_nat_dec_lt(v___x_2464_, v___x_2465_);
if (v___x_2466_ == 0)
{
lean_dec(v___x_2464_);
return v___x_2462_;
}
else
{
size_t v___x_2467_; size_t v___x_2468_; lean_object* v___x_2469_; 
v___x_2467_ = lean_usize_of_nat(v___x_2464_);
lean_dec(v___x_2464_);
v___x_2468_ = lean_usize_of_nat(v___x_2465_);
v___x_2469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2(v_cs_2451_, v___x_2467_, v___x_2468_, v___x_2462_);
return v___x_2469_;
}
}
else
{
lean_object* v_vs_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; uint8_t v___x_2473_; 
v_vs_2470_ = lean_ctor_get(v_x_2447_, 0);
v___x_2471_ = lean_usize_to_nat(v_x_2448_);
v___x_2472_ = lean_array_get_size(v_vs_2470_);
v___x_2473_ = lean_nat_dec_lt(v___x_2471_, v___x_2472_);
if (v___x_2473_ == 0)
{
lean_dec(v___x_2471_);
return v_x_2450_;
}
else
{
size_t v___x_2474_; size_t v___x_2475_; lean_object* v___x_2476_; 
v___x_2474_ = lean_usize_of_nat(v___x_2471_);
lean_dec(v___x_2471_);
v___x_2475_ = lean_usize_of_nat(v___x_2472_);
v___x_2476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_vs_2470_, v___x_2474_, v___x_2475_, v_x_2450_);
return v___x_2476_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___boxed(lean_object* v_x_2477_, lean_object* v_x_2478_, lean_object* v_x_2479_, lean_object* v_x_2480_){
_start:
{
size_t v_x_1498__boxed_2481_; size_t v_x_1499__boxed_2482_; lean_object* v_res_2483_; 
v_x_1498__boxed_2481_ = lean_unbox_usize(v_x_2478_);
lean_dec(v_x_2478_);
v_x_1499__boxed_2482_ = lean_unbox_usize(v_x_2479_);
lean_dec(v_x_2479_);
v_res_2483_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1(v_x_2477_, v_x_1498__boxed_2481_, v_x_1499__boxed_2482_, v_x_2480_);
lean_dec_ref(v_x_2477_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0(lean_object* v_t_2484_, lean_object* v_init_2485_, lean_object* v_start_2486_){
_start:
{
lean_object* v___x_2487_; uint8_t v___x_2488_; 
v___x_2487_ = lean_unsigned_to_nat(0u);
v___x_2488_ = lean_nat_dec_eq(v_start_2486_, v___x_2487_);
if (v___x_2488_ == 0)
{
lean_object* v_root_2489_; lean_object* v_tail_2490_; size_t v_shift_2491_; lean_object* v_tailOff_2492_; uint8_t v___x_2493_; 
v_root_2489_ = lean_ctor_get(v_t_2484_, 0);
v_tail_2490_ = lean_ctor_get(v_t_2484_, 1);
v_shift_2491_ = lean_ctor_get_usize(v_t_2484_, 4);
v_tailOff_2492_ = lean_ctor_get(v_t_2484_, 3);
v___x_2493_ = lean_nat_dec_le(v_tailOff_2492_, v_start_2486_);
if (v___x_2493_ == 0)
{
size_t v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; 
v___x_2494_ = lean_usize_of_nat(v_start_2486_);
v___x_2495_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1(v_root_2489_, v___x_2494_, v_shift_2491_, v_init_2485_);
v___x_2496_ = lean_array_get_size(v_tail_2490_);
v___x_2497_ = lean_nat_dec_lt(v___x_2487_, v___x_2496_);
if (v___x_2497_ == 0)
{
return v___x_2495_;
}
else
{
size_t v___x_2498_; size_t v___x_2499_; lean_object* v___x_2500_; 
v___x_2498_ = ((size_t)0ULL);
v___x_2499_ = lean_usize_of_nat(v___x_2496_);
v___x_2500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_tail_2490_, v___x_2498_, v___x_2499_, v___x_2495_);
return v___x_2500_;
}
}
else
{
lean_object* v___x_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; 
v___x_2501_ = lean_nat_sub(v_start_2486_, v_tailOff_2492_);
v___x_2502_ = lean_array_get_size(v_tail_2490_);
v___x_2503_ = lean_nat_dec_lt(v___x_2501_, v___x_2502_);
if (v___x_2503_ == 0)
{
lean_dec(v___x_2501_);
return v_init_2485_;
}
else
{
size_t v___x_2504_; size_t v___x_2505_; lean_object* v___x_2506_; 
v___x_2504_ = lean_usize_of_nat(v___x_2501_);
lean_dec(v___x_2501_);
v___x_2505_ = lean_usize_of_nat(v___x_2502_);
v___x_2506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_tail_2490_, v___x_2504_, v___x_2505_, v_init_2485_);
return v___x_2506_;
}
}
}
else
{
lean_object* v_root_2507_; lean_object* v_tail_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; uint8_t v___x_2511_; 
v_root_2507_ = lean_ctor_get(v_t_2484_, 0);
v_tail_2508_ = lean_ctor_get(v_t_2484_, 1);
v___x_2509_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3(v_root_2507_, v_init_2485_);
v___x_2510_ = lean_array_get_size(v_tail_2508_);
v___x_2511_ = lean_nat_dec_lt(v___x_2487_, v___x_2510_);
if (v___x_2511_ == 0)
{
return v___x_2509_;
}
else
{
size_t v___x_2512_; size_t v___x_2513_; lean_object* v___x_2514_; 
v___x_2512_ = ((size_t)0ULL);
v___x_2513_ = lean_usize_of_nat(v___x_2510_);
v___x_2514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_tail_2508_, v___x_2512_, v___x_2513_, v___x_2509_);
return v___x_2514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0___boxed(lean_object* v_t_2515_, lean_object* v_init_2516_, lean_object* v_start_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0(v_t_2515_, v_init_2516_, v_start_2517_);
lean_dec(v_start_2517_);
lean_dec_ref(v_t_2515_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0(lean_object* v_lctx_2519_, lean_object* v_init_2520_, lean_object* v_start_2521_){
_start:
{
lean_object* v_decls_2522_; lean_object* v___x_2523_; 
v_decls_2522_ = lean_ctor_get(v_lctx_2519_, 1);
v___x_2523_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0(v_decls_2522_, v_init_2520_, v_start_2521_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0___boxed(lean_object* v_lctx_2524_, lean_object* v_init_2525_, lean_object* v_start_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0(v_lctx_2524_, v_init_2525_, v_start_2526_);
lean_dec(v_start_2526_);
lean_dec_ref(v_lctx_2524_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals(lean_object* v_jp_2530_, lean_object* v_jump_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v_proof_2537_; lean_object* v___x_2538_; 
v_proof_2537_ = lean_ctor_get(v_jump_2531_, 0);
lean_inc(v_proof_2537_);
lean_dec_ref(v_jump_2531_);
v___x_2538_ = l_Lean_MVarId_getDecl(v_proof_2537_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2555_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2541_ = v___x_2538_;
v_isShared_2542_ = v_isSharedCheck_2555_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2538_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2555_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v_lctx_2543_; lean_object* v_spec_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2553_; 
v_lctx_2543_ = lean_ctor_get(v_a_2539_, 1);
lean_inc_ref_n(v_lctx_2543_, 2);
lean_dec(v_a_2539_);
v_spec_2544_ = lean_ctor_get(v_jp_2530_, 0);
v___x_2545_ = l_Lean_Expr_fvarId_x21(v_spec_2544_);
v___x_2546_ = l_Lean_LocalContext_get_x21(v_lctx_2543_, v___x_2545_);
v___x_2547_ = l_Lean_LocalDecl_index(v___x_2546_);
lean_dec_ref(v___x_2546_);
v___x_2548_ = lean_unsigned_to_nat(1u);
v___x_2549_ = lean_nat_add(v___x_2547_, v___x_2548_);
lean_dec(v___x_2547_);
v___x_2550_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals___closed__0));
v___x_2551_ = l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0(v_lctx_2543_, v___x_2550_, v___x_2549_);
lean_dec(v___x_2549_);
lean_dec_ref(v_lctx_2543_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2551_);
v___x_2553_ = v___x_2541_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2551_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
v_a_2556_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2538_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2538_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals___boxed(lean_object* v_jp_2564_, lean_object* v_jump_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals(v_jp_2564_, v_jump_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
lean_dec_ref(v_jp_2564_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg(lean_object* v_d_2575_, lean_object* v_00_u03c6_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_){
_start:
{
uint8_t v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = 0;
v___x_2585_ = l_Lean_LocalDecl_value_x3f(v_d_2575_, v___x_2584_);
if (lean_obj_tag(v___x_2585_) == 0)
{
uint8_t v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; uint8_t v___x_2591_; lean_object* v___x_2592_; 
v___x_2586_ = 1;
lean_inc_ref(v_d_2575_);
v___x_2587_ = l_Lean_LocalDecl_toExpr(v_d_2575_);
v___x_2588_ = lean_unsigned_to_nat(1u);
v___x_2589_ = lean_mk_empty_array_with_capacity(v___x_2588_);
v___x_2590_ = lean_array_push(v___x_2589_, v___x_2587_);
v___x_2591_ = 1;
v___x_2592_ = l_Lean_Meta_mkLambdaFVars(v___x_2590_, v_00_u03c6_2576_, v___x_2584_, v___x_2586_, v___x_2584_, v___x_2586_, v___x_2591_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_);
lean_dec_ref(v___x_2590_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2593_);
lean_dec_ref_known(v___x_2592_, 1);
v___x_2594_ = l_Lean_LocalDecl_type(v_d_2575_);
lean_dec_ref(v_d_2575_);
lean_inc_ref(v___x_2594_);
v___x_2595_ = l_Lean_Meta_Sym_inferType(v___x_2594_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2630_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2598_ = v___x_2595_;
v_isShared_2599_ = v_isSharedCheck_2630_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2595_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2630_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
uint8_t v___x_2623_; 
v___x_2623_ = l_Lean_Expr_isProp(v_a_2596_);
lean_dec(v_a_2596_);
if (v___x_2623_ == 0)
{
lean_del_object(v___x_2598_);
goto v___jp_2600_;
}
else
{
lean_object* v___x_2624_; uint8_t v___x_2625_; 
v___x_2624_ = l_Lean_Expr_bindingBody_x21(v_a_2593_);
v___x_2625_ = l_Lean_Expr_hasLooseBVars(v___x_2624_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; lean_object* v___x_2628_; 
lean_dec(v_a_2593_);
v___x_2626_ = l_Lean_mkAnd(v___x_2594_, v___x_2624_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2626_);
v___x_2628_ = v___x_2598_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
else
{
lean_dec_ref(v___x_2624_);
lean_del_object(v___x_2598_);
goto v___jp_2600_;
}
}
v___jp_2600_:
{
lean_object* v___x_2601_; 
lean_inc_ref(v___x_2594_);
v___x_2601_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_2594_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2614_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2614_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2614_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2612_; 
v___x_2606_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___closed__1));
v___x_2607_ = lean_box(0);
v___x_2608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2608_, 0, v_a_2602_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = l_Lean_mkConst(v___x_2606_, v___x_2608_);
v___x_2610_ = l_Lean_mkAppB(v___x_2609_, v___x_2594_, v_a_2593_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v___x_2610_);
v___x_2612_ = v___x_2604_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2610_);
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
lean_dec_ref(v___x_2594_);
lean_dec(v_a_2593_);
v_a_2615_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2601_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2601_);
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
else
{
lean_dec_ref(v___x_2594_);
lean_dec(v_a_2593_);
return v___x_2595_;
}
}
else
{
lean_dec_ref(v_d_2575_);
return v___x_2592_;
}
}
else
{
uint8_t v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; uint8_t v___x_2636_; lean_object* v___x_2637_; 
lean_dec_ref_known(v___x_2585_, 1);
v___x_2631_ = 1;
v___x_2632_ = l_Lean_LocalDecl_toExpr(v_d_2575_);
v___x_2633_ = lean_unsigned_to_nat(1u);
v___x_2634_ = lean_mk_empty_array_with_capacity(v___x_2633_);
v___x_2635_ = lean_array_push(v___x_2634_, v___x_2632_);
v___x_2636_ = 1;
v___x_2637_ = l_Lean_Meta_mkLetFVars(v___x_2635_, v_00_u03c6_2576_, v___x_2631_, v___x_2584_, v___x_2636_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_);
lean_dec_ref(v___x_2635_);
return v___x_2637_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___boxed(lean_object* v_d_2638_, lean_object* v_00_u03c6_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg(v_d_2638_, v_00_u03c6_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal(lean_object* v_d_2648_, lean_object* v_00_u03c6_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg(v_d_2648_, v_00_u03c6_2649_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___boxed(lean_object* v_d_2663_, lean_object* v_00_u03c6_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal(v_d_2663_, v_00_u03c6_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
lean_dec(v_a_2673_);
lean_dec_ref(v_a_2672_);
lean_dec(v_a_2671_);
lean_dec_ref(v_a_2670_);
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2668_);
lean_dec(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
return v_res_2677_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__2(void){
_start:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2681_ = lean_box(0);
v___x_2682_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__1));
v___x_2683_ = l_Lean_mkConst(v___x_2682_, v___x_2681_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(lean_object* v_ps_2684_, lean_object* v_lo_2685_, lean_object* v_hi_2686_){
_start:
{
uint8_t v___x_2687_; 
v___x_2687_ = lean_nat_dec_eq(v_hi_2686_, v_lo_2685_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; 
v___x_2688_ = lean_unsigned_to_nat(1u);
v___x_2689_ = lean_nat_add(v_lo_2685_, v___x_2688_);
v___x_2690_ = lean_nat_dec_eq(v_hi_2686_, v___x_2689_);
lean_dec(v___x_2689_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; lean_object* v_mid_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2691_ = lean_nat_add(v_lo_2685_, v_hi_2686_);
v_mid_2692_ = lean_nat_shiftr(v___x_2691_, v___x_2688_);
lean_dec(v___x_2691_);
v___x_2693_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(v_ps_2684_, v_lo_2685_, v_mid_2692_);
v___x_2694_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(v_ps_2684_, v_mid_2692_, v_hi_2686_);
lean_dec(v_mid_2692_);
v___x_2695_ = l_Lean_mkOr(v___x_2693_, v___x_2694_);
return v___x_2695_;
}
else
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2696_ = l_Lean_instInhabitedExpr;
v___x_2697_ = lean_array_get_borrowed(v___x_2696_, v_ps_2684_, v_lo_2685_);
lean_inc(v___x_2697_);
return v___x_2697_;
}
}
else
{
lean_object* v___x_2698_; 
v___x_2698_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__2, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__2_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__2);
return v___x_2698_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___boxed(lean_object* v_ps_2699_, lean_object* v_lo_2700_, lean_object* v_hi_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(v_ps_2699_, v_lo_2700_, v_hi_2701_);
lean_dec(v_hi_2701_);
lean_dec(v_lo_2700_);
lean_dec_ref(v_ps_2699_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(lean_object* v_msg_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_ref_2709_; lean_object* v___x_2710_; lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2719_; 
v_ref_2709_ = lean_ctor_get(v___y_2706_, 2);
v___x_2710_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2_spec__3(v_msg_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2713_ = v___x_2710_;
v_isShared_2714_ = v_isSharedCheck_2719_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2710_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2719_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2715_; lean_object* v___x_2717_; 
lean_inc(v_ref_2709_);
v___x_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2715_, 0, v_ref_2709_);
lean_ctor_set(v___x_2715_, 1, v_a_2711_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set_tag(v___x_2713_, 1);
lean_ctor_set(v___x_2713_, 0, v___x_2715_);
v___x_2717_ = v___x_2713_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v___x_2715_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg___boxed(lean_object* v_msg_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v_msg_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
return v_res_2726_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__1(void){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2728_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__0));
v___x_2729_ = l_Lean_stringToMessageData(v___x_2728_);
return v___x_2729_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__6(void){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2737_ = lean_box(0);
v___x_2738_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__5));
v___x_2739_ = l_Lean_mkConst(v___x_2738_, v___x_2737_);
return v___x_2739_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__9(void){
_start:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2744_ = lean_box(0);
v___x_2745_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__8));
v___x_2746_ = l_Lean_mkConst(v___x_2745_, v___x_2744_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(lean_object* v_00_u03c6_2747_, lean_object* v_i_2748_, lean_object* v_lo_2749_, lean_object* v_hi_2750_, lean_object* v_k_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_){
_start:
{
lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___x_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
v___x_2766_ = lean_unsigned_to_nat(1u);
v___x_2767_ = lean_nat_add(v_lo_2749_, v___x_2766_);
v___x_2768_ = lean_nat_dec_eq(v_hi_2750_, v___x_2767_);
lean_dec(v___x_2767_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; uint8_t v___x_2770_; 
v___x_2769_ = l_Lean_Expr_cleanupAnnotations(v_00_u03c6_2747_);
v___x_2770_ = l_Lean_Expr_isApp(v___x_2769_);
if (v___x_2770_ == 0)
{
lean_dec_ref(v___x_2769_);
lean_dec_ref(v_k_2751_);
v___y_2758_ = v_a_2752_;
v___y_2759_ = v_a_2753_;
v___y_2760_ = v_a_2754_;
v___y_2761_ = v_a_2755_;
goto v___jp_2757_;
}
else
{
lean_object* v___x_2771_; uint8_t v___x_2772_; 
v___x_2771_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2769_);
v___x_2772_ = l_Lean_Expr_isApp(v___x_2771_);
if (v___x_2772_ == 0)
{
lean_dec_ref(v___x_2771_);
lean_dec_ref(v___x_2769_);
lean_dec_ref(v_k_2751_);
v___y_2758_ = v_a_2752_;
v___y_2759_ = v_a_2753_;
v___y_2760_ = v_a_2754_;
v___y_2761_ = v_a_2755_;
goto v___jp_2757_;
}
else
{
lean_object* v___x_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; 
v___x_2773_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2771_);
v___x_2774_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__3));
v___x_2775_ = l_Lean_Expr_isConstOf(v___x_2773_, v___x_2774_);
lean_dec_ref(v___x_2773_);
if (v___x_2775_ == 0)
{
lean_dec_ref(v___x_2771_);
lean_dec_ref(v___x_2769_);
lean_dec_ref(v_k_2751_);
v___y_2758_ = v_a_2752_;
v___y_2759_ = v_a_2753_;
v___y_2760_ = v_a_2754_;
v___y_2761_ = v_a_2755_;
goto v___jp_2757_;
}
else
{
lean_object* v_arg_2776_; lean_object* v_arg_2777_; lean_object* v___x_2778_; lean_object* v_mid_2779_; uint8_t v___x_2780_; 
lean_dec_ref(v_00_u03c6_2747_);
v_arg_2776_ = lean_ctor_get(v___x_2769_, 1);
lean_inc_ref(v_arg_2776_);
lean_dec_ref(v___x_2769_);
v_arg_2777_ = lean_ctor_get(v___x_2771_, 1);
lean_inc_ref(v_arg_2777_);
lean_dec_ref(v___x_2771_);
v___x_2778_ = lean_nat_add(v_lo_2749_, v_hi_2750_);
v_mid_2779_ = lean_nat_shiftr(v___x_2778_, v___x_2766_);
lean_dec(v___x_2778_);
v___x_2780_ = lean_nat_dec_lt(v_i_2748_, v_mid_2779_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2781_; 
lean_inc_ref(v_arg_2776_);
v___x_2781_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(v_arg_2776_, v_i_2748_, v_mid_2779_, v_hi_2750_, v_k_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_);
lean_dec(v_mid_2779_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2791_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2784_ = v___x_2781_;
v_isShared_2785_ = v_isSharedCheck_2791_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2781_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2791_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2789_; 
v___x_2786_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__6, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__6_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__6);
v___x_2787_ = l_Lean_mkApp3(v___x_2786_, v_arg_2777_, v_arg_2776_, v_a_2782_);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v___x_2787_);
v___x_2789_ = v___x_2784_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2787_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
else
{
lean_dec_ref(v_arg_2777_);
lean_dec_ref(v_arg_2776_);
return v___x_2781_;
}
}
else
{
lean_object* v___x_2792_; 
lean_inc_ref(v_arg_2777_);
v___x_2792_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(v_arg_2777_, v_i_2748_, v_lo_2749_, v_mid_2779_, v_k_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_);
lean_dec(v_mid_2779_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2802_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2795_ = v___x_2792_;
v_isShared_2796_ = v_isSharedCheck_2802_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2792_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2802_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2800_; 
v___x_2797_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__9, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__9);
v___x_2798_ = l_Lean_mkApp3(v___x_2797_, v_arg_2777_, v_arg_2776_, v_a_2793_);
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 0, v___x_2798_);
v___x_2800_ = v___x_2795_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2798_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
else
{
lean_dec_ref(v_arg_2777_);
lean_dec_ref(v_arg_2776_);
return v___x_2792_;
}
}
}
}
}
}
else
{
lean_object* v___x_2803_; 
lean_inc(v_a_2755_);
lean_inc_ref(v_a_2754_);
lean_inc(v_a_2753_);
lean_inc_ref(v_a_2752_);
v___x_2803_ = lean_apply_6(v_k_2751_, v_00_u03c6_2747_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, lean_box(0));
return v___x_2803_;
}
v___jp_2757_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2762_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__1, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__1);
v___x_2763_ = l_Lean_indentExpr(v_00_u03c6_2747_);
v___x_2764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2762_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v___x_2764_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
return v___x_2765_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___boxed(lean_object* v_00_u03c6_2804_, lean_object* v_i_2805_, lean_object* v_lo_2806_, lean_object* v_hi_2807_, lean_object* v_k_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(v_00_u03c6_2804_, v_i_2805_, v_lo_2806_, v_hi_2807_, v_k_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2811_);
lean_dec(v_a_2810_);
lean_dec_ref(v_a_2809_);
lean_dec(v_hi_2807_);
lean_dec(v_lo_2806_);
lean_dec(v_i_2805_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0(lean_object* v_00_u03b1_2815_, lean_object* v_msg_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v_msg_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___boxed(lean_object* v_00_u03b1_2823_, lean_object* v_msg_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0(v_00_u03b1_2823_, v_msg_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(lean_object* v_lctx_2831_, lean_object* v_localInsts_2832_, lean_object* v_x_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v___f_2846_; lean_object* v___x_2847_; 
lean_inc(v___y_2840_);
lean_inc_ref(v___y_2839_);
lean_inc(v___y_2838_);
lean_inc_ref(v___y_2837_);
lean_inc(v___y_2836_);
lean_inc(v___y_2835_);
lean_inc_ref(v___y_2834_);
v___f_2846_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_2846_, 0, v_x_2833_);
lean_closure_set(v___f_2846_, 1, v___y_2834_);
lean_closure_set(v___f_2846_, 2, v___y_2835_);
lean_closure_set(v___f_2846_, 3, v___y_2836_);
lean_closure_set(v___f_2846_, 4, v___y_2837_);
lean_closure_set(v___f_2846_, 5, v___y_2838_);
lean_closure_set(v___f_2846_, 6, v___y_2839_);
lean_closure_set(v___f_2846_, 7, v___y_2840_);
v___x_2847_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2831_, v_localInsts_2832_, v___f_2846_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_2847_) == 0)
{
return v___x_2847_;
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2847_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2847_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg___boxed(lean_object* v_lctx_2856_, lean_object* v_localInsts_2857_, lean_object* v_x_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(v_lctx_2856_, v_localInsts_2857_, v_x_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6(lean_object* v_00_u03b1_2872_, lean_object* v_lctx_2873_, lean_object* v_localInsts_2874_, lean_object* v_x_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(v_lctx_2873_, v_localInsts_2874_, v_x_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___boxed(lean_object* v_00_u03b1_2889_, lean_object* v_lctx_2890_, lean_object* v_localInsts_2891_, lean_object* v_x_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6(v_00_u03b1_2889_, v_lctx_2890_, v_localInsts_2891_, v_x_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg(lean_object* v_a_2906_, lean_object* v_x_2907_){
_start:
{
if (lean_obj_tag(v_x_2907_) == 0)
{
lean_object* v___x_2908_; 
v___x_2908_ = lean_box(0);
return v___x_2908_;
}
else
{
lean_object* v_key_2909_; lean_object* v_value_2910_; lean_object* v_tail_2911_; uint8_t v___x_2912_; 
v_key_2909_ = lean_ctor_get(v_x_2907_, 0);
v_value_2910_ = lean_ctor_get(v_x_2907_, 1);
v_tail_2911_ = lean_ctor_get(v_x_2907_, 2);
v___x_2912_ = l_Lean_instBEqFVarId_beq(v_key_2909_, v_a_2906_);
if (v___x_2912_ == 0)
{
v_x_2907_ = v_tail_2911_;
goto _start;
}
else
{
lean_object* v___x_2914_; 
lean_inc(v_value_2910_);
v___x_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2914_, 0, v_value_2910_);
return v___x_2914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg___boxed(lean_object* v_a_2915_, lean_object* v_x_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg(v_a_2915_, v_x_2916_);
lean_dec(v_x_2916_);
lean_dec(v_a_2915_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg(lean_object* v_m_2918_, lean_object* v_a_2919_){
_start:
{
lean_object* v_buckets_2920_; lean_object* v___x_2921_; uint64_t v___x_2922_; uint64_t v___x_2923_; uint64_t v___x_2924_; uint64_t v_fold_2925_; uint64_t v___x_2926_; uint64_t v___x_2927_; uint64_t v___x_2928_; size_t v___x_2929_; size_t v___x_2930_; size_t v___x_2931_; size_t v___x_2932_; size_t v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v_buckets_2920_ = lean_ctor_get(v_m_2918_, 1);
v___x_2921_ = lean_array_get_size(v_buckets_2920_);
v___x_2922_ = l_Lean_instHashableFVarId_hash(v_a_2919_);
v___x_2923_ = 32ULL;
v___x_2924_ = lean_uint64_shift_right(v___x_2922_, v___x_2923_);
v_fold_2925_ = lean_uint64_xor(v___x_2922_, v___x_2924_);
v___x_2926_ = 16ULL;
v___x_2927_ = lean_uint64_shift_right(v_fold_2925_, v___x_2926_);
v___x_2928_ = lean_uint64_xor(v_fold_2925_, v___x_2927_);
v___x_2929_ = lean_uint64_to_usize(v___x_2928_);
v___x_2930_ = lean_usize_of_nat(v___x_2921_);
v___x_2931_ = ((size_t)1ULL);
v___x_2932_ = lean_usize_sub(v___x_2930_, v___x_2931_);
v___x_2933_ = lean_usize_land(v___x_2929_, v___x_2932_);
v___x_2934_ = lean_array_uget_borrowed(v_buckets_2920_, v___x_2933_);
v___x_2935_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg(v_a_2919_, v___x_2934_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg___boxed(lean_object* v_m_2936_, lean_object* v_a_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg(v_m_2936_, v_a_2937_);
lean_dec(v_a_2937_);
lean_dec_ref(v_m_2936_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4___redArg(lean_object* v_a_2939_, lean_object* v_b_2940_, lean_object* v_x_2941_){
_start:
{
if (lean_obj_tag(v_x_2941_) == 0)
{
lean_dec(v_b_2940_);
lean_dec(v_a_2939_);
return v_x_2941_;
}
else
{
lean_object* v_key_2942_; lean_object* v_value_2943_; lean_object* v_tail_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2956_; 
v_key_2942_ = lean_ctor_get(v_x_2941_, 0);
v_value_2943_ = lean_ctor_get(v_x_2941_, 1);
v_tail_2944_ = lean_ctor_get(v_x_2941_, 2);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_x_2941_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2946_ = v_x_2941_;
v_isShared_2947_ = v_isSharedCheck_2956_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_tail_2944_);
lean_inc(v_value_2943_);
lean_inc(v_key_2942_);
lean_dec(v_x_2941_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2956_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
uint8_t v___x_2948_; 
v___x_2948_ = l_Lean_instBEqFVarId_beq(v_key_2942_, v_a_2939_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; lean_object* v___x_2951_; 
v___x_2949_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4___redArg(v_a_2939_, v_b_2940_, v_tail_2944_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 2, v___x_2949_);
v___x_2951_ = v___x_2946_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_key_2942_);
lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_value_2943_);
lean_ctor_set(v_reuseFailAlloc_2952_, 2, v___x_2949_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
else
{
lean_object* v___x_2954_; 
lean_dec(v_value_2943_);
lean_dec(v_key_2942_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 1, v_b_2940_);
lean_ctor_set(v___x_2946_, 0, v_a_2939_);
v___x_2954_ = v___x_2946_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2939_);
lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_b_2940_);
lean_ctor_set(v_reuseFailAlloc_2955_, 2, v_tail_2944_);
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
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg(lean_object* v_a_2957_, lean_object* v_x_2958_){
_start:
{
if (lean_obj_tag(v_x_2958_) == 0)
{
uint8_t v___x_2959_; 
v___x_2959_ = 0;
return v___x_2959_;
}
else
{
lean_object* v_key_2960_; lean_object* v_tail_2961_; uint8_t v___x_2962_; 
v_key_2960_ = lean_ctor_get(v_x_2958_, 0);
v_tail_2961_ = lean_ctor_get(v_x_2958_, 2);
v___x_2962_ = l_Lean_instBEqFVarId_beq(v_key_2960_, v_a_2957_);
if (v___x_2962_ == 0)
{
v_x_2958_ = v_tail_2961_;
goto _start;
}
else
{
return v___x_2962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg___boxed(lean_object* v_a_2964_, lean_object* v_x_2965_){
_start:
{
uint8_t v_res_2966_; lean_object* v_r_2967_; 
v_res_2966_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg(v_a_2964_, v_x_2965_);
lean_dec(v_x_2965_);
lean_dec(v_a_2964_);
v_r_2967_ = lean_box(v_res_2966_);
return v_r_2967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5_spec__11___redArg(lean_object* v_x_2968_, lean_object* v_x_2969_){
_start:
{
if (lean_obj_tag(v_x_2969_) == 0)
{
return v_x_2968_;
}
else
{
lean_object* v_key_2970_; lean_object* v_value_2971_; lean_object* v_tail_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2995_; 
v_key_2970_ = lean_ctor_get(v_x_2969_, 0);
v_value_2971_ = lean_ctor_get(v_x_2969_, 1);
v_tail_2972_ = lean_ctor_get(v_x_2969_, 2);
v_isSharedCheck_2995_ = !lean_is_exclusive(v_x_2969_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2974_ = v_x_2969_;
v_isShared_2975_ = v_isSharedCheck_2995_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_tail_2972_);
lean_inc(v_value_2971_);
lean_inc(v_key_2970_);
lean_dec(v_x_2969_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2995_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; uint64_t v___x_2977_; uint64_t v___x_2978_; uint64_t v___x_2979_; uint64_t v_fold_2980_; uint64_t v___x_2981_; uint64_t v___x_2982_; uint64_t v___x_2983_; size_t v___x_2984_; size_t v___x_2985_; size_t v___x_2986_; size_t v___x_2987_; size_t v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2991_; 
v___x_2976_ = lean_array_get_size(v_x_2968_);
v___x_2977_ = l_Lean_instHashableFVarId_hash(v_key_2970_);
v___x_2978_ = 32ULL;
v___x_2979_ = lean_uint64_shift_right(v___x_2977_, v___x_2978_);
v_fold_2980_ = lean_uint64_xor(v___x_2977_, v___x_2979_);
v___x_2981_ = 16ULL;
v___x_2982_ = lean_uint64_shift_right(v_fold_2980_, v___x_2981_);
v___x_2983_ = lean_uint64_xor(v_fold_2980_, v___x_2982_);
v___x_2984_ = lean_uint64_to_usize(v___x_2983_);
v___x_2985_ = lean_usize_of_nat(v___x_2976_);
v___x_2986_ = ((size_t)1ULL);
v___x_2987_ = lean_usize_sub(v___x_2985_, v___x_2986_);
v___x_2988_ = lean_usize_land(v___x_2984_, v___x_2987_);
v___x_2989_ = lean_array_uget_borrowed(v_x_2968_, v___x_2988_);
lean_inc(v___x_2989_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 2, v___x_2989_);
v___x_2991_ = v___x_2974_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_key_2970_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v_value_2971_);
lean_ctor_set(v_reuseFailAlloc_2994_, 2, v___x_2989_);
v___x_2991_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
lean_object* v___x_2992_; 
v___x_2992_ = lean_array_uset(v_x_2968_, v___x_2988_, v___x_2991_);
v_x_2968_ = v___x_2992_;
v_x_2969_ = v_tail_2972_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5___redArg(lean_object* v_i_2996_, lean_object* v_source_2997_, lean_object* v_target_2998_){
_start:
{
lean_object* v___x_2999_; uint8_t v___x_3000_; 
v___x_2999_ = lean_array_get_size(v_source_2997_);
v___x_3000_ = lean_nat_dec_lt(v_i_2996_, v___x_2999_);
if (v___x_3000_ == 0)
{
lean_dec_ref(v_source_2997_);
lean_dec(v_i_2996_);
return v_target_2998_;
}
else
{
lean_object* v_es_3001_; lean_object* v___x_3002_; lean_object* v_source_3003_; lean_object* v_target_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_es_3001_ = lean_array_fget(v_source_2997_, v_i_2996_);
v___x_3002_ = lean_box(0);
v_source_3003_ = lean_array_fset(v_source_2997_, v_i_2996_, v___x_3002_);
v_target_3004_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5_spec__11___redArg(v_target_2998_, v_es_3001_);
v___x_3005_ = lean_unsigned_to_nat(1u);
v___x_3006_ = lean_nat_add(v_i_2996_, v___x_3005_);
lean_dec(v_i_2996_);
v_i_2996_ = v___x_3006_;
v_source_2997_ = v_source_3003_;
v_target_2998_ = v_target_3004_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3___redArg(lean_object* v_data_3008_){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v_nbuckets_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3009_ = lean_array_get_size(v_data_3008_);
v___x_3010_ = lean_unsigned_to_nat(2u);
v_nbuckets_3011_ = lean_nat_mul(v___x_3009_, v___x_3010_);
v___x_3012_ = lean_unsigned_to_nat(0u);
v___x_3013_ = lean_box(0);
v___x_3014_ = lean_mk_array(v_nbuckets_3011_, v___x_3013_);
v___x_3015_ = lean_array_propagate_mark(v_data_3008_, v___x_3014_);
v___x_3016_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5___redArg(v___x_3012_, v_data_3008_, v___x_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1___redArg(lean_object* v_m_3017_, lean_object* v_a_3018_, lean_object* v_b_3019_){
_start:
{
lean_object* v_size_3020_; lean_object* v_buckets_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3064_; 
v_size_3020_ = lean_ctor_get(v_m_3017_, 0);
v_buckets_3021_ = lean_ctor_get(v_m_3017_, 1);
v_isSharedCheck_3064_ = !lean_is_exclusive(v_m_3017_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3023_ = v_m_3017_;
v_isShared_3024_ = v_isSharedCheck_3064_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_buckets_3021_);
lean_inc(v_size_3020_);
lean_dec(v_m_3017_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3064_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3025_; uint64_t v___x_3026_; uint64_t v___x_3027_; uint64_t v___x_3028_; uint64_t v_fold_3029_; uint64_t v___x_3030_; uint64_t v___x_3031_; uint64_t v___x_3032_; size_t v___x_3033_; size_t v___x_3034_; size_t v___x_3035_; size_t v___x_3036_; size_t v___x_3037_; lean_object* v_bkt_3038_; uint8_t v___x_3039_; 
v___x_3025_ = lean_array_get_size(v_buckets_3021_);
v___x_3026_ = l_Lean_instHashableFVarId_hash(v_a_3018_);
v___x_3027_ = 32ULL;
v___x_3028_ = lean_uint64_shift_right(v___x_3026_, v___x_3027_);
v_fold_3029_ = lean_uint64_xor(v___x_3026_, v___x_3028_);
v___x_3030_ = 16ULL;
v___x_3031_ = lean_uint64_shift_right(v_fold_3029_, v___x_3030_);
v___x_3032_ = lean_uint64_xor(v_fold_3029_, v___x_3031_);
v___x_3033_ = lean_uint64_to_usize(v___x_3032_);
v___x_3034_ = lean_usize_of_nat(v___x_3025_);
v___x_3035_ = ((size_t)1ULL);
v___x_3036_ = lean_usize_sub(v___x_3034_, v___x_3035_);
v___x_3037_ = lean_usize_land(v___x_3033_, v___x_3036_);
v_bkt_3038_ = lean_array_uget_borrowed(v_buckets_3021_, v___x_3037_);
v___x_3039_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg(v_a_3018_, v_bkt_3038_);
if (v___x_3039_ == 0)
{
lean_object* v___x_3040_; lean_object* v_size_x27_3041_; lean_object* v___x_3042_; lean_object* v_buckets_x27_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; uint8_t v___x_3049_; 
v___x_3040_ = lean_unsigned_to_nat(1u);
v_size_x27_3041_ = lean_nat_add(v_size_3020_, v___x_3040_);
lean_dec(v_size_3020_);
lean_inc(v_bkt_3038_);
v___x_3042_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3042_, 0, v_a_3018_);
lean_ctor_set(v___x_3042_, 1, v_b_3019_);
lean_ctor_set(v___x_3042_, 2, v_bkt_3038_);
v_buckets_x27_3043_ = lean_array_uset(v_buckets_3021_, v___x_3037_, v___x_3042_);
v___x_3044_ = lean_unsigned_to_nat(4u);
v___x_3045_ = lean_nat_mul(v_size_x27_3041_, v___x_3044_);
v___x_3046_ = lean_unsigned_to_nat(3u);
v___x_3047_ = lean_nat_div(v___x_3045_, v___x_3046_);
lean_dec(v___x_3045_);
v___x_3048_ = lean_array_get_size(v_buckets_x27_3043_);
v___x_3049_ = lean_nat_dec_le(v___x_3047_, v___x_3048_);
lean_dec(v___x_3047_);
if (v___x_3049_ == 0)
{
lean_object* v_val_3050_; lean_object* v___x_3052_; 
v_val_3050_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3___redArg(v_buckets_x27_3043_);
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 1, v_val_3050_);
lean_ctor_set(v___x_3023_, 0, v_size_x27_3041_);
v___x_3052_ = v___x_3023_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_size_x27_3041_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v_val_3050_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
else
{
lean_object* v___x_3055_; 
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 1, v_buckets_x27_3043_);
lean_ctor_set(v___x_3023_, 0, v_size_x27_3041_);
v___x_3055_ = v___x_3023_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_size_x27_3041_);
lean_ctor_set(v_reuseFailAlloc_3056_, 1, v_buckets_x27_3043_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
else
{
lean_object* v___x_3057_; lean_object* v_buckets_x27_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3062_; 
lean_inc(v_bkt_3038_);
v___x_3057_ = lean_box(0);
v_buckets_x27_3058_ = lean_array_uset(v_buckets_3021_, v___x_3037_, v___x_3057_);
v___x_3059_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4___redArg(v_a_3018_, v_b_3019_, v_bkt_3038_);
v___x_3060_ = lean_array_uset(v_buckets_x27_3058_, v___x_3037_, v___x_3059_);
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 1, v___x_3060_);
v___x_3062_ = v___x_3023_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_size_3020_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v___x_3060_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg(lean_object* v_jumps_3065_, lean_object* v_i_3066_, lean_object* v_range_3067_, lean_object* v_b_3068_, lean_object* v_i_3069_){
_start:
{
lean_object* v_stop_3071_; lean_object* v_step_3072_; lean_object* v_a_3074_; lean_object* v_groups_3078_; lean_object* v_byLocal_3079_; uint8_t v___x_3085_; 
v_stop_3071_ = lean_ctor_get(v_range_3067_, 1);
v_step_3072_ = lean_ctor_get(v_range_3067_, 2);
v___x_3085_ = lean_nat_dec_lt(v_i_3069_, v_stop_3071_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; 
lean_dec(v_i_3069_);
v___x_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3086_, 0, v_b_3068_);
return v___x_3086_;
}
else
{
lean_object* v_fst_3087_; lean_object* v_snd_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3114_; 
v_fst_3087_ = lean_ctor_get(v_b_3068_, 0);
v_snd_3088_ = lean_ctor_get(v_b_3068_, 1);
v_isSharedCheck_3114_ = !lean_is_exclusive(v_b_3068_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3090_ = v_b_3068_;
v_isShared_3091_ = v_isSharedCheck_3114_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_snd_3088_);
lean_inc(v_fst_3087_);
lean_dec(v_b_3068_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3114_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___y_3093_; lean_object* v___x_3097_; lean_object* v_snd_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3097_ = lean_array_fget_borrowed(v_jumps_3065_, v_i_3069_);
v_snd_3098_ = lean_ctor_get(v___x_3097_, 1);
v___x_3099_ = lean_array_get_size(v_snd_3098_);
v___x_3100_ = lean_nat_dec_lt(v_i_3066_, v___x_3099_);
if (v___x_3100_ == 0)
{
lean_del_object(v___x_3090_);
v_groups_3078_ = v_fst_3087_;
v_byLocal_3079_ = v_snd_3088_;
goto v___jp_3077_;
}
else
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3101_ = lean_array_fget_borrowed(v_snd_3098_, v_i_3066_);
v___x_3102_ = l_Lean_LocalDecl_fvarId(v___x_3101_);
v___x_3103_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg(v_snd_3088_, v___x_3102_);
if (lean_obj_tag(v___x_3103_) == 1)
{
lean_object* v_val_3104_; lean_object* v___x_3105_; uint8_t v___x_3106_; 
lean_dec(v___x_3102_);
v_val_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_val_3104_);
lean_dec_ref_known(v___x_3103_, 1);
v___x_3105_ = lean_array_get_size(v_fst_3087_);
v___x_3106_ = lean_nat_dec_lt(v_val_3104_, v___x_3105_);
if (v___x_3106_ == 0)
{
lean_dec(v_val_3104_);
v___y_3093_ = v_fst_3087_;
goto v___jp_3092_;
}
else
{
lean_object* v_v_3107_; lean_object* v___x_3108_; lean_object* v_xs_x27_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v_v_3107_ = lean_array_fget(v_fst_3087_, v_val_3104_);
v___x_3108_ = lean_box(0);
v_xs_x27_3109_ = lean_array_fset(v_fst_3087_, v_val_3104_, v___x_3108_);
lean_inc(v_i_3069_);
v___x_3110_ = lean_array_push(v_v_3107_, v_i_3069_);
v___x_3111_ = lean_array_fset(v_xs_x27_3109_, v_val_3104_, v___x_3110_);
lean_dec(v_val_3104_);
v___y_3093_ = v___x_3111_;
goto v___jp_3092_;
}
}
else
{
lean_object* v___x_3112_; lean_object* v_byLocal_3113_; 
lean_dec(v___x_3103_);
lean_del_object(v___x_3090_);
v___x_3112_ = lean_array_get_size(v_fst_3087_);
v_byLocal_3113_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1___redArg(v_snd_3088_, v___x_3102_, v___x_3112_);
v_groups_3078_ = v_fst_3087_;
v_byLocal_3079_ = v_byLocal_3113_;
goto v___jp_3077_;
}
}
v___jp_3092_:
{
lean_object* v___x_3095_; 
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 0, v___y_3093_);
v___x_3095_ = v___x_3090_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___y_3093_);
lean_ctor_set(v_reuseFailAlloc_3096_, 1, v_snd_3088_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
v_a_3074_ = v___x_3095_;
goto v___jp_3073_;
}
}
}
}
v___jp_3073_:
{
lean_object* v___x_3075_; 
v___x_3075_ = lean_nat_add(v_i_3069_, v_step_3072_);
lean_dec(v_i_3069_);
v_b_3068_ = v_a_3074_;
v_i_3069_ = v___x_3075_;
goto _start;
}
v___jp_3077_:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v_groups_3083_; lean_object* v___x_3084_; 
v___x_3080_ = lean_unsigned_to_nat(1u);
v___x_3081_ = lean_mk_empty_array_with_capacity(v___x_3080_);
lean_inc(v_i_3069_);
v___x_3082_ = lean_array_push(v___x_3081_, v_i_3069_);
v_groups_3083_ = lean_array_push(v_groups_3078_, v___x_3082_);
v___x_3084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3084_, 0, v_groups_3083_);
lean_ctor_set(v___x_3084_, 1, v_byLocal_3079_);
v_a_3074_ = v___x_3084_;
goto v___jp_3073_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg___boxed(lean_object* v_jumps_3115_, lean_object* v_i_3116_, lean_object* v_range_3117_, lean_object* v_b_3118_, lean_object* v_i_3119_, lean_object* v___y_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg(v_jumps_3115_, v_i_3116_, v_range_3117_, v_b_3118_, v_i_3119_);
lean_dec_ref(v_range_3117_);
lean_dec(v_i_3116_);
lean_dec_ref(v_jumps_3115_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(lean_object* v_xs_3128_, lean_object* v_fst_3129_, lean_object* v_range_3130_, lean_object* v_b_3131_, lean_object* v_i_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v_stop_3140_; lean_object* v_step_3141_; lean_object* v_a_3143_; uint8_t v___x_3146_; 
v_stop_3140_ = lean_ctor_get(v_range_3130_, 1);
v_step_3141_ = lean_ctor_get(v_range_3130_, 2);
v___x_3146_ = lean_nat_dec_lt(v_i_3132_, v_stop_3140_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; 
lean_dec(v_i_3132_);
v___x_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3147_, 0, v_b_3131_);
return v___x_3147_;
}
else
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3148_ = l_Lean_instInhabitedExpr;
v___x_3149_ = lean_array_fget_borrowed(v_xs_3128_, v_i_3132_);
lean_inc(v___x_3149_);
v___x_3150_ = l_Lean_Meta_Sym_inferType(v___x_3149_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3151_; lean_object* v___x_3152_; uint8_t v___x_3153_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_a_3151_);
lean_dec_ref_known(v___x_3150_, 1);
v___x_3152_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__1));
v___x_3153_ = l_Lean_Expr_isConstOf(v_a_3151_, v___x_3152_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3154_; 
lean_inc(v_a_3151_);
v___x_3154_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_3151_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v_args_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3154_, 1);
v_args_3156_ = lean_ctor_get(v_fst_3129_, 1);
v___x_3157_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__3));
v___x_3158_ = lean_box(0);
v___x_3159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3159_, 0, v_a_3155_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = l_Lean_mkConst(v___x_3157_, v___x_3159_);
v___x_3161_ = lean_array_get_borrowed(v___x_3148_, v_args_3156_, v_i_3132_);
lean_inc(v___x_3161_);
lean_inc(v___x_3149_);
v___x_3162_ = l_Lean_mkApp3(v___x_3160_, v_a_3151_, v___x_3149_, v___x_3161_);
v___x_3163_ = lean_array_push(v_b_3131_, v___x_3162_);
v_a_3143_ = v___x_3163_;
goto v___jp_3142_;
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec(v_a_3151_);
lean_dec(v_i_3132_);
lean_dec_ref(v_b_3131_);
v_a_3164_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3154_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3154_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
else
{
lean_dec(v_a_3151_);
v_a_3143_ = v_b_3131_;
goto v___jp_3142_;
}
}
else
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
lean_dec(v_i_3132_);
lean_dec_ref(v_b_3131_);
v_a_3172_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3150_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3150_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
v___jp_3142_:
{
lean_object* v___x_3144_; 
v___x_3144_ = lean_nat_add(v_i_3132_, v_step_3141_);
lean_dec(v_i_3132_);
v_b_3131_ = v_a_3143_;
v_i_3132_ = v___x_3144_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___boxed(lean_object* v_xs_3180_, lean_object* v_fst_3181_, lean_object* v_range_3182_, lean_object* v_b_3183_, lean_object* v_i_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(v_xs_3180_, v_fst_3181_, v_range_3182_, v_b_3183_, v_i_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec_ref(v_range_3182_);
lean_dec_ref(v_fst_3181_);
lean_dec_ref(v_xs_3180_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(lean_object* v_g_3193_, lean_object* v___x_3194_, lean_object* v_as_3195_, size_t v_sz_3196_, size_t v_i_3197_, lean_object* v_b_3198_){
_start:
{
uint8_t v___x_3200_; 
v___x_3200_ = lean_usize_dec_lt(v_i_3197_, v_sz_3196_);
if (v___x_3200_ == 0)
{
lean_object* v___x_3201_; 
lean_dec(v___x_3194_);
lean_dec(v_g_3193_);
v___x_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3201_, 0, v_b_3198_);
return v___x_3201_;
}
else
{
lean_object* v_a_3202_; lean_object* v_fst_3203_; lean_object* v_snd_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3216_; 
v_a_3202_ = lean_array_uget(v_as_3195_, v_i_3197_);
v_fst_3203_ = lean_ctor_get(v_a_3202_, 0);
v_snd_3204_ = lean_ctor_get(v_a_3202_, 1);
v_isSharedCheck_3216_ = !lean_is_exclusive(v_a_3202_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3206_ = v_a_3202_;
v_isShared_3207_ = v_isSharedCheck_3216_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_snd_3204_);
lean_inc(v_fst_3203_);
lean_dec(v_a_3202_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3216_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
lean_inc(v___x_3194_);
lean_inc(v_g_3193_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 1, v___x_3194_);
lean_ctor_set(v___x_3206_, 0, v_g_3193_);
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_g_3193_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v___x_3194_);
v___x_3209_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; size_t v___x_3212_; size_t v___x_3213_; 
v___x_3210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
lean_ctor_set(v___x_3210_, 1, v_snd_3204_);
v___x_3211_ = lean_array_set(v_b_3198_, v_fst_3203_, v___x_3210_);
lean_dec(v_fst_3203_);
v___x_3212_ = ((size_t)1ULL);
v___x_3213_ = lean_usize_add(v_i_3197_, v___x_3212_);
v_i_3197_ = v___x_3213_;
v_b_3198_ = v___x_3211_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg___boxed(lean_object* v_g_3217_, lean_object* v___x_3218_, lean_object* v_as_3219_, lean_object* v_sz_3220_, lean_object* v_i_3221_, lean_object* v_b_3222_, lean_object* v___y_3223_){
_start:
{
size_t v_sz_boxed_3224_; size_t v_i_boxed_3225_; lean_object* v_res_3226_; 
v_sz_boxed_3224_ = lean_unbox_usize(v_sz_3220_);
lean_dec(v_sz_3220_);
v_i_boxed_3225_ = lean_unbox_usize(v_i_3221_);
lean_dec(v_i_3221_);
v_res_3226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(v_g_3217_, v___x_3218_, v_as_3219_, v_sz_boxed_3224_, v_i_boxed_3225_, v_b_3222_);
lean_dec_ref(v_as_3219_);
return v_res_3226_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3227_; 
v___x_3227_ = l_Array_instInhabited___redArg();
return v___x_3227_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1(void){
_start:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3228_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__0);
v___x_3229_ = l_Lean_Elab_Tactic_VCGen_instInhabitedJump_default;
v___x_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
lean_ctor_set(v___x_3230_, 1, v___x_3228_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5(lean_object* v_jumps_3231_, size_t v_sz_3232_, size_t v_i_3233_, lean_object* v_bs_3234_){
_start:
{
uint8_t v___x_3235_; 
v___x_3235_ = lean_usize_dec_lt(v_i_3233_, v_sz_3232_);
if (v___x_3235_ == 0)
{
return v_bs_3234_;
}
else
{
lean_object* v___x_3236_; lean_object* v_v_3237_; lean_object* v___x_3238_; lean_object* v_bs_x27_3239_; lean_object* v___x_3240_; size_t v___x_3241_; size_t v___x_3242_; lean_object* v___x_3243_; 
v___x_3236_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1);
v_v_3237_ = lean_array_uget(v_bs_3234_, v_i_3233_);
v___x_3238_ = lean_unsigned_to_nat(0u);
v_bs_x27_3239_ = lean_array_uset(v_bs_3234_, v_i_3233_, v___x_3238_);
v___x_3240_ = lean_array_get_borrowed(v___x_3236_, v_jumps_3231_, v_v_3237_);
lean_dec(v_v_3237_);
v___x_3241_ = ((size_t)1ULL);
v___x_3242_ = lean_usize_add(v_i_3233_, v___x_3241_);
lean_inc(v___x_3240_);
v___x_3243_ = lean_array_uset(v_bs_x27_3239_, v_i_3233_, v___x_3240_);
v_i_3233_ = v___x_3242_;
v_bs_3234_ = v___x_3243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___boxed(lean_object* v_jumps_3245_, lean_object* v_sz_3246_, lean_object* v_i_3247_, lean_object* v_bs_3248_){
_start:
{
size_t v_sz_boxed_3249_; size_t v_i_boxed_3250_; lean_object* v_res_3251_; 
v_sz_boxed_3249_ = lean_unbox_usize(v_sz_3246_);
lean_dec(v_sz_3246_);
v_i_boxed_3250_ = lean_unbox_usize(v_i_3247_);
lean_dec(v_i_3247_);
v_res_3251_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5(v_jumps_3245_, v_sz_boxed_3249_, v_i_boxed_3250_, v_bs_3248_);
lean_dec_ref(v_jumps_3245_);
return v_res_3251_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__1(void){
_start:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3254_ = lean_box(0);
v___x_3255_ = lean_unsigned_to_nat(16u);
v___x_3256_ = lean_mk_array(v___x_3255_, v___x_3254_);
return v___x_3256_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__2(void){
_start:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v_byLocal_3259_; 
v___x_3257_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__1, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__1);
v___x_3258_ = lean_unsigned_to_nat(0u);
v_byLocal_3259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byLocal_3259_, 0, v___x_3258_);
lean_ctor_set(v_byLocal_3259_, 1, v___x_3257_);
return v_byLocal_3259_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__3(void){
_start:
{
lean_object* v_byLocal_3260_; lean_object* v_groups_3261_; lean_object* v___x_3262_; 
v_byLocal_3260_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__2, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__2_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__2);
v_groups_3261_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__0));
v___x_3262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3262_, 0, v_groups_3261_);
lean_ctor_set(v___x_3262_, 1, v_byLocal_3260_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg(lean_object* v___x_3269_, lean_object* v_jumps_3270_, lean_object* v___x_3271_, lean_object* v_i_3272_, lean_object* v_xs_3273_, lean_object* v_range_3274_, lean_object* v_b_3275_, lean_object* v_i_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v_stop_3289_; lean_object* v_step_3290_; uint8_t v___x_3291_; 
v_stop_3289_ = lean_ctor_get(v_range_3274_, 1);
v_step_3290_ = lean_ctor_get(v_range_3274_, 2);
v___x_3291_ = lean_nat_dec_lt(v_i_3276_, v_stop_3289_);
if (v___x_3291_ == 0)
{
lean_object* v___x_3292_; 
lean_dec(v_i_3276_);
lean_dec(v___x_3271_);
v___x_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3292_, 0, v_b_3275_);
return v___x_3292_;
}
else
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v_fst_3298_; lean_object* v_snd_3299_; lean_object* v_fst_3300_; lean_object* v_snd_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3398_; 
v___x_3293_ = lean_unsigned_to_nat(0u);
v___x_3294_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1);
v___x_3295_ = lean_array_fget_borrowed(v___x_3269_, v_i_3276_);
v___x_3296_ = lean_array_get_borrowed(v___x_3293_, v___x_3295_, v___x_3293_);
v___x_3297_ = lean_array_get_borrowed(v___x_3294_, v_jumps_3270_, v___x_3296_);
v_fst_3298_ = lean_ctor_get(v___x_3297_, 0);
v_snd_3299_ = lean_ctor_get(v___x_3297_, 1);
v_fst_3300_ = lean_ctor_get(v_b_3275_, 0);
v_snd_3301_ = lean_ctor_get(v_b_3275_, 1);
v_isSharedCheck_3398_ = !lean_is_exclusive(v_b_3275_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3303_ = v_b_3275_;
v_isShared_3304_ = v_isSharedCheck_3398_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_snd_3301_);
lean_inc(v_fst_3300_);
lean_dec(v_b_3275_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3398_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v_fst_3306_; lean_object* v_snd_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___x_3338_; lean_object* v___x_3339_; uint8_t v___x_3340_; 
v___x_3338_ = lean_unsigned_to_nat(1u);
v___x_3339_ = lean_array_get_size(v_snd_3299_);
v___x_3340_ = lean_nat_dec_lt(v_i_3272_, v___x_3339_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3341_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__0));
v___x_3342_ = lean_array_get_size(v_xs_3273_);
v___x_3343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3293_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
lean_ctor_set(v___x_3343_, 2, v___x_3338_);
v___x_3344_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(v_xs_3273_, v_fst_3298_, v___x_3343_, v___x_3341_, v___x_3293_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
lean_dec_ref_known(v___x_3343_, 3);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v_a_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_a_3345_);
lean_dec_ref_known(v___x_3344_, 1);
v___x_3346_ = lean_array_to_list(v_a_3345_);
v___x_3347_ = l_Lean_mkAndN(v___x_3346_);
v___x_3348_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__1));
v_fst_3306_ = v___x_3347_;
v_snd_3307_ = v___x_3348_;
v___y_3308_ = v___y_3277_;
v___y_3309_ = v___y_3278_;
v___y_3310_ = v___y_3279_;
v___y_3311_ = v___y_3280_;
v___y_3312_ = v___y_3281_;
v___y_3313_ = v___y_3282_;
v___y_3314_ = v___y_3283_;
v___y_3315_ = v___y_3284_;
v___y_3316_ = v___y_3285_;
v___y_3317_ = v___y_3286_;
v___y_3318_ = v___y_3287_;
goto v___jp_3305_;
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
lean_del_object(v___x_3303_);
lean_dec(v_snd_3301_);
lean_dec(v_fst_3300_);
lean_dec(v_i_3276_);
lean_dec(v___x_3271_);
v_a_3349_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3344_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3344_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
else
{
lean_object* v___x_3357_; size_t v_sz_3358_; size_t v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3357_ = lean_array_fget_borrowed(v_snd_3299_, v_i_3272_);
v_sz_3358_ = lean_array_size(v___x_3295_);
v___x_3359_ = ((size_t)0ULL);
lean_inc(v___x_3295_);
v___x_3360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5(v_jumps_3270_, v_sz_3358_, v___x_3359_, v___x_3295_);
v___x_3361_ = lean_nat_add(v_i_3272_, v___x_3338_);
v___x_3362_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(v_xs_3273_, v___x_3360_, v___x_3361_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
lean_dec(v___x_3361_);
lean_dec_ref(v___x_3360_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v_fst_3364_; lean_object* v_snd_3365_; lean_object* v_proof_3366_; lean_object* v___x_3367_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
v_fst_3364_ = lean_ctor_get(v_a_3363_, 0);
lean_inc(v_fst_3364_);
v_snd_3365_ = lean_ctor_get(v_a_3363_, 1);
lean_inc(v_snd_3365_);
lean_dec(v_a_3363_);
v_proof_3366_ = lean_ctor_get(v_fst_3298_, 0);
lean_inc(v_proof_3366_);
v___x_3367_ = l_Lean_MVarId_getDecl(v_proof_3366_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; lean_object* v_lctx_3369_; lean_object* v_localInstances_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_a_3368_);
lean_dec_ref_known(v___x_3367_, 1);
v_lctx_3369_ = lean_ctor_get(v_a_3368_, 1);
lean_inc_ref(v_lctx_3369_);
v_localInstances_3370_ = lean_ctor_get(v_a_3368_, 4);
lean_inc_ref(v_localInstances_3370_);
lean_dec(v_a_3368_);
lean_inc(v___x_3357_);
v___x_3371_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___boxed), 14, 2);
lean_closure_set(v___x_3371_, 0, v___x_3357_);
lean_closure_set(v___x_3371_, 1, v_fst_3364_);
v___x_3372_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(v_lctx_3369_, v_localInstances_3370_, v___x_3371_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc(v_a_3373_);
lean_dec_ref_known(v___x_3372_, 1);
v_fst_3306_ = v_a_3373_;
v_snd_3307_ = v_snd_3365_;
v___y_3308_ = v___y_3277_;
v___y_3309_ = v___y_3278_;
v___y_3310_ = v___y_3279_;
v___y_3311_ = v___y_3280_;
v___y_3312_ = v___y_3281_;
v___y_3313_ = v___y_3282_;
v___y_3314_ = v___y_3283_;
v___y_3315_ = v___y_3284_;
v___y_3316_ = v___y_3285_;
v___y_3317_ = v___y_3286_;
v___y_3318_ = v___y_3287_;
goto v___jp_3305_;
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
lean_dec(v_snd_3365_);
lean_del_object(v___x_3303_);
lean_dec(v_snd_3301_);
lean_dec(v_fst_3300_);
lean_dec(v_i_3276_);
lean_dec(v___x_3271_);
v_a_3374_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3372_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3372_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
else
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
lean_dec(v_snd_3365_);
lean_dec(v_fst_3364_);
lean_del_object(v___x_3303_);
lean_dec(v_snd_3301_);
lean_dec(v_fst_3300_);
lean_dec(v_i_3276_);
lean_dec(v___x_3271_);
v_a_3382_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3367_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3367_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
else
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
lean_del_object(v___x_3303_);
lean_dec(v_snd_3301_);
lean_dec(v_fst_3300_);
lean_dec(v_i_3276_);
lean_dec(v___x_3271_);
v_a_3390_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3362_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3362_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3395_; 
if (v_isShared_3393_ == 0)
{
v___x_3395_ = v___x_3392_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3390_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
v___jp_3305_:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; size_t v_sz_3321_; size_t v___x_3322_; lean_object* v___x_3323_; 
v___x_3319_ = lean_array_push(v_fst_3300_, v_fst_3306_);
v___x_3320_ = l_Array_zip___redArg(v___x_3295_, v_snd_3307_);
lean_dec_ref(v_snd_3307_);
v_sz_3321_ = lean_array_size(v___x_3320_);
v___x_3322_ = ((size_t)0ULL);
lean_inc(v___x_3271_);
lean_inc(v_i_3276_);
v___x_3323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(v_i_3276_, v___x_3271_, v___x_3320_, v_sz_3321_, v___x_3322_, v_snd_3301_);
lean_dec_ref(v___x_3320_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; lean_object* v___x_3326_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3324_);
lean_dec_ref_known(v___x_3323_, 1);
if (v_isShared_3304_ == 0)
{
lean_ctor_set(v___x_3303_, 1, v_a_3324_);
lean_ctor_set(v___x_3303_, 0, v___x_3319_);
v___x_3326_ = v___x_3303_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___x_3319_);
lean_ctor_set(v_reuseFailAlloc_3329_, 1, v_a_3324_);
v___x_3326_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
lean_object* v___x_3327_; 
v___x_3327_ = lean_nat_add(v_i_3276_, v_step_3290_);
lean_dec(v_i_3276_);
v_b_3275_ = v___x_3326_;
v_i_3276_ = v___x_3327_;
goto _start;
}
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
lean_dec_ref(v___x_3319_);
lean_del_object(v___x_3303_);
lean_dec(v_i_3276_);
lean_dec(v___x_3271_);
v_a_3330_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3323_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3323_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg(lean_object* v___x_3399_, lean_object* v___x_3400_, lean_object* v_jumps_3401_, lean_object* v_xs_3402_, lean_object* v_i_3403_, lean_object* v_range_3404_, lean_object* v_b_3405_, lean_object* v_i_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v_stop_3419_; lean_object* v_step_3420_; uint8_t v___x_3421_; 
v_stop_3419_ = lean_ctor_get(v_range_3404_, 1);
v_step_3420_ = lean_ctor_get(v_range_3404_, 2);
v___x_3421_ = lean_nat_dec_lt(v_i_3406_, v_stop_3419_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; 
lean_dec(v_i_3406_);
lean_dec(v___x_3399_);
v___x_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3422_, 0, v_b_3405_);
return v___x_3422_;
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v_fst_3428_; lean_object* v_snd_3429_; lean_object* v_fst_3430_; lean_object* v_snd_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3529_; 
v___x_3423_ = lean_unsigned_to_nat(0u);
v___x_3424_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1);
v___x_3425_ = lean_array_fget_borrowed(v___x_3400_, v_i_3406_);
v___x_3426_ = lean_array_get_borrowed(v___x_3423_, v___x_3425_, v___x_3423_);
v___x_3427_ = lean_array_get_borrowed(v___x_3424_, v_jumps_3401_, v___x_3426_);
v_fst_3428_ = lean_ctor_get(v___x_3427_, 0);
v_snd_3429_ = lean_ctor_get(v___x_3427_, 1);
v_fst_3430_ = lean_ctor_get(v_b_3405_, 0);
v_snd_3431_ = lean_ctor_get(v_b_3405_, 1);
v_isSharedCheck_3529_ = !lean_is_exclusive(v_b_3405_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3433_ = v_b_3405_;
v_isShared_3434_ = v_isSharedCheck_3529_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_snd_3431_);
lean_inc(v_fst_3430_);
lean_dec(v_b_3405_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3529_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v_fst_3436_; lean_object* v_snd_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___x_3468_; lean_object* v___x_3469_; uint8_t v___x_3470_; 
v___x_3468_ = lean_unsigned_to_nat(1u);
v___x_3469_ = lean_array_get_size(v_snd_3429_);
v___x_3470_ = lean_nat_dec_lt(v_i_3403_, v___x_3469_);
if (v___x_3470_ == 0)
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3471_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__0));
v___x_3472_ = lean_array_get_size(v_xs_3402_);
v___x_3473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3423_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
lean_ctor_set(v___x_3473_, 2, v___x_3468_);
v___x_3474_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(v_xs_3402_, v_fst_3428_, v___x_3473_, v___x_3471_, v___x_3423_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
lean_dec_ref_known(v___x_3473_, 3);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3475_);
lean_dec_ref_known(v___x_3474_, 1);
v___x_3476_ = lean_array_to_list(v_a_3475_);
v___x_3477_ = l_Lean_mkAndN(v___x_3476_);
v___x_3478_ = lean_mk_empty_array_with_capacity(v___x_3468_);
lean_dec_ref(v___x_3478_);
v___x_3479_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__1));
v_fst_3436_ = v___x_3477_;
v_snd_3437_ = v___x_3479_;
v___y_3438_ = v___y_3407_;
v___y_3439_ = v___y_3408_;
v___y_3440_ = v___y_3409_;
v___y_3441_ = v___y_3410_;
v___y_3442_ = v___y_3411_;
v___y_3443_ = v___y_3412_;
v___y_3444_ = v___y_3413_;
v___y_3445_ = v___y_3414_;
v___y_3446_ = v___y_3415_;
v___y_3447_ = v___y_3416_;
v___y_3448_ = v___y_3417_;
goto v___jp_3435_;
}
else
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3487_; 
lean_del_object(v___x_3433_);
lean_dec(v_snd_3431_);
lean_dec(v_fst_3430_);
lean_dec(v_i_3406_);
lean_dec(v___x_3399_);
v_a_3480_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3482_ = v___x_3474_;
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3474_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3485_; 
if (v_isShared_3483_ == 0)
{
v___x_3485_ = v___x_3482_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_a_3480_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
else
{
lean_object* v___x_3488_; size_t v_sz_3489_; size_t v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3488_ = lean_array_fget_borrowed(v_snd_3429_, v_i_3403_);
v_sz_3489_ = lean_array_size(v___x_3425_);
v___x_3490_ = ((size_t)0ULL);
lean_inc(v___x_3425_);
v___x_3491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5(v_jumps_3401_, v_sz_3489_, v___x_3490_, v___x_3425_);
v___x_3492_ = lean_nat_add(v_i_3403_, v___x_3468_);
v___x_3493_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(v_xs_3402_, v___x_3491_, v___x_3492_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
lean_dec(v___x_3492_);
lean_dec_ref(v___x_3491_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; lean_object* v_fst_3495_; lean_object* v_snd_3496_; lean_object* v_proof_3497_; lean_object* v___x_3498_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3494_);
lean_dec_ref_known(v___x_3493_, 1);
v_fst_3495_ = lean_ctor_get(v_a_3494_, 0);
lean_inc(v_fst_3495_);
v_snd_3496_ = lean_ctor_get(v_a_3494_, 1);
lean_inc(v_snd_3496_);
lean_dec(v_a_3494_);
v_proof_3497_ = lean_ctor_get(v_fst_3428_, 0);
lean_inc(v_proof_3497_);
v___x_3498_ = l_Lean_MVarId_getDecl(v_proof_3497_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v_lctx_3500_; lean_object* v_localInstances_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3499_);
lean_dec_ref_known(v___x_3498_, 1);
v_lctx_3500_ = lean_ctor_get(v_a_3499_, 1);
lean_inc_ref(v_lctx_3500_);
v_localInstances_3501_ = lean_ctor_get(v_a_3499_, 4);
lean_inc_ref(v_localInstances_3501_);
lean_dec(v_a_3499_);
lean_inc(v___x_3488_);
v___x_3502_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___boxed), 14, 2);
lean_closure_set(v___x_3502_, 0, v___x_3488_);
lean_closure_set(v___x_3502_, 1, v_fst_3495_);
v___x_3503_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(v_lctx_3500_, v_localInstances_3501_, v___x_3502_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3503_, 1);
v_fst_3436_ = v_a_3504_;
v_snd_3437_ = v_snd_3496_;
v___y_3438_ = v___y_3407_;
v___y_3439_ = v___y_3408_;
v___y_3440_ = v___y_3409_;
v___y_3441_ = v___y_3410_;
v___y_3442_ = v___y_3411_;
v___y_3443_ = v___y_3412_;
v___y_3444_ = v___y_3413_;
v___y_3445_ = v___y_3414_;
v___y_3446_ = v___y_3415_;
v___y_3447_ = v___y_3416_;
v___y_3448_ = v___y_3417_;
goto v___jp_3435_;
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec(v_snd_3496_);
lean_del_object(v___x_3433_);
lean_dec(v_snd_3431_);
lean_dec(v_fst_3430_);
lean_dec(v_i_3406_);
lean_dec(v___x_3399_);
v_a_3505_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3503_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3503_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
else
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3520_; 
lean_dec(v_snd_3496_);
lean_dec(v_fst_3495_);
lean_del_object(v___x_3433_);
lean_dec(v_snd_3431_);
lean_dec(v_fst_3430_);
lean_dec(v_i_3406_);
lean_dec(v___x_3399_);
v_a_3513_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3515_ = v___x_3498_;
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3498_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3518_; 
if (v_isShared_3516_ == 0)
{
v___x_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3513_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
}
else
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
lean_del_object(v___x_3433_);
lean_dec(v_snd_3431_);
lean_dec(v_fst_3430_);
lean_dec(v_i_3406_);
lean_dec(v___x_3399_);
v_a_3521_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3493_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3493_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
v___jp_3435_:
{
lean_object* v___x_3449_; lean_object* v___x_3450_; size_t v_sz_3451_; size_t v___x_3452_; lean_object* v___x_3453_; 
v___x_3449_ = lean_array_push(v_fst_3430_, v_fst_3436_);
v___x_3450_ = l_Array_zip___redArg(v___x_3425_, v_snd_3437_);
lean_dec_ref(v_snd_3437_);
v_sz_3451_ = lean_array_size(v___x_3450_);
v___x_3452_ = ((size_t)0ULL);
lean_inc(v___x_3399_);
lean_inc(v_i_3406_);
v___x_3453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(v_i_3406_, v___x_3399_, v___x_3450_, v_sz_3451_, v___x_3452_, v_snd_3431_);
lean_dec_ref(v___x_3450_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3456_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref_known(v___x_3453_, 1);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 1, v_a_3454_);
lean_ctor_set(v___x_3433_, 0, v___x_3449_);
v___x_3456_ = v___x_3433_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v___x_3449_);
lean_ctor_set(v_reuseFailAlloc_3459_, 1, v_a_3454_);
v___x_3456_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3457_ = lean_nat_add(v_i_3406_, v_step_3420_);
lean_dec(v_i_3406_);
v___x_3458_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg(v___x_3400_, v_jumps_3401_, v___x_3399_, v_i_3403_, v_xs_3402_, v_range_3404_, v___x_3456_, v___x_3457_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
return v___x_3458_;
}
}
else
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
lean_dec_ref(v___x_3449_);
lean_del_object(v___x_3433_);
lean_dec(v_i_3406_);
lean_dec(v___x_3399_);
v_a_3460_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3453_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3453_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(lean_object* v_xs_3530_, lean_object* v_jumps_3531_, lean_object* v_i_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_){
_start:
{
lean_object* v___x_3545_; lean_object* v_groups_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3545_ = lean_unsigned_to_nat(0u);
v_groups_3546_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__0));
v___x_3547_ = lean_array_get_size(v_jumps_3531_);
v___x_3548_ = lean_unsigned_to_nat(1u);
v___x_3549_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3545_);
lean_ctor_set(v___x_3549_, 1, v___x_3547_);
lean_ctor_set(v___x_3549_, 2, v___x_3548_);
v___x_3550_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__3, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__3);
v___x_3551_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg(v_jumps_3531_, v_i_3532_, v___x_3549_, v___x_3550_, v___x_3545_);
lean_dec_ref_known(v___x_3549_, 3);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v_fst_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3592_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3552_);
lean_dec_ref_known(v___x_3551_, 1);
v_fst_3553_ = lean_ctor_get(v_a_3552_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v_a_3552_);
if (v_isSharedCheck_3592_ == 0)
{
lean_object* v_unused_3593_; 
v_unused_3593_ = lean_ctor_get(v_a_3552_, 1);
lean_dec(v_unused_3593_);
v___x_3555_ = v_a_3552_;
v_isShared_3556_ = v_isSharedCheck_3592_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_fst_3553_);
lean_dec(v_a_3552_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3592_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3562_; 
v___x_3557_ = lean_box(0);
v___x_3558_ = lean_mk_array(v___x_3547_, v___x_3557_);
v___x_3559_ = lean_array_get_size(v_fst_3553_);
v___x_3560_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3545_);
lean_ctor_set(v___x_3560_, 1, v___x_3559_);
lean_ctor_set(v___x_3560_, 2, v___x_3548_);
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 1, v___x_3558_);
lean_ctor_set(v___x_3555_, 0, v_groups_3546_);
v___x_3562_ = v___x_3555_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_groups_3546_);
lean_ctor_set(v_reuseFailAlloc_3591_, 1, v___x_3558_);
v___x_3562_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
lean_object* v___x_3563_; 
v___x_3563_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg(v___x_3559_, v_fst_3553_, v_jumps_3531_, v_xs_3530_, v_i_3532_, v___x_3560_, v___x_3562_, v___x_3545_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_);
lean_dec_ref_known(v___x_3560_, 3);
lean_dec(v_fst_3553_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3582_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3566_ = v___x_3563_;
v_isShared_3567_ = v_isSharedCheck_3582_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3563_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3582_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v_fst_3568_; lean_object* v_snd_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3581_; 
v_fst_3568_ = lean_ctor_get(v_a_3564_, 0);
v_snd_3569_ = lean_ctor_get(v_a_3564_, 1);
v_isSharedCheck_3581_ = !lean_is_exclusive(v_a_3564_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3571_ = v_a_3564_;
v_isShared_3572_ = v_isSharedCheck_3581_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_snd_3569_);
lean_inc(v_fst_3568_);
lean_dec(v_a_3564_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3581_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3576_; 
v___x_3573_ = lean_array_get_size(v_fst_3568_);
v___x_3574_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(v_fst_3568_, v___x_3545_, v___x_3573_);
lean_dec(v_fst_3568_);
if (v_isShared_3572_ == 0)
{
lean_ctor_set(v___x_3571_, 0, v___x_3574_);
v___x_3576_ = v___x_3571_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3574_);
lean_ctor_set(v_reuseFailAlloc_3580_, 1, v_snd_3569_);
v___x_3576_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
lean_object* v___x_3578_; 
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 0, v___x_3576_);
v___x_3578_ = v___x_3566_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3576_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
v_a_3583_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3563_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3563_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
}
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
v_a_3594_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3551_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3551_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___boxed(lean_object* v_xs_3602_, lean_object* v_jumps_3603_, lean_object* v_i_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_){
_start:
{
lean_object* v_res_3617_; 
v_res_3617_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(v_xs_3602_, v_jumps_3603_, v_i_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_);
lean_dec(v_a_3615_);
lean_dec_ref(v_a_3614_);
lean_dec(v_a_3613_);
lean_dec_ref(v_a_3612_);
lean_dec(v_a_3611_);
lean_dec_ref(v_a_3610_);
lean_dec(v_a_3609_);
lean_dec_ref(v_a_3608_);
lean_dec(v_a_3607_);
lean_dec(v_a_3606_);
lean_dec_ref(v_a_3605_);
lean_dec(v_i_3604_);
lean_dec_ref(v_jumps_3603_);
lean_dec_ref(v_xs_3602_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___boxed(lean_object** _args){
lean_object* v___x_3618_ = _args[0];
lean_object* v_jumps_3619_ = _args[1];
lean_object* v___x_3620_ = _args[2];
lean_object* v_i_3621_ = _args[3];
lean_object* v_xs_3622_ = _args[4];
lean_object* v_range_3623_ = _args[5];
lean_object* v_b_3624_ = _args[6];
lean_object* v_i_3625_ = _args[7];
lean_object* v___y_3626_ = _args[8];
lean_object* v___y_3627_ = _args[9];
lean_object* v___y_3628_ = _args[10];
lean_object* v___y_3629_ = _args[11];
lean_object* v___y_3630_ = _args[12];
lean_object* v___y_3631_ = _args[13];
lean_object* v___y_3632_ = _args[14];
lean_object* v___y_3633_ = _args[15];
lean_object* v___y_3634_ = _args[16];
lean_object* v___y_3635_ = _args[17];
lean_object* v___y_3636_ = _args[18];
lean_object* v___y_3637_ = _args[19];
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg(v___x_3618_, v_jumps_3619_, v___x_3620_, v_i_3621_, v_xs_3622_, v_range_3623_, v_b_3624_, v_i_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec_ref(v_range_3623_);
lean_dec_ref(v_xs_3622_);
lean_dec(v_i_3621_);
lean_dec_ref(v_jumps_3619_);
lean_dec_ref(v___x_3618_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg___boxed(lean_object** _args){
lean_object* v___x_3639_ = _args[0];
lean_object* v___x_3640_ = _args[1];
lean_object* v_jumps_3641_ = _args[2];
lean_object* v_xs_3642_ = _args[3];
lean_object* v_i_3643_ = _args[4];
lean_object* v_range_3644_ = _args[5];
lean_object* v_b_3645_ = _args[6];
lean_object* v_i_3646_ = _args[7];
lean_object* v___y_3647_ = _args[8];
lean_object* v___y_3648_ = _args[9];
lean_object* v___y_3649_ = _args[10];
lean_object* v___y_3650_ = _args[11];
lean_object* v___y_3651_ = _args[12];
lean_object* v___y_3652_ = _args[13];
lean_object* v___y_3653_ = _args[14];
lean_object* v___y_3654_ = _args[15];
lean_object* v___y_3655_ = _args[16];
lean_object* v___y_3656_ = _args[17];
lean_object* v___y_3657_ = _args[18];
lean_object* v___y_3658_ = _args[19];
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg(v___x_3639_, v___x_3640_, v_jumps_3641_, v_xs_3642_, v_i_3643_, v_range_3644_, v_b_3645_, v_i_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
lean_dec(v___y_3655_);
lean_dec_ref(v___y_3654_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
lean_dec(v___y_3649_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec_ref(v_range_3644_);
lean_dec(v_i_3643_);
lean_dec_ref(v_xs_3642_);
lean_dec_ref(v_jumps_3641_);
lean_dec_ref(v___x_3640_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0(lean_object* v_00_u03b2_3660_, lean_object* v_m_3661_, lean_object* v_a_3662_){
_start:
{
lean_object* v___x_3663_; 
v___x_3663_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg(v_m_3661_, v_a_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___boxed(lean_object* v_00_u03b2_3664_, lean_object* v_m_3665_, lean_object* v_a_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0(v_00_u03b2_3664_, v_m_3665_, v_a_3666_);
lean_dec(v_a_3666_);
lean_dec_ref(v_m_3665_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1(lean_object* v_00_u03b2_3668_, lean_object* v_m_3669_, lean_object* v_a_3670_, lean_object* v_b_3671_){
_start:
{
lean_object* v___x_3672_; 
v___x_3672_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1___redArg(v_m_3669_, v_a_3670_, v_b_3671_);
return v___x_3672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2(lean_object* v_jumps_3673_, lean_object* v_i_3674_, lean_object* v_range_3675_, lean_object* v_b_3676_, lean_object* v_i_3677_, lean_object* v_hs_3678_, lean_object* v_hl_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg(v_jumps_3673_, v_i_3674_, v_range_3675_, v_b_3676_, v_i_3677_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___boxed(lean_object** _args){
lean_object* v_jumps_3693_ = _args[0];
lean_object* v_i_3694_ = _args[1];
lean_object* v_range_3695_ = _args[2];
lean_object* v_b_3696_ = _args[3];
lean_object* v_i_3697_ = _args[4];
lean_object* v_hs_3698_ = _args[5];
lean_object* v_hl_3699_ = _args[6];
lean_object* v___y_3700_ = _args[7];
lean_object* v___y_3701_ = _args[8];
lean_object* v___y_3702_ = _args[9];
lean_object* v___y_3703_ = _args[10];
lean_object* v___y_3704_ = _args[11];
lean_object* v___y_3705_ = _args[12];
lean_object* v___y_3706_ = _args[13];
lean_object* v___y_3707_ = _args[14];
lean_object* v___y_3708_ = _args[15];
lean_object* v___y_3709_ = _args[16];
lean_object* v___y_3710_ = _args[17];
lean_object* v___y_3711_ = _args[18];
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2(v_jumps_3693_, v_i_3694_, v_range_3695_, v_b_3696_, v_i_3697_, v_hs_3698_, v_hl_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
lean_dec(v___y_3702_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v_range_3695_);
lean_dec(v_i_3694_);
lean_dec_ref(v_jumps_3693_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3(lean_object* v_g_3713_, lean_object* v___x_3714_, lean_object* v_as_3715_, size_t v_sz_3716_, size_t v_i_3717_, lean_object* v_b_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v___x_3731_; 
v___x_3731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(v_g_3713_, v___x_3714_, v_as_3715_, v_sz_3716_, v_i_3717_, v_b_3718_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___boxed(lean_object** _args){
lean_object* v_g_3732_ = _args[0];
lean_object* v___x_3733_ = _args[1];
lean_object* v_as_3734_ = _args[2];
lean_object* v_sz_3735_ = _args[3];
lean_object* v_i_3736_ = _args[4];
lean_object* v_b_3737_ = _args[5];
lean_object* v___y_3738_ = _args[6];
lean_object* v___y_3739_ = _args[7];
lean_object* v___y_3740_ = _args[8];
lean_object* v___y_3741_ = _args[9];
lean_object* v___y_3742_ = _args[10];
lean_object* v___y_3743_ = _args[11];
lean_object* v___y_3744_ = _args[12];
lean_object* v___y_3745_ = _args[13];
lean_object* v___y_3746_ = _args[14];
lean_object* v___y_3747_ = _args[15];
lean_object* v___y_3748_ = _args[16];
lean_object* v___y_3749_ = _args[17];
_start:
{
size_t v_sz_boxed_3750_; size_t v_i_boxed_3751_; lean_object* v_res_3752_; 
v_sz_boxed_3750_ = lean_unbox_usize(v_sz_3735_);
lean_dec(v_sz_3735_);
v_i_boxed_3751_ = lean_unbox_usize(v_i_3736_);
lean_dec(v_i_3736_);
v_res_3752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3(v_g_3732_, v___x_3733_, v_as_3734_, v_sz_boxed_3750_, v_i_boxed_3751_, v_b_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
lean_dec(v___y_3748_);
lean_dec_ref(v___y_3747_);
lean_dec(v___y_3746_);
lean_dec_ref(v___y_3745_);
lean_dec(v___y_3744_);
lean_dec_ref(v___y_3743_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec(v___y_3740_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec_ref(v_as_3734_);
return v_res_3752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4(lean_object* v_xs_3753_, lean_object* v_fst_3754_, lean_object* v_range_3755_, lean_object* v_b_3756_, lean_object* v_i_3757_, lean_object* v_hs_3758_, lean_object* v_hl_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v___x_3772_; 
v___x_3772_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(v_xs_3753_, v_fst_3754_, v_range_3755_, v_b_3756_, v_i_3757_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___boxed(lean_object** _args){
lean_object* v_xs_3773_ = _args[0];
lean_object* v_fst_3774_ = _args[1];
lean_object* v_range_3775_ = _args[2];
lean_object* v_b_3776_ = _args[3];
lean_object* v_i_3777_ = _args[4];
lean_object* v_hs_3778_ = _args[5];
lean_object* v_hl_3779_ = _args[6];
lean_object* v___y_3780_ = _args[7];
lean_object* v___y_3781_ = _args[8];
lean_object* v___y_3782_ = _args[9];
lean_object* v___y_3783_ = _args[10];
lean_object* v___y_3784_ = _args[11];
lean_object* v___y_3785_ = _args[12];
lean_object* v___y_3786_ = _args[13];
lean_object* v___y_3787_ = _args[14];
lean_object* v___y_3788_ = _args[15];
lean_object* v___y_3789_ = _args[16];
lean_object* v___y_3790_ = _args[17];
lean_object* v___y_3791_ = _args[18];
_start:
{
lean_object* v_res_3792_; 
v_res_3792_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4(v_xs_3773_, v_fst_3774_, v_range_3775_, v_b_3776_, v_i_3777_, v_hs_3778_, v_hl_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec_ref(v_range_3775_);
lean_dec_ref(v_fst_3774_);
lean_dec_ref(v_xs_3773_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7(lean_object* v___x_3793_, lean_object* v___x_3794_, lean_object* v_jumps_3795_, lean_object* v_xs_3796_, lean_object* v_i_3797_, lean_object* v_range_3798_, lean_object* v_b_3799_, lean_object* v_i_3800_, lean_object* v_hs_3801_, lean_object* v_hl_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v___x_3815_; 
v___x_3815_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg(v___x_3793_, v___x_3794_, v_jumps_3795_, v_xs_3796_, v_i_3797_, v_range_3798_, v_b_3799_, v_i_3800_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___boxed(lean_object** _args){
lean_object* v___x_3816_ = _args[0];
lean_object* v___x_3817_ = _args[1];
lean_object* v_jumps_3818_ = _args[2];
lean_object* v_xs_3819_ = _args[3];
lean_object* v_i_3820_ = _args[4];
lean_object* v_range_3821_ = _args[5];
lean_object* v_b_3822_ = _args[6];
lean_object* v_i_3823_ = _args[7];
lean_object* v_hs_3824_ = _args[8];
lean_object* v_hl_3825_ = _args[9];
lean_object* v___y_3826_ = _args[10];
lean_object* v___y_3827_ = _args[11];
lean_object* v___y_3828_ = _args[12];
lean_object* v___y_3829_ = _args[13];
lean_object* v___y_3830_ = _args[14];
lean_object* v___y_3831_ = _args[15];
lean_object* v___y_3832_ = _args[16];
lean_object* v___y_3833_ = _args[17];
lean_object* v___y_3834_ = _args[18];
lean_object* v___y_3835_ = _args[19];
lean_object* v___y_3836_ = _args[20];
lean_object* v___y_3837_ = _args[21];
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7(v___x_3816_, v___x_3817_, v_jumps_3818_, v_xs_3819_, v_i_3820_, v_range_3821_, v_b_3822_, v_i_3823_, v_hs_3824_, v_hl_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec_ref(v_range_3821_);
lean_dec(v_i_3820_);
lean_dec_ref(v_xs_3819_);
lean_dec_ref(v_jumps_3818_);
lean_dec_ref(v___x_3817_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0(lean_object* v_00_u03b2_3839_, lean_object* v_a_3840_, lean_object* v_x_3841_){
_start:
{
lean_object* v___x_3842_; 
v___x_3842_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg(v_a_3840_, v_x_3841_);
return v___x_3842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3843_, lean_object* v_a_3844_, lean_object* v_x_3845_){
_start:
{
lean_object* v_res_3846_; 
v_res_3846_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0(v_00_u03b2_3843_, v_a_3844_, v_x_3845_);
lean_dec(v_x_3845_);
lean_dec(v_a_3844_);
return v_res_3846_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2(lean_object* v_00_u03b2_3847_, lean_object* v_a_3848_, lean_object* v_x_3849_){
_start:
{
uint8_t v___x_3850_; 
v___x_3850_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg(v_a_3848_, v_x_3849_);
return v___x_3850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3851_, lean_object* v_a_3852_, lean_object* v_x_3853_){
_start:
{
uint8_t v_res_3854_; lean_object* v_r_3855_; 
v_res_3854_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2(v_00_u03b2_3851_, v_a_3852_, v_x_3853_);
lean_dec(v_x_3853_);
lean_dec(v_a_3852_);
v_r_3855_ = lean_box(v_res_3854_);
return v_r_3855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3(lean_object* v_00_u03b2_3856_, lean_object* v_data_3857_){
_start:
{
lean_object* v___x_3858_; 
v___x_3858_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3___redArg(v_data_3857_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4(lean_object* v_00_u03b2_3859_, lean_object* v_a_3860_, lean_object* v_b_3861_, lean_object* v_x_3862_){
_start:
{
lean_object* v___x_3863_; 
v___x_3863_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4___redArg(v_a_3860_, v_b_3861_, v_x_3862_);
return v___x_3863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11(lean_object* v___x_3864_, lean_object* v_jumps_3865_, lean_object* v___x_3866_, lean_object* v_i_3867_, lean_object* v_xs_3868_, lean_object* v_range_3869_, lean_object* v_b_3870_, lean_object* v_i_3871_, lean_object* v_hs_3872_, lean_object* v_hl_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v___x_3886_; 
v___x_3886_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg(v___x_3864_, v_jumps_3865_, v___x_3866_, v_i_3867_, v_xs_3868_, v_range_3869_, v_b_3870_, v_i_3871_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_3886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___boxed(lean_object** _args){
lean_object* v___x_3887_ = _args[0];
lean_object* v_jumps_3888_ = _args[1];
lean_object* v___x_3889_ = _args[2];
lean_object* v_i_3890_ = _args[3];
lean_object* v_xs_3891_ = _args[4];
lean_object* v_range_3892_ = _args[5];
lean_object* v_b_3893_ = _args[6];
lean_object* v_i_3894_ = _args[7];
lean_object* v_hs_3895_ = _args[8];
lean_object* v_hl_3896_ = _args[9];
lean_object* v___y_3897_ = _args[10];
lean_object* v___y_3898_ = _args[11];
lean_object* v___y_3899_ = _args[12];
lean_object* v___y_3900_ = _args[13];
lean_object* v___y_3901_ = _args[14];
lean_object* v___y_3902_ = _args[15];
lean_object* v___y_3903_ = _args[16];
lean_object* v___y_3904_ = _args[17];
lean_object* v___y_3905_ = _args[18];
lean_object* v___y_3906_ = _args[19];
lean_object* v___y_3907_ = _args[20];
lean_object* v___y_3908_ = _args[21];
_start:
{
lean_object* v_res_3909_; 
v_res_3909_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11(v___x_3887_, v_jumps_3888_, v___x_3889_, v_i_3890_, v_xs_3891_, v_range_3892_, v_b_3893_, v_i_3894_, v_hs_3895_, v_hl_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec_ref(v_range_3892_);
lean_dec_ref(v_xs_3891_);
lean_dec(v_i_3890_);
lean_dec_ref(v_jumps_3888_);
lean_dec_ref(v___x_3887_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_3910_, lean_object* v_i_3911_, lean_object* v_source_3912_, lean_object* v_target_3913_){
_start:
{
lean_object* v___x_3914_; 
v___x_3914_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5___redArg(v_i_3911_, v_source_3912_, v_target_3913_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_3915_, lean_object* v_x_3916_, lean_object* v_x_3917_){
_start:
{
lean_object* v___x_3918_; 
v___x_3918_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5_spec__11___redArg(v_x_3916_, v_x_3917_);
return v___x_3918_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__1(void){
_start:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3920_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__0));
v___x_3921_ = l_Lean_stringToMessageData(v___x_3920_);
return v___x_3921_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10(void){
_start:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3936_ = lean_box(0);
v___x_3937_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__9));
v___x_3938_ = l_Lean_mkConst(v___x_3937_, v___x_3936_);
return v___x_3938_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__12(void){
_start:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3942_ = lean_box(0);
v___x_3943_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__11));
v___x_3944_ = l_Lean_mkConst(v___x_3943_, v___x_3942_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(lean_object* v_00_u03c6_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_){
_start:
{
lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___x_3960_; 
lean_inc_ref(v_00_u03c6_3945_);
v___x_3960_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_00_u03c6_3945_, v_a_3947_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_4006_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_3963_ = v___x_3960_;
v_isShared_3964_ = v_isSharedCheck_4006_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_a_3961_);
lean_dec(v___x_3960_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_4006_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; uint8_t v___x_3967_; 
v___x_3965_ = l_Lean_Expr_cleanupAnnotations(v_a_3961_);
lean_dec(v_a_3961_);
v___x_3966_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__3));
v___x_3967_ = l_Lean_Expr_isConstOf(v___x_3965_, v___x_3966_);
if (v___x_3967_ == 0)
{
uint8_t v___x_3968_; 
v___x_3968_ = l_Lean_Expr_isApp(v___x_3965_);
if (v___x_3968_ == 0)
{
lean_dec_ref(v___x_3965_);
lean_del_object(v___x_3963_);
v___y_3952_ = v_a_3946_;
v___y_3953_ = v_a_3947_;
v___y_3954_ = v_a_3948_;
v___y_3955_ = v_a_3949_;
goto v___jp_3951_;
}
else
{
lean_object* v___x_3969_; uint8_t v___x_3970_; 
v___x_3969_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3965_);
v___x_3970_ = l_Lean_Expr_isApp(v___x_3969_);
if (v___x_3970_ == 0)
{
lean_dec_ref(v___x_3969_);
lean_dec_ref(v___x_3965_);
lean_del_object(v___x_3963_);
v___y_3952_ = v_a_3946_;
v___y_3953_ = v_a_3947_;
v___y_3954_ = v_a_3948_;
v___y_3955_ = v_a_3949_;
goto v___jp_3951_;
}
else
{
lean_object* v_arg_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; uint8_t v___x_3974_; 
v_arg_3971_ = lean_ctor_get(v___x_3969_, 1);
lean_inc_ref(v_arg_3971_);
v___x_3972_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3969_);
lean_dec_ref(v___x_3969_);
v___x_3973_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__5));
v___x_3974_ = l_Lean_Expr_isConstOf(v___x_3972_, v___x_3973_);
if (v___x_3974_ == 0)
{
uint8_t v___x_3975_; 
lean_dec_ref(v___x_3965_);
v___x_3975_ = l_Lean_Expr_isApp(v___x_3972_);
if (v___x_3975_ == 0)
{
lean_dec_ref(v___x_3972_);
lean_dec_ref(v_arg_3971_);
lean_del_object(v___x_3963_);
v___y_3952_ = v_a_3946_;
v___y_3953_ = v_a_3947_;
v___y_3954_ = v_a_3948_;
v___y_3955_ = v_a_3949_;
goto v___jp_3951_;
}
else
{
lean_object* v___x_3976_; lean_object* v___x_3977_; uint8_t v___x_3978_; 
v___x_3976_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3972_);
v___x_3977_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__3));
v___x_3978_ = l_Lean_Expr_isConstOf(v___x_3976_, v___x_3977_);
lean_dec_ref(v___x_3976_);
if (v___x_3978_ == 0)
{
lean_dec_ref(v___x_3972_);
lean_dec_ref(v_arg_3971_);
lean_del_object(v___x_3963_);
v___y_3952_ = v_a_3946_;
v___y_3953_ = v_a_3947_;
v___y_3954_ = v_a_3948_;
v___y_3955_ = v_a_3949_;
goto v___jp_3951_;
}
else
{
lean_object* v_arg_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3986_; 
v_arg_3979_ = lean_ctor_get(v___x_3972_, 1);
lean_inc_ref(v_arg_3979_);
lean_dec_ref(v___x_3972_);
v___x_3980_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__7));
v___x_3981_ = l_Lean_Expr_getAppFn(v_00_u03c6_3945_);
lean_dec_ref(v_00_u03c6_3945_);
v___x_3982_ = l_Lean_Expr_constLevels_x21(v___x_3981_);
lean_dec_ref(v___x_3981_);
v___x_3983_ = l_Lean_mkConst(v___x_3980_, v___x_3982_);
v___x_3984_ = l_Lean_mkAppB(v___x_3983_, v_arg_3979_, v_arg_3971_);
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 0, v___x_3984_);
v___x_3986_ = v___x_3963_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v___x_3984_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
else
{
lean_object* v_arg_3988_; lean_object* v___x_3989_; 
lean_dec_ref(v___x_3972_);
lean_del_object(v___x_3963_);
lean_dec_ref(v_00_u03c6_3945_);
v_arg_3988_ = lean_ctor_get(v___x_3965_, 1);
lean_inc_ref(v_arg_3988_);
lean_dec_ref(v___x_3965_);
lean_inc_ref(v_arg_3971_);
v___x_3989_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(v_arg_3971_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
if (lean_obj_tag(v___x_3989_) == 0)
{
lean_object* v_a_3990_; lean_object* v___x_3991_; 
v_a_3990_ = lean_ctor_get(v___x_3989_, 0);
lean_inc(v_a_3990_);
lean_dec_ref_known(v___x_3989_, 1);
lean_inc_ref(v_arg_3988_);
v___x_3991_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(v_arg_3988_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_object* v_a_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_4001_; 
v_a_3992_ = lean_ctor_get(v___x_3991_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3994_ = v___x_3991_;
v_isShared_3995_ = v_isSharedCheck_4001_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_a_3992_);
lean_dec(v___x_3991_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_4001_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3999_; 
v___x_3996_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10);
v___x_3997_ = l_Lean_mkApp4(v___x_3996_, v_arg_3971_, v_arg_3988_, v_a_3990_, v_a_3992_);
if (v_isShared_3995_ == 0)
{
lean_ctor_set(v___x_3994_, 0, v___x_3997_);
v___x_3999_ = v___x_3994_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___x_3997_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
else
{
lean_dec(v_a_3990_);
lean_dec_ref(v_arg_3988_);
lean_dec_ref(v_arg_3971_);
return v___x_3991_;
}
}
else
{
lean_dec_ref(v_arg_3988_);
lean_dec_ref(v_arg_3971_);
return v___x_3989_;
}
}
}
}
}
else
{
lean_object* v___x_4002_; lean_object* v___x_4004_; 
lean_dec_ref(v___x_3965_);
lean_dec_ref(v_00_u03c6_3945_);
v___x_4002_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__12, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__12_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__12);
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 0, v___x_4002_);
v___x_4004_ = v___x_3963_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___x_4002_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
}
}
else
{
lean_dec_ref(v_00_u03c6_3945_);
return v___x_3960_;
}
v___jp_3951_:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3956_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__1, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__1);
v___x_3957_ = l_Lean_indentExpr(v_00_u03c6_3945_);
v___x_3958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3956_);
lean_ctor_set(v___x_3958_, 1, v___x_3957_);
v___x_3959_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v___x_3958_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
return v___x_3959_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___boxed(lean_object* v_00_u03c6_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(v_00_u03c6_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_);
lean_dec(v_a_4011_);
lean_dec_ref(v_a_4010_);
lean_dec(v_a_4009_);
lean_dec_ref(v_a_4008_);
return v_res_4013_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__1(void){
_start:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; 
v___x_4015_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__0));
v___x_4016_ = l_Lean_stringToMessageData(v___x_4015_);
return v___x_4016_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; 
v___x_4018_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__0));
v___x_4019_ = l_Lean_stringToMessageData(v___x_4018_);
return v___x_4019_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4024_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__3));
v___x_4025_ = l_Lean_stringToMessageData(v___x_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0(lean_object* v_tail_4026_, lean_object* v_locals_4027_, lean_object* v_00_u03c6_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_){
_start:
{
lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; uint8_t v___x_4043_; 
v___x_4043_ = l_List_isEmpty___redArg(v_tail_4026_);
if (v___x_4043_ == 0)
{
if (lean_obj_tag(v_locals_4027_) == 1)
{
lean_object* v_head_4044_; lean_object* v_tail_4045_; lean_object* v___x_4046_; 
v_head_4044_ = lean_ctor_get(v_locals_4027_, 0);
lean_inc(v_head_4044_);
v_tail_4045_ = lean_ctor_get(v_locals_4027_, 1);
lean_inc(v_tail_4045_);
lean_dec_ref_known(v_locals_4027_, 2);
v___x_4046_ = l_Lean_LocalDecl_value_x3f(v_head_4044_, v___x_4043_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_w_4047_; lean_object* v___x_4048_; 
v_w_4047_ = l_Lean_LocalDecl_toExpr(v_head_4044_);
lean_inc_ref(v_00_u03c6_4028_);
v___x_4048_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_00_u03c6_4028_, v___y_4030_);
if (lean_obj_tag(v___x_4048_) == 0)
{
lean_object* v_a_4049_; lean_object* v___x_4050_; uint8_t v___x_4051_; 
v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
lean_inc(v_a_4049_);
lean_dec_ref_known(v___x_4048_, 1);
v___x_4050_ = l_Lean_Expr_cleanupAnnotations(v_a_4049_);
lean_dec(v_a_4049_);
v___x_4051_ = l_Lean_Expr_isApp(v___x_4050_);
if (v___x_4051_ == 0)
{
lean_dec_ref(v___x_4050_);
lean_dec_ref(v_w_4047_);
lean_dec(v_tail_4045_);
lean_dec(v_tail_4026_);
v___y_4035_ = v___y_4029_;
v___y_4036_ = v___y_4030_;
v___y_4037_ = v___y_4031_;
v___y_4038_ = v___y_4032_;
goto v___jp_4034_;
}
else
{
lean_object* v___x_4052_; uint8_t v___x_4053_; 
v___x_4052_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4050_);
v___x_4053_ = l_Lean_Expr_isApp(v___x_4052_);
if (v___x_4053_ == 0)
{
lean_dec_ref(v___x_4052_);
lean_dec_ref(v___x_4050_);
lean_dec_ref(v_w_4047_);
lean_dec(v_tail_4045_);
lean_dec(v_tail_4026_);
v___y_4035_ = v___y_4029_;
v___y_4036_ = v___y_4030_;
v___y_4037_ = v___y_4031_;
v___y_4038_ = v___y_4032_;
goto v___jp_4034_;
}
else
{
lean_object* v_arg_4054_; lean_object* v_arg_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; uint8_t v___x_4058_; 
v_arg_4054_ = lean_ctor_get(v___x_4050_, 1);
lean_inc_ref(v_arg_4054_);
lean_dec_ref(v___x_4050_);
v_arg_4055_ = lean_ctor_get(v___x_4052_, 1);
lean_inc_ref(v_arg_4055_);
v___x_4056_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4052_);
lean_dec_ref(v___x_4052_);
v___x_4057_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__5));
v___x_4058_ = l_Lean_Expr_isConstOf(v___x_4056_, v___x_4057_);
if (v___x_4058_ == 0)
{
lean_object* v___x_4059_; uint8_t v___x_4060_; 
v___x_4059_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___closed__1));
v___x_4060_ = l_Lean_Expr_isConstOf(v___x_4056_, v___x_4059_);
lean_dec_ref(v___x_4056_);
if (v___x_4060_ == 0)
{
lean_dec_ref(v_arg_4055_);
lean_dec_ref(v_arg_4054_);
lean_dec_ref(v_w_4047_);
lean_dec(v_tail_4045_);
lean_dec(v_tail_4026_);
v___y_4035_ = v___y_4029_;
v___y_4036_ = v___y_4030_;
v___y_4037_ = v___y_4031_;
v___y_4038_ = v___y_4032_;
goto v___jp_4034_;
}
else
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4061_ = lean_unsigned_to_nat(1u);
v___x_4062_ = lean_mk_empty_array_with_capacity(v___x_4061_);
lean_inc_ref(v_w_4047_);
v___x_4063_ = lean_array_push(v___x_4062_, v_w_4047_);
lean_inc_ref(v_arg_4054_);
v___x_4064_ = l_Lean_Expr_beta(v_arg_4054_, v___x_4063_);
v___x_4065_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v___x_4064_, v_tail_4026_, v_tail_4045_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
if (lean_obj_tag(v___x_4065_) == 0)
{
lean_object* v_a_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4078_; 
v_a_4066_ = lean_ctor_get(v___x_4065_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4065_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4068_ = v___x_4065_;
v_isShared_4069_ = v_isSharedCheck_4078_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_a_4066_);
lean_dec(v___x_4065_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4078_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4076_; 
v___x_4070_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__2));
v___x_4071_ = l_Lean_Expr_getAppFn(v_00_u03c6_4028_);
lean_dec_ref(v_00_u03c6_4028_);
v___x_4072_ = l_Lean_Expr_constLevels_x21(v___x_4071_);
lean_dec_ref(v___x_4071_);
v___x_4073_ = l_Lean_mkConst(v___x_4070_, v___x_4072_);
v___x_4074_ = l_Lean_mkApp4(v___x_4073_, v_arg_4055_, v_arg_4054_, v_w_4047_, v_a_4066_);
if (v_isShared_4069_ == 0)
{
lean_ctor_set(v___x_4068_, 0, v___x_4074_);
v___x_4076_ = v___x_4068_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v___x_4074_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
else
{
lean_dec_ref(v_arg_4055_);
lean_dec_ref(v_arg_4054_);
lean_dec_ref(v_w_4047_);
lean_dec_ref(v_00_u03c6_4028_);
return v___x_4065_;
}
}
}
else
{
lean_object* v___x_4079_; 
lean_dec_ref(v___x_4056_);
lean_dec_ref(v_00_u03c6_4028_);
lean_inc_ref(v_arg_4054_);
v___x_4079_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v_arg_4054_, v_tail_4026_, v_tail_4045_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4089_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4082_ = v___x_4079_;
v_isShared_4083_ = v_isSharedCheck_4089_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_a_4080_);
lean_dec(v___x_4079_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4089_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4087_; 
v___x_4084_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10);
v___x_4085_ = l_Lean_mkApp4(v___x_4084_, v_arg_4055_, v_arg_4054_, v_w_4047_, v_a_4080_);
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 0, v___x_4085_);
v___x_4087_ = v___x_4082_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___x_4085_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
else
{
lean_dec_ref(v_arg_4055_);
lean_dec_ref(v_arg_4054_);
lean_dec_ref(v_w_4047_);
return v___x_4079_;
}
}
}
}
}
else
{
lean_dec_ref(v_w_4047_);
lean_dec(v_tail_4045_);
lean_dec_ref(v_00_u03c6_4028_);
lean_dec(v_tail_4026_);
return v___x_4048_;
}
}
else
{
lean_dec_ref_known(v___x_4046_, 1);
lean_dec(v_head_4044_);
if (lean_obj_tag(v_00_u03c6_4028_) == 8)
{
lean_object* v_value_4090_; lean_object* v_body_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
v_value_4090_ = lean_ctor_get(v_00_u03c6_4028_, 2);
lean_inc_ref(v_value_4090_);
v_body_4091_ = lean_ctor_get(v_00_u03c6_4028_, 3);
lean_inc_ref(v_body_4091_);
lean_dec_ref_known(v_00_u03c6_4028_, 4);
v___x_4092_ = lean_expr_instantiate1(v_body_4091_, v_value_4090_);
lean_dec_ref(v_value_4090_);
lean_dec_ref(v_body_4091_);
v___x_4093_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v___x_4092_, v_tail_4026_, v_tail_4045_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
return v___x_4093_;
}
else
{
lean_object* v___x_4094_; 
v___x_4094_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v_00_u03c6_4028_, v_tail_4026_, v_tail_4045_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
return v___x_4094_;
}
}
}
else
{
lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
lean_dec(v_locals_4027_);
lean_dec(v_tail_4026_);
v___x_4095_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__4, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__4_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__4);
v___x_4096_ = l_Lean_indentExpr(v_00_u03c6_4028_);
v___x_4097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4095_);
lean_ctor_set(v___x_4097_, 1, v___x_4096_);
v___x_4098_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v___x_4097_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
return v___x_4098_;
}
}
else
{
lean_object* v___x_4099_; 
lean_dec(v_locals_4027_);
lean_dec(v_tail_4026_);
v___x_4099_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(v_00_u03c6_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
return v___x_4099_;
}
v___jp_4034_:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4039_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__1, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__1);
v___x_4040_ = l_Lean_indentExpr(v_00_u03c6_4028_);
v___x_4041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4039_);
lean_ctor_set(v___x_4041_, 1, v___x_4040_);
v___x_4042_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v___x_4041_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
return v___x_4042_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___boxed(lean_object* v_tail_4100_, lean_object* v_locals_4101_, lean_object* v_00_u03c6_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0(v_tail_4100_, v_locals_4101_, v_00_u03c6_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
return v_res_4108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(lean_object* v_00_u03c6_4109_, lean_object* v_path_4110_, lean_object* v_locals_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_){
_start:
{
if (lean_obj_tag(v_path_4110_) == 1)
{
lean_object* v_head_4117_; lean_object* v_tail_4118_; lean_object* v_fst_4119_; lean_object* v_snd_4120_; lean_object* v___f_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
v_head_4117_ = lean_ctor_get(v_path_4110_, 0);
lean_inc(v_head_4117_);
v_tail_4118_ = lean_ctor_get(v_path_4110_, 1);
lean_inc(v_tail_4118_);
lean_dec_ref_known(v_path_4110_, 2);
v_fst_4119_ = lean_ctor_get(v_head_4117_, 0);
lean_inc(v_fst_4119_);
v_snd_4120_ = lean_ctor_get(v_head_4117_, 1);
lean_inc(v_snd_4120_);
lean_dec(v_head_4117_);
v___f_4121_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4121_, 0, v_tail_4118_);
lean_closure_set(v___f_4121_, 1, v_locals_4111_);
v___x_4122_ = lean_unsigned_to_nat(0u);
v___x_4123_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(v_00_u03c6_4109_, v_fst_4119_, v___x_4122_, v_snd_4120_, v___f_4121_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_);
lean_dec(v_snd_4120_);
lean_dec(v_fst_4119_);
return v___x_4123_;
}
else
{
lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
lean_dec(v_locals_4111_);
lean_dec(v_path_4110_);
v___x_4124_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__1, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__1);
v___x_4125_ = l_Lean_indentExpr(v_00_u03c6_4109_);
v___x_4126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4124_);
lean_ctor_set(v___x_4126_, 1, v___x_4125_);
v___x_4127_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v___x_4126_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_);
return v___x_4127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___boxed(lean_object* v_00_u03c6_4128_, lean_object* v_path_4129_, lean_object* v_locals_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_){
_start:
{
lean_object* v_res_4136_; 
v_res_4136_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v_00_u03c6_4128_, v_path_4129_, v_locals_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_);
lean_dec(v_a_4134_);
lean_dec_ref(v_a_4133_);
lean_dec(v_a_4132_);
lean_dec_ref(v_a_4131_);
return v_res_4136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg(lean_object* v_type_4137_, lean_object* v_k_4138_, uint8_t v_cleanupAnnotations_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_){
_start:
{
lean_object* v___f_4152_; uint8_t v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
lean_inc(v___y_4146_);
lean_inc_ref(v___y_4145_);
lean_inc(v___y_4144_);
lean_inc_ref(v___y_4143_);
lean_inc(v___y_4142_);
lean_inc(v___y_4141_);
lean_inc_ref(v___y_4140_);
v___f_4152_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___redArg___lam__0___boxed), 15, 8);
lean_closure_set(v___f_4152_, 0, v_k_4138_);
lean_closure_set(v___f_4152_, 1, v___y_4140_);
lean_closure_set(v___f_4152_, 2, v___y_4141_);
lean_closure_set(v___f_4152_, 3, v___y_4142_);
lean_closure_set(v___f_4152_, 4, v___y_4143_);
lean_closure_set(v___f_4152_, 5, v___y_4144_);
lean_closure_set(v___f_4152_, 6, v___y_4145_);
lean_closure_set(v___f_4152_, 7, v___y_4146_);
v___x_4153_ = 0;
v___x_4154_ = lean_box(0);
v___x_4155_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_4153_, v___x_4154_, v_type_4137_, v___f_4152_, v_cleanupAnnotations_4139_, v___x_4153_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
if (lean_obj_tag(v___x_4155_) == 0)
{
return v___x_4155_;
}
else
{
lean_object* v_a_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4163_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4158_ = v___x_4155_;
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v___x_4155_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4161_; 
if (v_isShared_4159_ == 0)
{
v___x_4161_ = v___x_4158_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_a_4156_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg___boxed(lean_object* v_type_4164_, lean_object* v_k_4165_, lean_object* v_cleanupAnnotations_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4179_; lean_object* v_res_4180_; 
v_cleanupAnnotations_boxed_4179_ = lean_unbox(v_cleanupAnnotations_4166_);
v_res_4180_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg(v_type_4164_, v_k_4165_, v_cleanupAnnotations_boxed_4179_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec(v___y_4171_);
lean_dec_ref(v___y_4170_);
lean_dec(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1(lean_object* v_00_u03b1_4181_, lean_object* v_type_4182_, lean_object* v_k_4183_, uint8_t v_cleanupAnnotations_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
lean_object* v___x_4197_; 
v___x_4197_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg(v_type_4182_, v_k_4183_, v_cleanupAnnotations_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___boxed(lean_object* v_00_u03b1_4198_, lean_object* v_type_4199_, lean_object* v_k_4200_, lean_object* v_cleanupAnnotations_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4214_; lean_object* v_res_4215_; 
v_cleanupAnnotations_boxed_4214_ = lean_unbox(v_cleanupAnnotations_4201_);
v_res_4215_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1(v_00_u03b1_4198_, v_type_4199_, v_k_4200_, v_cleanupAnnotations_boxed_4214_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4207_);
lean_dec(v___y_4206_);
lean_dec_ref(v___y_4205_);
lean_dec(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___redArg(lean_object* v_e_4216_, lean_object* v___y_4217_){
_start:
{
uint8_t v___x_4219_; 
v___x_4219_ = l_Lean_Expr_hasMVar(v_e_4216_);
if (v___x_4219_ == 0)
{
lean_object* v___x_4220_; 
v___x_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4220_, 0, v_e_4216_);
return v___x_4220_;
}
else
{
lean_object* v___x_4221_; lean_object* v_mctx_4222_; lean_object* v___x_4223_; lean_object* v_fst_4224_; lean_object* v_snd_4225_; lean_object* v___x_4226_; lean_object* v_cache_4227_; lean_object* v_zetaDeltaFVarIds_4228_; lean_object* v_postponed_4229_; lean_object* v_diag_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4239_; 
v___x_4221_ = lean_st_ref_get(v___y_4217_);
v_mctx_4222_ = lean_ctor_get(v___x_4221_, 0);
lean_inc_ref(v_mctx_4222_);
lean_dec(v___x_4221_);
v___x_4223_ = l_Lean_instantiateMVarsCore(v_mctx_4222_, v_e_4216_);
v_fst_4224_ = lean_ctor_get(v___x_4223_, 0);
lean_inc(v_fst_4224_);
v_snd_4225_ = lean_ctor_get(v___x_4223_, 1);
lean_inc(v_snd_4225_);
lean_dec_ref(v___x_4223_);
v___x_4226_ = lean_st_ref_take(v___y_4217_);
v_cache_4227_ = lean_ctor_get(v___x_4226_, 1);
v_zetaDeltaFVarIds_4228_ = lean_ctor_get(v___x_4226_, 2);
v_postponed_4229_ = lean_ctor_get(v___x_4226_, 3);
v_diag_4230_ = lean_ctor_get(v___x_4226_, 4);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4239_ == 0)
{
lean_object* v_unused_4240_; 
v_unused_4240_ = lean_ctor_get(v___x_4226_, 0);
lean_dec(v_unused_4240_);
v___x_4232_ = v___x_4226_;
v_isShared_4233_ = v_isSharedCheck_4239_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_diag_4230_);
lean_inc(v_postponed_4229_);
lean_inc(v_zetaDeltaFVarIds_4228_);
lean_inc(v_cache_4227_);
lean_dec(v___x_4226_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4239_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4235_; 
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 0, v_snd_4225_);
v___x_4235_ = v___x_4232_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_snd_4225_);
lean_ctor_set(v_reuseFailAlloc_4238_, 1, v_cache_4227_);
lean_ctor_set(v_reuseFailAlloc_4238_, 2, v_zetaDeltaFVarIds_4228_);
lean_ctor_set(v_reuseFailAlloc_4238_, 3, v_postponed_4229_);
lean_ctor_set(v_reuseFailAlloc_4238_, 4, v_diag_4230_);
v___x_4235_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
lean_object* v___x_4236_; lean_object* v___x_4237_; 
v___x_4236_ = lean_st_ref_put(v___y_4217_, v___x_4235_);
v___x_4237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4237_, 0, v_fst_4224_);
return v___x_4237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___redArg___boxed(lean_object* v_e_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___redArg(v_e_4241_, v___y_4242_);
lean_dec(v___y_4242_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2(lean_object* v_e_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
lean_object* v___x_4258_; 
v___x_4258_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___redArg(v_e_4245_, v___y_4254_);
return v___x_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___boxed(lean_object* v_e_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_){
_start:
{
lean_object* v_res_4272_; 
v_res_4272_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2(v_e_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec(v___y_4266_);
lean_dec_ref(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec(v___y_4261_);
lean_dec_ref(v___y_4260_);
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___lam__0(lean_object* v_a_4273_, lean_object* v_hyp_4274_, lean_object* v_xs_4275_, lean_object* v_x_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_){
_start:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___x_4289_ = lean_unsigned_to_nat(0u);
v___x_4290_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(v_xs_4275_, v_a_4273_, v___x_4289_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v_a_4291_; lean_object* v_fst_4292_; lean_object* v_snd_4293_; uint8_t v___x_4294_; uint8_t v___x_4295_; uint8_t v___x_4296_; lean_object* v___x_4297_; 
v_a_4291_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_a_4291_);
lean_dec_ref_known(v___x_4290_, 1);
v_fst_4292_ = lean_ctor_get(v_a_4291_, 0);
lean_inc(v_fst_4292_);
v_snd_4293_ = lean_ctor_get(v_a_4291_, 1);
lean_inc(v_snd_4293_);
lean_dec(v_a_4291_);
v___x_4294_ = 0;
v___x_4295_ = 1;
v___x_4296_ = 1;
v___x_4297_ = l_Lean_Meta_mkLambdaFVars(v_xs_4275_, v_fst_4292_, v___x_4294_, v___x_4295_, v___x_4294_, v___x_4295_, v___x_4296_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v_a_4298_; lean_object* v___x_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4306_; 
v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
lean_inc(v_a_4298_);
lean_dec_ref_known(v___x_4297_, 1);
v___x_4299_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg(v_hyp_4274_, v_a_4298_, v___y_4285_);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4306_ == 0)
{
lean_object* v_unused_4307_; 
v_unused_4307_ = lean_ctor_get(v___x_4299_, 0);
lean_dec(v_unused_4307_);
v___x_4301_ = v___x_4299_;
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
else
{
lean_dec(v___x_4299_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
if (v_isShared_4302_ == 0)
{
lean_ctor_set(v___x_4301_, 0, v_snd_4293_);
v___x_4304_ = v___x_4301_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_snd_4293_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
return v___x_4304_;
}
}
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4315_; 
lean_dec(v_snd_4293_);
lean_dec(v_hyp_4274_);
v_a_4308_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___x_4297_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4297_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
else
{
lean_object* v_a_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4323_; 
lean_dec(v_hyp_4274_);
v_a_4316_ = lean_ctor_get(v___x_4290_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4318_ = v___x_4290_;
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_a_4316_);
lean_dec(v___x_4290_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4321_; 
if (v_isShared_4319_ == 0)
{
v___x_4321_ = v___x_4318_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4316_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
return v___x_4321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___lam__0___boxed(lean_object* v_a_4324_, lean_object* v_hyp_4325_, lean_object* v_xs_4326_, lean_object* v_x_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___lam__0(v_a_4324_, v_hyp_4325_, v_xs_4326_, v_x_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
lean_dec(v___y_4334_);
lean_dec_ref(v___y_4333_);
lean_dec(v___y_4332_);
lean_dec_ref(v___y_4331_);
lean_dec(v___y_4330_);
lean_dec(v___y_4329_);
lean_dec_ref(v___y_4328_);
lean_dec_ref(v_x_4327_);
lean_dec_ref(v_xs_4326_);
lean_dec_ref(v_a_4324_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg(lean_object* v_jp_4341_, size_t v_sz_4342_, size_t v_i_4343_, lean_object* v_bs_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_){
_start:
{
uint8_t v___x_4350_; 
v___x_4350_ = lean_usize_dec_lt(v_i_4343_, v_sz_4342_);
if (v___x_4350_ == 0)
{
lean_object* v___x_4351_; 
v___x_4351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4351_, 0, v_bs_4344_);
return v___x_4351_;
}
else
{
lean_object* v_v_4352_; lean_object* v___x_4353_; lean_object* v_bs_x27_4354_; lean_object* v___x_4355_; 
v_v_4352_ = lean_array_uget(v_bs_4344_, v_i_4343_);
v___x_4353_ = lean_unsigned_to_nat(0u);
v_bs_x27_4354_ = lean_array_uset(v_bs_4344_, v_i_4343_, v___x_4353_);
lean_inc(v_v_4352_);
v___x_4355_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals(v_jp_4341_, v_v_4352_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; lean_object* v___x_4357_; size_t v___x_4358_; size_t v___x_4359_; lean_object* v___x_4360_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_a_4356_);
lean_dec_ref_known(v___x_4355_, 1);
v___x_4357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4357_, 0, v_v_4352_);
lean_ctor_set(v___x_4357_, 1, v_a_4356_);
v___x_4358_ = ((size_t)1ULL);
v___x_4359_ = lean_usize_add(v_i_4343_, v___x_4358_);
v___x_4360_ = lean_array_uset(v_bs_x27_4354_, v_i_4343_, v___x_4357_);
v_i_4343_ = v___x_4359_;
v_bs_4344_ = v___x_4360_;
goto _start;
}
else
{
lean_object* v_a_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4369_; 
lean_dec_ref(v_bs_x27_4354_);
lean_dec(v_v_4352_);
v_a_4362_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4369_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4369_ == 0)
{
v___x_4364_ = v___x_4355_;
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_a_4362_);
lean_dec(v___x_4355_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v___x_4367_; 
if (v_isShared_4365_ == 0)
{
v___x_4367_ = v___x_4364_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_a_4362_);
v___x_4367_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
return v___x_4367_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg___boxed(lean_object* v_jp_4370_, lean_object* v_sz_4371_, lean_object* v_i_4372_, lean_object* v_bs_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
size_t v_sz_boxed_4379_; size_t v_i_boxed_4380_; lean_object* v_res_4381_; 
v_sz_boxed_4379_ = lean_unbox_usize(v_sz_4371_);
lean_dec(v_sz_4371_);
v_i_boxed_4380_ = lean_unbox_usize(v_i_4372_);
lean_dec(v_i_4372_);
v_res_4381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg(v_jp_4370_, v_sz_boxed_4379_, v_i_boxed_4380_, v_bs_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
lean_dec_ref(v_jp_4370_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___lam__0(lean_object* v_proof_4382_, lean_object* v_snd_4383_, lean_object* v_snd_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_){
_start:
{
lean_object* v___x_4397_; 
lean_inc(v_proof_4382_);
v___x_4397_ = l_Lean_MVarId_getType(v_proof_4382_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
if (lean_obj_tag(v___x_4397_) == 0)
{
lean_object* v_a_4398_; lean_object* v___x_4399_; 
v_a_4398_ = lean_ctor_get(v___x_4397_, 0);
lean_inc(v_a_4398_);
lean_dec_ref_known(v___x_4397_, 1);
v___x_4399_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___redArg(v_a_4398_, v___y_4393_);
if (lean_obj_tag(v___x_4399_) == 0)
{
lean_object* v_a_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; 
v_a_4400_ = lean_ctor_get(v___x_4399_, 0);
lean_inc(v_a_4400_);
lean_dec_ref_known(v___x_4399_, 1);
v___x_4401_ = lean_array_to_list(v_snd_4383_);
v___x_4402_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v_a_4400_, v_snd_4384_, v___x_4401_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_object* v_a_4403_; lean_object* v___x_4404_; 
v_a_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc(v_a_4403_);
lean_dec_ref_known(v___x_4402_, 1);
v___x_4404_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg(v_proof_4382_, v_a_4403_, v___y_4393_);
return v___x_4404_;
}
else
{
lean_object* v_a_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4412_; 
lean_dec(v_proof_4382_);
v_a_4405_ = lean_ctor_get(v___x_4402_, 0);
v_isSharedCheck_4412_ = !lean_is_exclusive(v___x_4402_);
if (v_isSharedCheck_4412_ == 0)
{
v___x_4407_ = v___x_4402_;
v_isShared_4408_ = v_isSharedCheck_4412_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_a_4405_);
lean_dec(v___x_4402_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4412_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___x_4410_; 
if (v_isShared_4408_ == 0)
{
v___x_4410_ = v___x_4407_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v_a_4405_);
v___x_4410_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
return v___x_4410_;
}
}
}
}
else
{
lean_object* v_a_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4420_; 
lean_dec(v_snd_4384_);
lean_dec_ref(v_snd_4383_);
lean_dec(v_proof_4382_);
v_a_4413_ = lean_ctor_get(v___x_4399_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4399_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4415_ = v___x_4399_;
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_a_4413_);
lean_dec(v___x_4399_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v___x_4418_; 
if (v_isShared_4416_ == 0)
{
v___x_4418_ = v___x_4415_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4413_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
return v___x_4418_;
}
}
}
}
else
{
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4428_; 
lean_dec(v_snd_4384_);
lean_dec_ref(v_snd_4383_);
lean_dec(v_proof_4382_);
v_a_4421_ = lean_ctor_get(v___x_4397_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4397_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4423_ = v___x_4397_;
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4397_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4426_; 
if (v_isShared_4424_ == 0)
{
v___x_4426_ = v___x_4423_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_a_4421_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___lam__0___boxed(lean_object* v_proof_4429_, lean_object* v_snd_4430_, lean_object* v_snd_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_){
_start:
{
lean_object* v_res_4444_; 
v_res_4444_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___lam__0(v_proof_4429_, v_snd_4430_, v_snd_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
lean_dec(v___y_4442_);
lean_dec_ref(v___y_4441_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3(lean_object* v_as_4445_, size_t v_sz_4446_, size_t v_i_4447_, lean_object* v_b_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_){
_start:
{
uint8_t v___x_4461_; 
v___x_4461_ = lean_usize_dec_lt(v_i_4447_, v_sz_4446_);
if (v___x_4461_ == 0)
{
lean_object* v___x_4462_; 
v___x_4462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4462_, 0, v_b_4448_);
return v___x_4462_;
}
else
{
lean_object* v_a_4463_; lean_object* v_fst_4464_; lean_object* v_fst_4465_; lean_object* v_snd_4466_; lean_object* v_snd_4467_; lean_object* v_proof_4468_; lean_object* v___x_4469_; lean_object* v___f_4470_; lean_object* v___x_4471_; 
v_a_4463_ = lean_array_uget_borrowed(v_as_4445_, v_i_4447_);
v_fst_4464_ = lean_ctor_get(v_a_4463_, 0);
v_fst_4465_ = lean_ctor_get(v_fst_4464_, 0);
v_snd_4466_ = lean_ctor_get(v_a_4463_, 1);
v_snd_4467_ = lean_ctor_get(v_fst_4464_, 1);
v_proof_4468_ = lean_ctor_get(v_fst_4465_, 0);
v___x_4469_ = lean_box(0);
lean_inc(v_snd_4466_);
lean_inc(v_snd_4467_);
lean_inc_n(v_proof_4468_, 2);
v___f_4470_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___lam__0___boxed), 15, 3);
lean_closure_set(v___f_4470_, 0, v_proof_4468_);
lean_closure_set(v___f_4470_, 1, v_snd_4467_);
lean_closure_set(v___f_4470_, 2, v_snd_4466_);
v___x_4471_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg(v_proof_4468_, v___f_4470_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_);
if (lean_obj_tag(v___x_4471_) == 0)
{
size_t v___x_4472_; size_t v___x_4473_; 
lean_dec_ref_known(v___x_4471_, 1);
v___x_4472_ = ((size_t)1ULL);
v___x_4473_ = lean_usize_add(v_i_4447_, v___x_4472_);
v_i_4447_ = v___x_4473_;
v_b_4448_ = v___x_4469_;
goto _start;
}
else
{
return v___x_4471_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___boxed(lean_object* v_as_4475_, lean_object* v_sz_4476_, lean_object* v_i_4477_, lean_object* v_b_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_){
_start:
{
size_t v_sz_boxed_4491_; size_t v_i_boxed_4492_; lean_object* v_res_4493_; 
v_sz_boxed_4491_ = lean_unbox_usize(v_sz_4476_);
lean_dec(v_sz_4476_);
v_i_boxed_4492_ = lean_unbox_usize(v_i_4477_);
lean_dec(v_i_4477_);
v_res_4493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3(v_as_4475_, v_sz_boxed_4491_, v_i_boxed_4492_, v_b_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec(v___y_4485_);
lean_dec_ref(v___y_4484_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec_ref(v_as_4475_);
return v_res_4493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint(lean_object* v_jp_4494_, lean_object* v_jumps_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_){
_start:
{
size_t v_sz_4508_; size_t v___x_4509_; lean_object* v___x_4510_; 
v_sz_4508_ = lean_array_size(v_jumps_4495_);
v___x_4509_ = ((size_t)0ULL);
v___x_4510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg(v_jp_4494_, v_sz_4508_, v___x_4509_, v_jumps_4495_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_);
if (lean_obj_tag(v___x_4510_) == 0)
{
lean_object* v_a_4511_; lean_object* v_hyp_4512_; lean_object* v___f_4513_; lean_object* v___x_4514_; 
v_a_4511_ = lean_ctor_get(v___x_4510_, 0);
lean_inc_n(v_a_4511_, 2);
lean_dec_ref_known(v___x_4510_, 1);
v_hyp_4512_ = lean_ctor_get(v_jp_4494_, 2);
lean_inc_n(v_hyp_4512_, 2);
lean_dec_ref(v_jp_4494_);
v___f_4513_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___lam__0___boxed), 16, 2);
lean_closure_set(v___f_4513_, 0, v_a_4511_);
lean_closure_set(v___f_4513_, 1, v_hyp_4512_);
v___x_4514_ = l_Lean_MVarId_getType(v_hyp_4512_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_);
if (lean_obj_tag(v___x_4514_) == 0)
{
lean_object* v_a_4515_; uint8_t v___x_4516_; lean_object* v___x_4517_; 
v_a_4515_ = lean_ctor_get(v___x_4514_, 0);
lean_inc(v_a_4515_);
lean_dec_ref_known(v___x_4514_, 1);
v___x_4516_ = 0;
v___x_4517_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg(v_a_4515_, v___f_4513_, v___x_4516_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_a_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; size_t v_sz_4521_; lean_object* v___x_4522_; 
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
lean_inc(v_a_4518_);
lean_dec_ref_known(v___x_4517_, 1);
v___x_4519_ = l_Array_zip___redArg(v_a_4511_, v_a_4518_);
lean_dec(v_a_4518_);
lean_dec(v_a_4511_);
v___x_4520_ = lean_box(0);
v_sz_4521_ = lean_array_size(v___x_4519_);
v___x_4522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3(v___x_4519_, v_sz_4521_, v___x_4509_, v___x_4520_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_);
lean_dec_ref(v___x_4519_);
if (lean_obj_tag(v___x_4522_) == 0)
{
lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4529_; 
v_isSharedCheck_4529_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4529_ == 0)
{
lean_object* v_unused_4530_; 
v_unused_4530_ = lean_ctor_get(v___x_4522_, 0);
lean_dec(v_unused_4530_);
v___x_4524_ = v___x_4522_;
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
else
{
lean_dec(v___x_4522_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
lean_object* v___x_4527_; 
if (v_isShared_4525_ == 0)
{
lean_ctor_set(v___x_4524_, 0, v___x_4520_);
v___x_4527_ = v___x_4524_;
goto v_reusejp_4526_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v___x_4520_);
v___x_4527_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4526_;
}
v_reusejp_4526_:
{
return v___x_4527_;
}
}
}
else
{
return v___x_4522_;
}
}
else
{
lean_object* v_a_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4538_; 
lean_dec(v_a_4511_);
v_a_4531_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4538_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4533_ = v___x_4517_;
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_a_4531_);
lean_dec(v___x_4517_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___x_4536_; 
if (v_isShared_4534_ == 0)
{
v___x_4536_ = v___x_4533_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4531_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
}
}
}
}
else
{
lean_object* v_a_4539_; lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4546_; 
lean_dec_ref(v___f_4513_);
lean_dec(v_a_4511_);
v_a_4539_ = lean_ctor_get(v___x_4514_, 0);
v_isSharedCheck_4546_ = !lean_is_exclusive(v___x_4514_);
if (v_isSharedCheck_4546_ == 0)
{
v___x_4541_ = v___x_4514_;
v_isShared_4542_ = v_isSharedCheck_4546_;
goto v_resetjp_4540_;
}
else
{
lean_inc(v_a_4539_);
lean_dec(v___x_4514_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4546_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v___x_4544_; 
if (v_isShared_4542_ == 0)
{
v___x_4544_ = v___x_4541_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v_a_4539_);
v___x_4544_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
return v___x_4544_;
}
}
}
}
else
{
lean_object* v_a_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4554_; 
lean_dec_ref(v_jp_4494_);
v_a_4547_ = lean_ctor_get(v___x_4510_, 0);
v_isSharedCheck_4554_ = !lean_is_exclusive(v___x_4510_);
if (v_isSharedCheck_4554_ == 0)
{
v___x_4549_ = v___x_4510_;
v_isShared_4550_ = v_isSharedCheck_4554_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_a_4547_);
lean_dec(v___x_4510_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4554_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
lean_object* v___x_4552_; 
if (v_isShared_4550_ == 0)
{
v___x_4552_ = v___x_4549_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_a_4547_);
v___x_4552_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
return v___x_4552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___boxed(lean_object* v_jp_4555_, lean_object* v_jumps_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_){
_start:
{
lean_object* v_res_4569_; 
v_res_4569_ = l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint(v_jp_4555_, v_jumps_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
lean_dec(v_a_4565_);
lean_dec_ref(v_a_4564_);
lean_dec(v_a_4563_);
lean_dec_ref(v_a_4562_);
lean_dec(v_a_4561_);
lean_dec_ref(v_a_4560_);
lean_dec(v_a_4559_);
lean_dec(v_a_4558_);
lean_dec_ref(v_a_4557_);
return v_res_4569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0(lean_object* v_jp_4570_, size_t v_sz_4571_, size_t v_i_4572_, lean_object* v_bs_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_){
_start:
{
lean_object* v___x_4586_; 
v___x_4586_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg(v_jp_4570_, v_sz_4571_, v_i_4572_, v_bs_4573_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
return v___x_4586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___boxed(lean_object* v_jp_4587_, lean_object* v_sz_4588_, lean_object* v_i_4589_, lean_object* v_bs_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_){
_start:
{
size_t v_sz_boxed_4603_; size_t v_i_boxed_4604_; lean_object* v_res_4605_; 
v_sz_boxed_4603_ = lean_unbox_usize(v_sz_4588_);
lean_dec(v_sz_4588_);
v_i_boxed_4604_ = lean_unbox_usize(v_i_4589_);
lean_dec(v_i_4589_);
v_res_4605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0(v_jp_4587_, v_sz_boxed_4603_, v_i_boxed_4604_, v_bs_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
lean_dec(v___y_4599_);
lean_dec_ref(v___y_4598_);
lean_dec(v___y_4597_);
lean_dec_ref(v___y_4596_);
lean_dec(v___y_4595_);
lean_dec_ref(v___y_4594_);
lean_dec(v___y_4593_);
lean_dec(v___y_4592_);
lean_dec_ref(v___y_4591_);
lean_dec_ref(v_jp_4587_);
return v_res_4605_;
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
