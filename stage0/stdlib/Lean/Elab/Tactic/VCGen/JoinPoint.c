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
size_t v_x_19576__boxed_1837_; size_t v_x_19577__boxed_1838_; lean_object* v_res_1839_; 
v_x_19576__boxed_1837_ = lean_unbox_usize(v_x_1833_);
lean_dec(v_x_1833_);
v_x_19577__boxed_1838_ = lean_unbox_usize(v_x_1834_);
lean_dec(v_x_1834_);
v_res_1839_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3___redArg(v_x_1832_, v_x_19576__boxed_1837_, v_x_19577__boxed_1838_, v_x_1835_, v_x_1836_);
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
lean_object* v___x_1851_; lean_object* v_mctx_1852_; lean_object* v_cache_1853_; lean_object* v_zetaDeltaFVarIds_1854_; lean_object* v_postponed_1855_; lean_object* v_diag_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1885_; 
v___x_1851_ = lean_st_ref_take(v___y_1849_);
v_mctx_1852_ = lean_ctor_get(v___x_1851_, 0);
v_cache_1853_ = lean_ctor_get(v___x_1851_, 1);
v_zetaDeltaFVarIds_1854_ = lean_ctor_get(v___x_1851_, 2);
v_postponed_1855_ = lean_ctor_get(v___x_1851_, 3);
v_diag_1856_ = lean_ctor_get(v___x_1851_, 4);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1858_ = v___x_1851_;
v_isShared_1859_ = v_isSharedCheck_1885_;
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
v_isShared_1859_ = v_isSharedCheck_1885_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v_depth_1860_; lean_object* v_levelAssignDepth_1861_; lean_object* v_lmvarCounter_1862_; lean_object* v_mvarCounter_1863_; lean_object* v_lDecls_1864_; lean_object* v_decls_1865_; lean_object* v_userNames_1866_; lean_object* v_lAssignment_1867_; lean_object* v_eAssignment_1868_; lean_object* v_dAssignment_1869_; lean_object* v_instanceTypedMVars_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1884_; 
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
v_isSharedCheck_1884_ = !lean_is_exclusive(v_mctx_1852_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1872_ = v_mctx_1852_;
v_isShared_1873_ = v_isSharedCheck_1884_;
goto v_resetjp_1871_;
}
else
{
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
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1884_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1877_; 
v___x_1874_ = lean_box(0);
v___x_1875_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2___redArg(v_eAssignment_1868_, v_mvarId_1847_, v_val_1848_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 8, v___x_1875_);
v___x_1877_ = v___x_1872_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_depth_1860_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_levelAssignDepth_1861_);
lean_ctor_set(v_reuseFailAlloc_1883_, 2, v_lmvarCounter_1862_);
lean_ctor_set(v_reuseFailAlloc_1883_, 3, v_mvarCounter_1863_);
lean_ctor_set(v_reuseFailAlloc_1883_, 4, v_lDecls_1864_);
lean_ctor_set(v_reuseFailAlloc_1883_, 5, v_decls_1865_);
lean_ctor_set(v_reuseFailAlloc_1883_, 6, v_userNames_1866_);
lean_ctor_set(v_reuseFailAlloc_1883_, 7, v_lAssignment_1867_);
lean_ctor_set(v_reuseFailAlloc_1883_, 8, v___x_1875_);
lean_ctor_set(v_reuseFailAlloc_1883_, 9, v_dAssignment_1869_);
lean_ctor_set(v_reuseFailAlloc_1883_, 10, v_instanceTypedMVars_1870_);
v___x_1877_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1879_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1877_);
v___x_1879_ = v___x_1858_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_cache_1853_);
lean_ctor_set(v_reuseFailAlloc_1882_, 2, v_zetaDeltaFVarIds_1854_);
lean_ctor_set(v_reuseFailAlloc_1882_, 3, v_postponed_1855_);
lean_ctor_set(v_reuseFailAlloc_1882_, 4, v_diag_1856_);
v___x_1879_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_st_ref_put(v___y_1849_, v___x_1879_);
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1874_);
return v___x_1881_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg___boxed(lean_object* v_mvarId_1886_, lean_object* v_val_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg(v_mvarId_1886_, v_val_1887_, v___y_1888_);
lean_dec(v___y_1888_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__4(lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_x_1894_){
_start:
{
if (lean_obj_tag(v_x_1894_) == 0)
{
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
return v_x_1894_;
}
else
{
lean_object* v_key_1895_; lean_object* v_value_1896_; lean_object* v_tail_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1921_; 
v_key_1895_ = lean_ctor_get(v_x_1894_, 0);
v_value_1896_ = lean_ctor_get(v_x_1894_, 1);
v_tail_1897_ = lean_ctor_get(v_x_1894_, 2);
v_isSharedCheck_1921_ = !lean_is_exclusive(v_x_1894_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1899_ = v_x_1894_;
v_isShared_1900_ = v_isSharedCheck_1921_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_tail_1897_);
lean_inc(v_value_1896_);
lean_inc(v_key_1895_);
lean_dec(v_x_1894_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1921_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
uint8_t v___x_1901_; 
v___x_1901_ = l_Lean_instBEqMVarId_beq(v_key_1895_, v_a_1893_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1904_; 
v___x_1902_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__4(v_a_1891_, v_a_1892_, v_a_1893_, v_tail_1897_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 2, v___x_1902_);
v___x_1904_ = v___x_1899_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_key_1895_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v_value_1896_);
lean_ctor_set(v_reuseFailAlloc_1905_, 2, v___x_1902_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
else
{
lean_object* v_fst_1906_; lean_object* v_snd_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1920_; 
lean_dec(v_key_1895_);
v_fst_1906_ = lean_ctor_get(v_value_1896_, 0);
v_snd_1907_ = lean_ctor_get(v_value_1896_, 1);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_value_1896_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1909_ = v_value_1896_;
v_isShared_1910_ = v_isSharedCheck_1920_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_snd_1907_);
lean_inc(v_fst_1906_);
lean_dec(v_value_1896_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1920_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1915_; 
v___x_1911_ = l_Lean_Expr_mvarId_x21(v_a_1891_);
v___x_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
lean_ctor_set(v___x_1912_, 1, v_a_1892_);
v___x_1913_ = lean_array_push(v_snd_1907_, v___x_1912_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 1, v___x_1913_);
v___x_1915_ = v___x_1909_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_fst_1906_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1917_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 1, v___x_1915_);
lean_ctor_set(v___x_1899_, 0, v_a_1893_);
v___x_1917_ = v___x_1899_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1893_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v___x_1915_);
lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_tail_1897_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__4___boxed(lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_x_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__4(v_a_1922_, v_a_1923_, v_a_1924_, v_x_1925_);
lean_dec_ref(v_a_1922_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3(lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_m_1929_, lean_object* v_a_1930_){
_start:
{
lean_object* v_size_1931_; lean_object* v_buckets_1932_; lean_object* v___x_1933_; uint64_t v___x_1934_; uint64_t v___x_1935_; uint64_t v___x_1936_; uint64_t v_fold_1937_; uint64_t v___x_1938_; uint64_t v___x_1939_; uint64_t v___x_1940_; size_t v___x_1941_; size_t v___x_1942_; size_t v___x_1943_; size_t v___x_1944_; size_t v___x_1945_; lean_object* v_bucket_1946_; uint8_t v___x_1947_; 
v_size_1931_ = lean_ctor_get(v_m_1929_, 0);
v_buckets_1932_ = lean_ctor_get(v_m_1929_, 1);
v___x_1933_ = lean_array_get_size(v_buckets_1932_);
v___x_1934_ = l_Lean_instHashableMVarId_hash(v_a_1930_);
v___x_1935_ = 32ULL;
v___x_1936_ = lean_uint64_shift_right(v___x_1934_, v___x_1935_);
v_fold_1937_ = lean_uint64_xor(v___x_1934_, v___x_1936_);
v___x_1938_ = 16ULL;
v___x_1939_ = lean_uint64_shift_right(v_fold_1937_, v___x_1938_);
v___x_1940_ = lean_uint64_xor(v_fold_1937_, v___x_1939_);
v___x_1941_ = lean_uint64_to_usize(v___x_1940_);
v___x_1942_ = lean_usize_of_nat(v___x_1933_);
v___x_1943_ = ((size_t)1ULL);
v___x_1944_ = lean_usize_sub(v___x_1942_, v___x_1943_);
v___x_1945_ = lean_usize_land(v___x_1941_, v___x_1944_);
v_bucket_1946_ = lean_array_uget_borrowed(v_buckets_1932_, v___x_1945_);
v___x_1947_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__5_spec__7___redArg(v_a_1930_, v_bucket_1946_);
if (v___x_1947_ == 0)
{
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1928_);
return v_m_1929_;
}
else
{
lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1958_; 
lean_inc(v_bucket_1946_);
lean_inc_ref(v_buckets_1932_);
lean_inc(v_size_1931_);
v_isSharedCheck_1958_ = !lean_is_exclusive(v_m_1929_);
if (v_isSharedCheck_1958_ == 0)
{
lean_object* v_unused_1959_; lean_object* v_unused_1960_; 
v_unused_1959_ = lean_ctor_get(v_m_1929_, 1);
lean_dec(v_unused_1959_);
v_unused_1960_ = lean_ctor_get(v_m_1929_, 0);
lean_dec(v_unused_1960_);
v___x_1949_ = v_m_1929_;
v_isShared_1950_ = v_isSharedCheck_1958_;
goto v_resetjp_1948_;
}
else
{
lean_dec(v_m_1929_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1958_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1951_; lean_object* v_buckets_1952_; lean_object* v_bucket_1953_; lean_object* v___x_1954_; lean_object* v___x_1956_; 
v___x_1951_ = lean_box(0);
v_buckets_1952_ = lean_array_uset(v_buckets_1932_, v___x_1945_, v___x_1951_);
v_bucket_1953_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3_spec__4(v_a_1927_, v_a_1928_, v_a_1930_, v_bucket_1946_);
v___x_1954_ = lean_array_uset(v_buckets_1952_, v___x_1945_, v_bucket_1953_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 1, v___x_1954_);
v___x_1956_ = v___x_1949_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_size_1931_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v___x_1954_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3___boxed(lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_m_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3(v_a_1961_, v_a_1962_, v_m_1963_, v_a_1964_);
lean_dec_ref(v_a_1961_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg(size_t v_sz_1966_, size_t v_i_1967_, lean_object* v_bs_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
uint8_t v___x_1976_; 
v___x_1976_ = lean_usize_dec_lt(v_i_1967_, v_sz_1966_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; 
v___x_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1977_, 0, v_bs_1968_);
return v___x_1977_;
}
else
{
lean_object* v_v_1978_; lean_object* v___x_1979_; lean_object* v_bs_x27_1980_; lean_object* v___x_1981_; 
v_v_1978_ = lean_array_uget(v_bs_1968_, v_i_1967_);
v___x_1979_ = lean_unsigned_to_nat(0u);
v_bs_x27_1980_ = lean_array_uset(v_bs_1968_, v_i_1967_, v___x_1979_);
v___x_1981_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v_v_1978_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; size_t v___x_1983_; size_t v___x_1984_; lean_object* v___x_1985_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref_known(v___x_1981_, 1);
v___x_1983_ = ((size_t)1ULL);
v___x_1984_ = lean_usize_add(v_i_1967_, v___x_1983_);
v___x_1985_ = lean_array_uset(v_bs_x27_1980_, v_i_1967_, v_a_1982_);
v_i_1967_ = v___x_1984_;
v_bs_1968_ = v___x_1985_;
goto _start;
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec_ref(v_bs_x27_1980_);
v_a_1987_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1981_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1981_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg___boxed(lean_object* v_sz_1995_, lean_object* v_i_1996_, lean_object* v_bs_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
size_t v_sz_boxed_2005_; size_t v_i_boxed_2006_; lean_object* v_res_2007_; 
v_sz_boxed_2005_ = lean_unbox_usize(v_sz_1995_);
lean_dec(v_sz_1995_);
v_i_boxed_2006_ = lean_unbox_usize(v_i_1996_);
lean_dec(v_i_1996_);
v_res_2007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg(v_sz_boxed_2005_, v_i_boxed_2006_, v_bs_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v_res_2007_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2008_; lean_object* v_dummy_2009_; 
v___x_2008_ = lean_box(0);
v_dummy_2009_ = l_Lean_Expr_sort___override(v___x_2008_);
return v_dummy_2009_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__2));
v___x_2014_ = l_Lean_stringToMessageData(v___x_2013_);
return v___x_2014_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__4));
v___x_2017_ = l_Lean_stringToMessageData(v___x_2016_);
return v___x_2017_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__6));
v___x_2020_ = l_Lean_stringToMessageData(v___x_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0(lean_object* v_info_2021_, lean_object* v___x_2022_, lean_object* v_val_2023_, lean_object* v_goal_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v___x_2128_; 
lean_inc(v_goal_2024_);
v___x_2128_ = l_Lean_MVarId_getType(v_goal_2024_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2175_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2131_ = v___x_2128_;
v_isShared_2132_ = v_isSharedCheck_2175_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2128_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2175_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2133_ = l_Lean_Expr_cleanupAnnotations(v_a_2129_);
lean_dec(v_a_2129_);
v___x_2134_ = l_Lean_Expr_isApp(v___x_2133_);
if (v___x_2134_ == 0)
{
lean_dec_ref(v___x_2133_);
lean_del_object(v___x_2131_);
lean_dec(v_goal_2024_);
lean_dec_ref(v_val_2023_);
lean_dec_ref(v___x_2022_);
goto v___jp_2037_;
}
else
{
lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2135_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2133_);
lean_dec_ref(v___x_2133_);
v___x_2136_ = l_Lean_Expr_isApp(v___x_2135_);
if (v___x_2136_ == 0)
{
lean_dec_ref(v___x_2135_);
lean_del_object(v___x_2131_);
lean_dec(v_goal_2024_);
lean_dec_ref(v_val_2023_);
lean_dec_ref(v___x_2022_);
goto v___jp_2037_;
}
else
{
lean_object* v___x_2137_; uint8_t v___x_2138_; 
v___x_2137_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2135_);
v___x_2138_ = l_Lean_Expr_isApp(v___x_2137_);
if (v___x_2138_ == 0)
{
lean_dec_ref(v___x_2137_);
lean_dec_ref(v___x_2135_);
lean_del_object(v___x_2131_);
lean_dec(v_goal_2024_);
lean_dec_ref(v_val_2023_);
lean_dec_ref(v___x_2022_);
goto v___jp_2037_;
}
else
{
lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2139_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2137_);
lean_dec_ref(v___x_2137_);
v___x_2140_ = l_Lean_Expr_isApp(v___x_2139_);
if (v___x_2140_ == 0)
{
lean_dec_ref(v___x_2139_);
lean_dec_ref(v___x_2135_);
lean_del_object(v___x_2131_);
lean_dec(v_goal_2024_);
lean_dec_ref(v_val_2023_);
lean_dec_ref(v___x_2022_);
goto v___jp_2037_;
}
else
{
lean_object* v___x_2141_; lean_object* v___x_2142_; uint8_t v___x_2143_; 
v___x_2141_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2139_);
lean_dec_ref(v___x_2139_);
v___x_2142_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_registerJoinPoint___lam__3___closed__2));
v___x_2143_ = l_Lean_Expr_isConstOf(v___x_2141_, v___x_2142_);
lean_dec_ref(v___x_2141_);
if (v___x_2143_ == 0)
{
lean_dec_ref(v___x_2135_);
lean_del_object(v___x_2131_);
lean_dec(v_goal_2024_);
lean_dec_ref(v_val_2023_);
lean_dec_ref(v___x_2022_);
goto v___jp_2037_;
}
else
{
lean_object* v_arg_2144_; lean_object* v_top_2145_; lean_object* v_numStates_2146_; uint8_t v___x_2147_; 
v_arg_2144_ = lean_ctor_get(v___x_2135_, 1);
lean_inc_ref(v_arg_2144_);
lean_dec_ref(v___x_2135_);
v_top_2145_ = lean_ctor_get(v_val_2023_, 1);
v_numStates_2146_ = lean_ctor_get(v_val_2023_, 4);
v___x_2147_ = lean_expr_eqv(v_arg_2144_, v_top_2145_);
lean_dec_ref(v_arg_2144_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
lean_dec(v_goal_2024_);
lean_dec_ref(v_val_2023_);
lean_dec_ref(v___x_2022_);
v___x_2148_ = lean_box(0);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v___x_2148_);
v___x_2150_ = v___x_2131_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
else
{
lean_object* v_excessArgs_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; 
lean_del_object(v___x_2131_);
v_excessArgs_2152_ = lean_ctor_get(v_info_2021_, 3);
v___x_2153_ = lean_array_get_size(v_excessArgs_2152_);
v___x_2154_ = lean_nat_dec_eq(v___x_2153_, v_numStates_2146_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_inc(v_numStates_2146_);
lean_dec(v_goal_2024_);
lean_dec_ref(v_val_2023_);
v___x_2155_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__3, &l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__3);
v___x_2156_ = l_Lean_indentExpr(v___x_2022_);
v___x_2157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2155_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__5, &l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__5);
v___x_2159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2157_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = l_Nat_reprFast(v_numStates_2146_);
v___x_2161_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
v___x_2162_ = l_Lean_MessageData_ofFormat(v___x_2161_);
v___x_2163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2159_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__7, &l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__7);
v___x_2165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2163_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2___redArg(v___x_2165_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2166_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2166_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
else
{
goto v___jp_2040_;
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
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec(v_goal_2024_);
lean_dec_ref(v_val_2023_);
lean_dec_ref(v___x_2022_);
v_a_2176_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2128_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2128_);
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
v___jp_2037_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = lean_box(0);
v___x_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
return v___x_2039_;
}
v___jp_2040_:
{
lean_object* v_excessArgs_2041_; lean_object* v_nargs_2042_; lean_object* v_dummy_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; size_t v_sz_2049_; size_t v___x_2050_; lean_object* v___x_2051_; 
v_excessArgs_2041_ = lean_ctor_get(v_info_2021_, 3);
v_nargs_2042_ = l_Lean_Expr_getAppNumArgs(v___x_2022_);
v_dummy_2043_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__0, &l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__0);
lean_inc(v_nargs_2042_);
v___x_2044_ = lean_mk_array(v_nargs_2042_, v_dummy_2043_);
v___x_2045_ = lean_unsigned_to_nat(1u);
v___x_2046_ = lean_nat_sub(v_nargs_2042_, v___x_2045_);
lean_dec(v_nargs_2042_);
v___x_2047_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_2022_, v___x_2044_, v___x_2046_);
v___x_2048_ = l_Array_append___redArg(v___x_2047_, v_excessArgs_2041_);
v_sz_2049_ = lean_array_size(v___x_2048_);
v___x_2050_ = ((size_t)0ULL);
v___x_2051_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg(v_sz_2049_, v___x_2050_, v___x_2048_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v_spec_2053_; lean_object* v_hyp_2054_; lean_object* v_rhsGoal_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2051_, 1);
v_spec_2053_ = lean_ctor_get(v_val_2023_, 0);
lean_inc_ref(v_spec_2053_);
v_hyp_2054_ = lean_ctor_get(v_val_2023_, 2);
lean_inc(v_hyp_2054_);
v_rhsGoal_2055_ = lean_ctor_get(v_val_2023_, 3);
lean_inc(v_rhsGoal_2055_);
lean_dec_ref(v_val_2023_);
v___x_2056_ = l_Lean_Expr_mvar___override(v_hyp_2054_);
v___x_2057_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0(v___x_2056_, v_a_2052_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref_known(v___x_2057_, 1);
v___x_2059_ = lean_box(0);
v___x_2060_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2058_, v___x_2059_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc_n(v_a_2061_, 2);
lean_dec_ref_known(v___x_2060_, 1);
lean_inc(v_a_2052_);
v___x_2062_ = lean_array_push(v_a_2052_, v_a_2061_);
v___x_2063_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__0(v_spec_2053_, v___x_2062_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
lean_dec_ref(v___x_2062_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2094_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref_known(v___x_2063_, 1);
v___x_2065_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg(v_goal_2024_, v_a_2064_, v___y_2033_);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2094_ == 0)
{
lean_object* v_unused_2095_; 
v_unused_2095_ = lean_ctor_get(v___x_2065_, 0);
lean_dec(v_unused_2095_);
v___x_2067_ = v___x_2065_;
v_isShared_2068_ = v_isSharedCheck_2094_;
goto v_resetjp_2066_;
}
else
{
lean_dec(v___x_2065_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2094_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v_specBackwardRuleCache_2070_; lean_object* v_splitBackwardRuleCache_2071_; lean_object* v_latticeBackwardRuleCache_2072_; lean_object* v_frameBackwardRuleCache_2073_; lean_object* v_frameDB_2074_; lean_object* v_invariants_2075_; lean_object* v_vcs_2076_; lean_object* v_simpState_2077_; lean_object* v_fuel_2078_; lean_object* v_inlineHandledInvariants_2079_; lean_object* v_pendingJoinPoints_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2093_; 
v___x_2069_ = lean_st_ref_take(v___y_2026_);
v_specBackwardRuleCache_2070_ = lean_ctor_get(v___x_2069_, 0);
v_splitBackwardRuleCache_2071_ = lean_ctor_get(v___x_2069_, 1);
v_latticeBackwardRuleCache_2072_ = lean_ctor_get(v___x_2069_, 2);
v_frameBackwardRuleCache_2073_ = lean_ctor_get(v___x_2069_, 3);
v_frameDB_2074_ = lean_ctor_get(v___x_2069_, 4);
v_invariants_2075_ = lean_ctor_get(v___x_2069_, 5);
v_vcs_2076_ = lean_ctor_get(v___x_2069_, 6);
v_simpState_2077_ = lean_ctor_get(v___x_2069_, 7);
v_fuel_2078_ = lean_ctor_get(v___x_2069_, 8);
v_inlineHandledInvariants_2079_ = lean_ctor_get(v___x_2069_, 9);
v_pendingJoinPoints_2080_ = lean_ctor_get(v___x_2069_, 10);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2082_ = v___x_2069_;
v_isShared_2083_ = v_isSharedCheck_2093_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_pendingJoinPoints_2080_);
lean_inc(v_inlineHandledInvariants_2079_);
lean_inc(v_fuel_2078_);
lean_inc(v_simpState_2077_);
lean_inc(v_vcs_2076_);
lean_inc(v_invariants_2075_);
lean_inc(v_frameDB_2074_);
lean_inc(v_frameBackwardRuleCache_2073_);
lean_inc(v_latticeBackwardRuleCache_2072_);
lean_inc(v_splitBackwardRuleCache_2071_);
lean_inc(v_specBackwardRuleCache_2070_);
lean_dec(v___x_2069_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2093_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2084_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__3(v_a_2061_, v_a_2052_, v_pendingJoinPoints_2080_, v_rhsGoal_2055_);
lean_dec(v_a_2061_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 10, v___x_2084_);
v___x_2086_ = v___x_2082_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_specBackwardRuleCache_2070_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_splitBackwardRuleCache_2071_);
lean_ctor_set(v_reuseFailAlloc_2092_, 2, v_latticeBackwardRuleCache_2072_);
lean_ctor_set(v_reuseFailAlloc_2092_, 3, v_frameBackwardRuleCache_2073_);
lean_ctor_set(v_reuseFailAlloc_2092_, 4, v_frameDB_2074_);
lean_ctor_set(v_reuseFailAlloc_2092_, 5, v_invariants_2075_);
lean_ctor_set(v_reuseFailAlloc_2092_, 6, v_vcs_2076_);
lean_ctor_set(v_reuseFailAlloc_2092_, 7, v_simpState_2077_);
lean_ctor_set(v_reuseFailAlloc_2092_, 8, v_fuel_2078_);
lean_ctor_set(v_reuseFailAlloc_2092_, 9, v_inlineHandledInvariants_2079_);
lean_ctor_set(v_reuseFailAlloc_2092_, 10, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2090_; 
v___x_2087_ = lean_st_ref_put(v___y_2026_, v___x_2086_);
v___x_2088_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___closed__1));
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 0, v___x_2088_);
v___x_2090_ = v___x_2067_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2088_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec(v_a_2061_);
lean_dec(v_rhsGoal_2055_);
lean_dec(v_a_2052_);
lean_dec(v_goal_2024_);
v_a_2096_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2063_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2063_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec(v_rhsGoal_2055_);
lean_dec_ref(v_spec_2053_);
lean_dec(v_a_2052_);
lean_dec(v_goal_2024_);
v_a_2104_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2060_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2060_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec(v_rhsGoal_2055_);
lean_dec_ref(v_spec_2053_);
lean_dec(v_a_2052_);
lean_dec(v_goal_2024_);
v_a_2112_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2057_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2057_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec(v_goal_2024_);
lean_dec_ref(v_val_2023_);
v_a_2120_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2051_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2051_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___boxed(lean_object* v_info_2184_, lean_object* v___x_2185_, lean_object* v_val_2186_, lean_object* v_goal_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0(v_info_2184_, v___x_2185_, v_val_2186_, v_goal_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec_ref(v_info_2184_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg(lean_object* v_t_2201_, lean_object* v_k_2202_){
_start:
{
if (lean_obj_tag(v_t_2201_) == 0)
{
lean_object* v_k_2203_; lean_object* v_v_2204_; lean_object* v_l_2205_; lean_object* v_r_2206_; uint8_t v___x_2207_; 
v_k_2203_ = lean_ctor_get(v_t_2201_, 1);
v_v_2204_ = lean_ctor_get(v_t_2201_, 2);
v_l_2205_ = lean_ctor_get(v_t_2201_, 3);
v_r_2206_ = lean_ctor_get(v_t_2201_, 4);
v___x_2207_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2202_, v_k_2203_);
switch(v___x_2207_)
{
case 0:
{
v_t_2201_ = v_l_2205_;
goto _start;
}
case 1:
{
lean_object* v___x_2209_; 
lean_inc(v_v_2204_);
v___x_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2209_, 0, v_v_2204_);
return v___x_2209_;
}
default: 
{
v_t_2201_ = v_r_2206_;
goto _start;
}
}
}
else
{
lean_object* v___x_2211_; 
v___x_2211_ = lean_box(0);
return v___x_2211_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg___boxed(lean_object* v_t_2212_, lean_object* v_k_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg(v_t_2212_, v_k_2213_);
lean_dec(v_k_2213_);
lean_dec(v_t_2212_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f(lean_object* v_scope_2215_, lean_object* v_goal_2216_, lean_object* v_info_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2230_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_2217_);
v___x_2231_ = l_Lean_Expr_getAppFn(v___x_2230_);
v___x_2232_ = l_Lean_Expr_fvarId_x3f(v___x_2231_);
lean_dec_ref(v___x_2231_);
if (lean_obj_tag(v___x_2232_) == 1)
{
lean_object* v_val_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2246_; 
v_val_2233_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2235_ = v___x_2232_;
v_isShared_2236_ = v_isSharedCheck_2246_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_val_2233_);
lean_dec(v___x_2232_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2246_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v_joinPoints_2237_; lean_object* v___x_2238_; 
v_joinPoints_2237_ = lean_ctor_get(v_scope_2215_, 3);
v___x_2238_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg(v_joinPoints_2237_, v_val_2233_);
lean_dec(v_val_2233_);
if (lean_obj_tag(v___x_2238_) == 1)
{
lean_object* v_val_2239_; lean_object* v___f_2240_; lean_object* v___x_2241_; 
lean_del_object(v___x_2235_);
v_val_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_val_2239_);
lean_dec_ref_known(v___x_2238_, 1);
lean_inc(v_goal_2216_);
v___f_2240_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_wpJump_x3f___lam__0___boxed), 16, 4);
lean_closure_set(v___f_2240_, 0, v_info_2217_);
lean_closure_set(v___f_2240_, 1, v___x_2230_);
lean_closure_set(v___f_2240_, 2, v_val_2239_);
lean_closure_set(v___f_2240_, 3, v_goal_2216_);
v___x_2241_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg(v_goal_2216_, v___f_2240_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
return v___x_2241_;
}
else
{
lean_object* v___x_2242_; lean_object* v___x_2244_; 
lean_dec(v___x_2238_);
lean_dec_ref(v___x_2230_);
lean_dec_ref(v_info_2217_);
lean_dec(v_goal_2216_);
v___x_2242_ = lean_box(0);
if (v_isShared_2236_ == 0)
{
lean_ctor_set_tag(v___x_2235_, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2242_);
v___x_2244_ = v___x_2235_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2242_);
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
lean_object* v___x_2247_; lean_object* v___x_2248_; 
lean_dec(v___x_2232_);
lean_dec_ref(v___x_2230_);
lean_dec_ref(v_info_2217_);
lean_dec(v_goal_2216_);
v___x_2247_ = lean_box(0);
v___x_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
return v___x_2248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f___boxed(lean_object* v_scope_2249_, lean_object* v_goal_2250_, lean_object* v_info_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_Elab_Tactic_VCGen_wpJump_x3f(v_scope_2249_, v_goal_2250_, v_info_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
lean_dec(v_a_2262_);
lean_dec_ref(v_a_2261_);
lean_dec(v_a_2260_);
lean_dec_ref(v_a_2259_);
lean_dec(v_a_2258_);
lean_dec_ref(v_a_2257_);
lean_dec(v_a_2256_);
lean_dec_ref(v_a_2255_);
lean_dec(v_a_2254_);
lean_dec(v_a_2253_);
lean_dec_ref(v_a_2252_);
lean_dec_ref(v_scope_2249_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0(lean_object* v_00_u03b4_2265_, lean_object* v_t_2266_, lean_object* v_k_2267_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___redArg(v_t_2266_, v_k_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0___boxed(lean_object* v_00_u03b4_2269_, lean_object* v_t_2270_, lean_object* v_k_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__0(v_00_u03b4_2269_, v_t_2270_, v_k_2271_);
lean_dec(v_k_2271_);
lean_dec(v_t_2270_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1(size_t v_sz_2273_, size_t v_i_2274_, lean_object* v_bs_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___redArg(v_sz_2273_, v_i_2274_, v_bs_2275_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1___boxed(lean_object* v_sz_2289_, lean_object* v_i_2290_, lean_object* v_bs_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
size_t v_sz_boxed_2304_; size_t v_i_boxed_2305_; lean_object* v_res_2306_; 
v_sz_boxed_2304_ = lean_unbox_usize(v_sz_2289_);
lean_dec(v_sz_2289_);
v_i_boxed_2305_ = lean_unbox_usize(v_i_2290_);
lean_dec(v_i_2290_);
v_res_2306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__1(v_sz_boxed_2304_, v_i_boxed_2305_, v_bs_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2(lean_object* v_mvarId_2307_, lean_object* v_val_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg(v_mvarId_2307_, v_val_2308_, v___y_2317_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___boxed(lean_object* v_mvarId_2322_, lean_object* v_val_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2(v_mvarId_2322_, v_val_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2(lean_object* v_00_u03b2_2337_, lean_object* v_x_2338_, lean_object* v_x_2339_, lean_object* v_x_2340_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2___redArg(v_x_2338_, v_x_2339_, v_x_2340_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_2342_, lean_object* v_x_2343_, size_t v_x_2344_, size_t v_x_2345_, lean_object* v_x_2346_, lean_object* v_x_2347_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3___redArg(v_x_2343_, v_x_2344_, v_x_2345_, v_x_2346_, v_x_2347_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2349_, lean_object* v_x_2350_, lean_object* v_x_2351_, lean_object* v_x_2352_, lean_object* v_x_2353_, lean_object* v_x_2354_){
_start:
{
size_t v_x_20448__boxed_2355_; size_t v_x_20449__boxed_2356_; lean_object* v_res_2357_; 
v_x_20448__boxed_2355_ = lean_unbox_usize(v_x_2351_);
lean_dec(v_x_2351_);
v_x_20449__boxed_2356_ = lean_unbox_usize(v_x_2352_);
lean_dec(v_x_2352_);
v_res_2357_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3(v_00_u03b2_2349_, v_x_2350_, v_x_20448__boxed_2355_, v_x_20449__boxed_2356_, v_x_2353_, v_x_2354_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_2358_, lean_object* v_n_2359_, lean_object* v_k_2360_, lean_object* v_v_2361_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__5___redArg(v_n_2359_, v_k_2360_, v_v_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_2363_, size_t v_depth_2364_, lean_object* v_keys_2365_, lean_object* v_vals_2366_, lean_object* v_heq_2367_, lean_object* v_i_2368_, lean_object* v_entries_2369_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__6___redArg(v_depth_2364_, v_keys_2365_, v_vals_2366_, v_i_2368_, v_entries_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2371_, lean_object* v_depth_2372_, lean_object* v_keys_2373_, lean_object* v_vals_2374_, lean_object* v_heq_2375_, lean_object* v_i_2376_, lean_object* v_entries_2377_){
_start:
{
size_t v_depth_boxed_2378_; lean_object* v_res_2379_; 
v_depth_boxed_2378_ = lean_unbox_usize(v_depth_2372_);
lean_dec(v_depth_2372_);
v_res_2379_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__6(v_00_u03b2_2371_, v_depth_boxed_2378_, v_keys_2373_, v_vals_2374_, v_heq_2375_, v_i_2376_, v_entries_2377_);
lean_dec_ref(v_vals_2374_);
lean_dec_ref(v_keys_2373_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_2380_, lean_object* v_x_2381_, lean_object* v_x_2382_, lean_object* v_x_2383_, lean_object* v_x_2384_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2_spec__2_spec__3_spec__5_spec__7___redArg(v_x_2381_, v_x_2382_, v_x_2383_, v_x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(lean_object* v_as_2386_, size_t v_i_2387_, size_t v_stop_2388_, lean_object* v_b_2389_){
_start:
{
lean_object* v___y_2391_; uint8_t v___x_2395_; 
v___x_2395_ = lean_usize_dec_eq(v_i_2387_, v_stop_2388_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; 
v___x_2396_ = lean_array_uget_borrowed(v_as_2386_, v_i_2387_);
if (lean_obj_tag(v___x_2396_) == 0)
{
v___y_2391_ = v_b_2389_;
goto v___jp_2390_;
}
else
{
lean_object* v_val_2397_; uint8_t v___x_2398_; 
v_val_2397_ = lean_ctor_get(v___x_2396_, 0);
v___x_2398_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2397_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; 
lean_inc(v_val_2397_);
v___x_2399_ = lean_array_push(v_b_2389_, v_val_2397_);
v___y_2391_ = v___x_2399_;
goto v___jp_2390_;
}
else
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_LocalDecl_value_x3f(v_val_2397_, v___x_2395_);
if (lean_obj_tag(v___x_2400_) == 0)
{
v___y_2391_ = v_b_2389_;
goto v___jp_2390_;
}
else
{
lean_object* v___x_2401_; 
lean_dec_ref_known(v___x_2400_, 1);
lean_inc(v_val_2397_);
v___x_2401_ = lean_array_push(v_b_2389_, v_val_2397_);
v___y_2391_ = v___x_2401_;
goto v___jp_2390_;
}
}
}
}
else
{
return v_b_2389_;
}
v___jp_2390_:
{
size_t v___x_2392_; size_t v___x_2393_; 
v___x_2392_ = ((size_t)1ULL);
v___x_2393_ = lean_usize_add(v_i_2387_, v___x_2392_);
v_i_2387_ = v___x_2393_;
v_b_2389_ = v___y_2391_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2___boxed(lean_object* v_as_2402_, lean_object* v_i_2403_, lean_object* v_stop_2404_, lean_object* v_b_2405_){
_start:
{
size_t v_i_boxed_2406_; size_t v_stop_boxed_2407_; lean_object* v_res_2408_; 
v_i_boxed_2406_ = lean_unbox_usize(v_i_2403_);
lean_dec(v_i_2403_);
v_stop_boxed_2407_ = lean_unbox_usize(v_stop_2404_);
lean_dec(v_stop_2404_);
v_res_2408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_as_2402_, v_i_boxed_2406_, v_stop_boxed_2407_, v_b_2405_);
lean_dec_ref(v_as_2402_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3(lean_object* v_x_2409_, lean_object* v_x_2410_){
_start:
{
if (lean_obj_tag(v_x_2409_) == 0)
{
lean_object* v_cs_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; 
v_cs_2411_ = lean_ctor_get(v_x_2409_, 0);
v___x_2412_ = lean_unsigned_to_nat(0u);
v___x_2413_ = lean_array_get_size(v_cs_2411_);
v___x_2414_ = lean_nat_dec_lt(v___x_2412_, v___x_2413_);
if (v___x_2414_ == 0)
{
return v_x_2410_;
}
else
{
size_t v___x_2415_; size_t v___x_2416_; lean_object* v___x_2417_; 
v___x_2415_ = ((size_t)0ULL);
v___x_2416_ = lean_usize_of_nat(v___x_2413_);
v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2(v_cs_2411_, v___x_2415_, v___x_2416_, v_x_2410_);
return v___x_2417_;
}
}
else
{
lean_object* v_vs_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; uint8_t v___x_2421_; 
v_vs_2418_ = lean_ctor_get(v_x_2409_, 0);
v___x_2419_ = lean_unsigned_to_nat(0u);
v___x_2420_ = lean_array_get_size(v_vs_2418_);
v___x_2421_ = lean_nat_dec_lt(v___x_2419_, v___x_2420_);
if (v___x_2421_ == 0)
{
return v_x_2410_;
}
else
{
size_t v___x_2422_; size_t v___x_2423_; lean_object* v___x_2424_; 
v___x_2422_ = ((size_t)0ULL);
v___x_2423_ = lean_usize_of_nat(v___x_2420_);
v___x_2424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_vs_2418_, v___x_2422_, v___x_2423_, v_x_2410_);
return v___x_2424_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_2425_, size_t v_i_2426_, size_t v_stop_2427_, lean_object* v_b_2428_){
_start:
{
uint8_t v___x_2429_; 
v___x_2429_ = lean_usize_dec_eq(v_i_2426_, v_stop_2427_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; lean_object* v___x_2431_; size_t v___x_2432_; size_t v___x_2433_; 
v___x_2430_ = lean_array_uget_borrowed(v_as_2425_, v_i_2426_);
v___x_2431_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3(v___x_2430_, v_b_2428_);
v___x_2432_ = ((size_t)1ULL);
v___x_2433_ = lean_usize_add(v_i_2426_, v___x_2432_);
v_i_2426_ = v___x_2433_;
v_b_2428_ = v___x_2431_;
goto _start;
}
else
{
return v_b_2428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_2435_, lean_object* v_i_2436_, lean_object* v_stop_2437_, lean_object* v_b_2438_){
_start:
{
size_t v_i_boxed_2439_; size_t v_stop_boxed_2440_; lean_object* v_res_2441_; 
v_i_boxed_2439_ = lean_unbox_usize(v_i_2436_);
lean_dec(v_i_2436_);
v_stop_boxed_2440_ = lean_unbox_usize(v_stop_2437_);
lean_dec(v_stop_2437_);
v_res_2441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2(v_as_2435_, v_i_boxed_2439_, v_stop_boxed_2440_, v_b_2438_);
lean_dec_ref(v_as_2435_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3___boxed(lean_object* v_x_2442_, lean_object* v_x_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3(v_x_2442_, v_x_2443_);
lean_dec_ref(v_x_2442_);
return v_res_2444_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2445_; 
v___x_2445_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1(lean_object* v_x_2446_, size_t v_x_2447_, size_t v_x_2448_, lean_object* v_x_2449_){
_start:
{
if (lean_obj_tag(v_x_2446_) == 0)
{
lean_object* v_cs_2450_; lean_object* v___x_2451_; size_t v___x_2452_; lean_object* v_j_2453_; lean_object* v___x_2454_; size_t v___x_2455_; size_t v___x_2456_; size_t v___x_2457_; size_t v___x_2458_; size_t v___x_2459_; size_t v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; uint8_t v___x_2465_; 
v_cs_2450_ = lean_ctor_get(v_x_2446_, 0);
v___x_2451_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___closed__0);
v___x_2452_ = lean_usize_shift_right(v_x_2447_, v_x_2448_);
v_j_2453_ = lean_usize_to_nat(v___x_2452_);
v___x_2454_ = lean_array_get_borrowed(v___x_2451_, v_cs_2450_, v_j_2453_);
v___x_2455_ = ((size_t)1ULL);
v___x_2456_ = lean_usize_shift_left(v___x_2455_, v_x_2448_);
v___x_2457_ = lean_usize_sub(v___x_2456_, v___x_2455_);
v___x_2458_ = lean_usize_land(v_x_2447_, v___x_2457_);
v___x_2459_ = ((size_t)5ULL);
v___x_2460_ = lean_usize_sub(v_x_2448_, v___x_2459_);
v___x_2461_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1(v___x_2454_, v___x_2458_, v___x_2460_, v_x_2449_);
v___x_2462_ = lean_unsigned_to_nat(1u);
v___x_2463_ = lean_nat_add(v_j_2453_, v___x_2462_);
lean_dec(v_j_2453_);
v___x_2464_ = lean_array_get_size(v_cs_2450_);
v___x_2465_ = lean_nat_dec_lt(v___x_2463_, v___x_2464_);
if (v___x_2465_ == 0)
{
lean_dec(v___x_2463_);
return v___x_2461_;
}
else
{
size_t v___x_2466_; size_t v___x_2467_; lean_object* v___x_2468_; 
v___x_2466_ = lean_usize_of_nat(v___x_2463_);
lean_dec(v___x_2463_);
v___x_2467_ = lean_usize_of_nat(v___x_2464_);
v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1_spec__2(v_cs_2450_, v___x_2466_, v___x_2467_, v___x_2461_);
return v___x_2468_;
}
}
else
{
lean_object* v_vs_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; 
v_vs_2469_ = lean_ctor_get(v_x_2446_, 0);
v___x_2470_ = lean_usize_to_nat(v_x_2447_);
v___x_2471_ = lean_array_get_size(v_vs_2469_);
v___x_2472_ = lean_nat_dec_lt(v___x_2470_, v___x_2471_);
if (v___x_2472_ == 0)
{
lean_dec(v___x_2470_);
return v_x_2449_;
}
else
{
size_t v___x_2473_; size_t v___x_2474_; lean_object* v___x_2475_; 
v___x_2473_ = lean_usize_of_nat(v___x_2470_);
lean_dec(v___x_2470_);
v___x_2474_ = lean_usize_of_nat(v___x_2471_);
v___x_2475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_vs_2469_, v___x_2473_, v___x_2474_, v_x_2449_);
return v___x_2475_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1___boxed(lean_object* v_x_2476_, lean_object* v_x_2477_, lean_object* v_x_2478_, lean_object* v_x_2479_){
_start:
{
size_t v_x_1498__boxed_2480_; size_t v_x_1499__boxed_2481_; lean_object* v_res_2482_; 
v_x_1498__boxed_2480_ = lean_unbox_usize(v_x_2477_);
lean_dec(v_x_2477_);
v_x_1499__boxed_2481_ = lean_unbox_usize(v_x_2478_);
lean_dec(v_x_2478_);
v_res_2482_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1(v_x_2476_, v_x_1498__boxed_2480_, v_x_1499__boxed_2481_, v_x_2479_);
lean_dec_ref(v_x_2476_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0(lean_object* v_t_2483_, lean_object* v_init_2484_, lean_object* v_start_2485_){
_start:
{
lean_object* v___x_2486_; uint8_t v___x_2487_; 
v___x_2486_ = lean_unsigned_to_nat(0u);
v___x_2487_ = lean_nat_dec_eq(v_start_2485_, v___x_2486_);
if (v___x_2487_ == 0)
{
lean_object* v_root_2488_; lean_object* v_tail_2489_; size_t v_shift_2490_; lean_object* v_tailOff_2491_; uint8_t v___x_2492_; 
v_root_2488_ = lean_ctor_get(v_t_2483_, 0);
v_tail_2489_ = lean_ctor_get(v_t_2483_, 1);
v_shift_2490_ = lean_ctor_get_usize(v_t_2483_, 4);
v_tailOff_2491_ = lean_ctor_get(v_t_2483_, 3);
v___x_2492_ = lean_nat_dec_le(v_tailOff_2491_, v_start_2485_);
if (v___x_2492_ == 0)
{
size_t v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; 
v___x_2493_ = lean_usize_of_nat(v_start_2485_);
v___x_2494_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__1(v_root_2488_, v___x_2493_, v_shift_2490_, v_init_2484_);
v___x_2495_ = lean_array_get_size(v_tail_2489_);
v___x_2496_ = lean_nat_dec_lt(v___x_2486_, v___x_2495_);
if (v___x_2496_ == 0)
{
return v___x_2494_;
}
else
{
size_t v___x_2497_; size_t v___x_2498_; lean_object* v___x_2499_; 
v___x_2497_ = ((size_t)0ULL);
v___x_2498_ = lean_usize_of_nat(v___x_2495_);
v___x_2499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_tail_2489_, v___x_2497_, v___x_2498_, v___x_2494_);
return v___x_2499_;
}
}
else
{
lean_object* v___x_2500_; lean_object* v___x_2501_; uint8_t v___x_2502_; 
v___x_2500_ = lean_nat_sub(v_start_2485_, v_tailOff_2491_);
v___x_2501_ = lean_array_get_size(v_tail_2489_);
v___x_2502_ = lean_nat_dec_lt(v___x_2500_, v___x_2501_);
if (v___x_2502_ == 0)
{
lean_dec(v___x_2500_);
return v_init_2484_;
}
else
{
size_t v___x_2503_; size_t v___x_2504_; lean_object* v___x_2505_; 
v___x_2503_ = lean_usize_of_nat(v___x_2500_);
lean_dec(v___x_2500_);
v___x_2504_ = lean_usize_of_nat(v___x_2501_);
v___x_2505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_tail_2489_, v___x_2503_, v___x_2504_, v_init_2484_);
return v___x_2505_;
}
}
}
else
{
lean_object* v_root_2506_; lean_object* v_tail_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; 
v_root_2506_ = lean_ctor_get(v_t_2483_, 0);
v_tail_2507_ = lean_ctor_get(v_t_2483_, 1);
v___x_2508_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__3(v_root_2506_, v_init_2484_);
v___x_2509_ = lean_array_get_size(v_tail_2507_);
v___x_2510_ = lean_nat_dec_lt(v___x_2486_, v___x_2509_);
if (v___x_2510_ == 0)
{
return v___x_2508_;
}
else
{
size_t v___x_2511_; size_t v___x_2512_; lean_object* v___x_2513_; 
v___x_2511_ = ((size_t)0ULL);
v___x_2512_ = lean_usize_of_nat(v___x_2509_);
v___x_2513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0_spec__2(v_tail_2507_, v___x_2511_, v___x_2512_, v___x_2508_);
return v___x_2513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0___boxed(lean_object* v_t_2514_, lean_object* v_init_2515_, lean_object* v_start_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0(v_t_2514_, v_init_2515_, v_start_2516_);
lean_dec(v_start_2516_);
lean_dec_ref(v_t_2514_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0(lean_object* v_lctx_2518_, lean_object* v_init_2519_, lean_object* v_start_2520_){
_start:
{
lean_object* v_decls_2521_; lean_object* v___x_2522_; 
v_decls_2521_ = lean_ctor_get(v_lctx_2518_, 1);
v___x_2522_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0_spec__0(v_decls_2521_, v_init_2519_, v_start_2520_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0___boxed(lean_object* v_lctx_2523_, lean_object* v_init_2524_, lean_object* v_start_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0(v_lctx_2523_, v_init_2524_, v_start_2525_);
lean_dec(v_start_2525_);
lean_dec_ref(v_lctx_2523_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals(lean_object* v_jp_2529_, lean_object* v_jump_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_){
_start:
{
lean_object* v_proof_2536_; lean_object* v___x_2537_; 
v_proof_2536_ = lean_ctor_get(v_jump_2530_, 0);
lean_inc(v_proof_2536_);
lean_dec_ref(v_jump_2530_);
v___x_2537_ = l_Lean_MVarId_getDecl(v_proof_2536_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2554_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2540_ = v___x_2537_;
v_isShared_2541_ = v_isSharedCheck_2554_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2554_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v_lctx_2542_; lean_object* v_spec_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2552_; 
v_lctx_2542_ = lean_ctor_get(v_a_2538_, 1);
lean_inc_ref_n(v_lctx_2542_, 2);
lean_dec(v_a_2538_);
v_spec_2543_ = lean_ctor_get(v_jp_2529_, 0);
v___x_2544_ = l_Lean_Expr_fvarId_x21(v_spec_2543_);
v___x_2545_ = l_Lean_LocalContext_get_x21(v_lctx_2542_, v___x_2544_);
v___x_2546_ = l_Lean_LocalDecl_index(v___x_2545_);
lean_dec_ref(v___x_2545_);
v___x_2547_ = lean_unsigned_to_nat(1u);
v___x_2548_ = lean_nat_add(v___x_2546_, v___x_2547_);
lean_dec(v___x_2546_);
v___x_2549_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals___closed__0));
v___x_2550_ = l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals_spec__0(v_lctx_2542_, v___x_2549_, v___x_2548_);
lean_dec(v___x_2548_);
lean_dec_ref(v_lctx_2542_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v___x_2550_);
v___x_2552_ = v___x_2540_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2550_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
v_a_2555_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2537_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2537_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals___boxed(lean_object* v_jp_2563_, lean_object* v_jump_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals(v_jp_2563_, v_jump_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
lean_dec(v_a_2568_);
lean_dec_ref(v_a_2567_);
lean_dec(v_a_2566_);
lean_dec_ref(v_a_2565_);
lean_dec_ref(v_jp_2563_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg(lean_object* v_d_2574_, lean_object* v_00_u03c6_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_){
_start:
{
uint8_t v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = 0;
v___x_2584_ = l_Lean_LocalDecl_value_x3f(v_d_2574_, v___x_2583_);
if (lean_obj_tag(v___x_2584_) == 0)
{
uint8_t v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; uint8_t v___x_2590_; lean_object* v___x_2591_; 
v___x_2585_ = 1;
lean_inc_ref(v_d_2574_);
v___x_2586_ = l_Lean_LocalDecl_toExpr(v_d_2574_);
v___x_2587_ = lean_unsigned_to_nat(1u);
v___x_2588_ = lean_mk_empty_array_with_capacity(v___x_2587_);
v___x_2589_ = lean_array_push(v___x_2588_, v___x_2586_);
v___x_2590_ = 1;
v___x_2591_ = l_Lean_Meta_mkLambdaFVars(v___x_2589_, v_00_u03c6_2575_, v___x_2583_, v___x_2585_, v___x_2583_, v___x_2585_, v___x_2590_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_);
lean_dec_ref(v___x_2589_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2591_, 1);
v___x_2593_ = l_Lean_LocalDecl_type(v_d_2574_);
lean_dec_ref(v_d_2574_);
lean_inc_ref(v___x_2593_);
v___x_2594_ = l_Lean_Meta_Sym_inferType(v___x_2593_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2629_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2597_ = v___x_2594_;
v_isShared_2598_ = v_isSharedCheck_2629_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2594_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2629_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
uint8_t v___x_2622_; 
v___x_2622_ = l_Lean_Expr_isProp(v_a_2595_);
lean_dec(v_a_2595_);
if (v___x_2622_ == 0)
{
lean_del_object(v___x_2597_);
goto v___jp_2599_;
}
else
{
lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2623_ = l_Lean_Expr_bindingBody_x21(v_a_2592_);
v___x_2624_ = l_Lean_Expr_hasLooseBVars(v___x_2623_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; lean_object* v___x_2627_; 
lean_dec(v_a_2592_);
v___x_2625_ = l_Lean_mkAnd(v___x_2593_, v___x_2623_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v___x_2625_);
v___x_2627_ = v___x_2597_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
else
{
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2597_);
goto v___jp_2599_;
}
}
v___jp_2599_:
{
lean_object* v___x_2600_; 
lean_inc_ref(v___x_2593_);
v___x_2600_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_2593_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2613_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2603_ = v___x_2600_;
v_isShared_2604_ = v_isSharedCheck_2613_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2600_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2613_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2611_; 
v___x_2605_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___closed__1));
v___x_2606_ = lean_box(0);
v___x_2607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2607_, 0, v_a_2601_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = l_Lean_mkConst(v___x_2605_, v___x_2607_);
v___x_2609_ = l_Lean_mkAppB(v___x_2608_, v___x_2593_, v_a_2592_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2609_);
v___x_2611_ = v___x_2603_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2609_);
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
lean_dec_ref(v___x_2593_);
lean_dec(v_a_2592_);
v_a_2614_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2600_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2600_);
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
else
{
lean_dec_ref(v___x_2593_);
lean_dec(v_a_2592_);
return v___x_2594_;
}
}
else
{
lean_dec_ref(v_d_2574_);
return v___x_2591_;
}
}
else
{
uint8_t v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; uint8_t v___x_2635_; lean_object* v___x_2636_; 
lean_dec_ref_known(v___x_2584_, 1);
v___x_2630_ = 1;
v___x_2631_ = l_Lean_LocalDecl_toExpr(v_d_2574_);
v___x_2632_ = lean_unsigned_to_nat(1u);
v___x_2633_ = lean_mk_empty_array_with_capacity(v___x_2632_);
v___x_2634_ = lean_array_push(v___x_2633_, v___x_2631_);
v___x_2635_ = 1;
v___x_2636_ = l_Lean_Meta_mkLetFVars(v___x_2634_, v_00_u03c6_2575_, v___x_2630_, v___x_2583_, v___x_2635_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_);
lean_dec_ref(v___x_2634_);
return v___x_2636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___boxed(lean_object* v_d_2637_, lean_object* v_00_u03c6_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg(v_d_2637_, v_00_u03c6_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
lean_dec(v_a_2640_);
lean_dec_ref(v_a_2639_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal(lean_object* v_d_2647_, lean_object* v_00_u03c6_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg(v_d_2647_, v_00_u03c6_2648_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___boxed(lean_object* v_d_2662_, lean_object* v_00_u03c6_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal(v_d_2662_, v_00_u03c6_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
lean_dec(v_a_2674_);
lean_dec_ref(v_a_2673_);
lean_dec(v_a_2672_);
lean_dec_ref(v_a_2671_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
return v_res_2676_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__2(void){
_start:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2680_ = lean_box(0);
v___x_2681_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__1));
v___x_2682_ = l_Lean_mkConst(v___x_2681_, v___x_2680_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(lean_object* v_ps_2683_, lean_object* v_lo_2684_, lean_object* v_hi_2685_){
_start:
{
uint8_t v___x_2686_; 
v___x_2686_ = lean_nat_dec_eq(v_hi_2685_, v_lo_2684_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; 
v___x_2687_ = lean_unsigned_to_nat(1u);
v___x_2688_ = lean_nat_add(v_lo_2684_, v___x_2687_);
v___x_2689_ = lean_nat_dec_eq(v_hi_2685_, v___x_2688_);
lean_dec(v___x_2688_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2690_; lean_object* v_mid_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2690_ = lean_nat_add(v_lo_2684_, v_hi_2685_);
v_mid_2691_ = lean_nat_shiftr(v___x_2690_, v___x_2687_);
lean_dec(v___x_2690_);
v___x_2692_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(v_ps_2683_, v_lo_2684_, v_mid_2691_);
v___x_2693_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(v_ps_2683_, v_mid_2691_, v_hi_2685_);
lean_dec(v_mid_2691_);
v___x_2694_ = l_Lean_mkOr(v___x_2692_, v___x_2693_);
return v___x_2694_;
}
else
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2695_ = l_Lean_instInhabitedExpr;
v___x_2696_ = lean_array_get_borrowed(v___x_2695_, v_ps_2683_, v_lo_2684_);
lean_inc(v___x_2696_);
return v___x_2696_;
}
}
else
{
lean_object* v___x_2697_; 
v___x_2697_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__2, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__2_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___closed__2);
return v___x_2697_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree___boxed(lean_object* v_ps_2698_, lean_object* v_lo_2699_, lean_object* v_hi_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(v_ps_2698_, v_lo_2699_, v_hi_2700_);
lean_dec(v_hi_2700_);
lean_dec(v_lo_2699_);
lean_dec_ref(v_ps_2698_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(lean_object* v_msg_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_ref_2708_; lean_object* v___x_2709_; lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2718_; 
v_ref_2708_ = lean_ctor_get(v___y_2705_, 2);
v___x_2709_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__2_spec__3(v_msg_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2712_ = v___x_2709_;
v_isShared_2713_ = v_isSharedCheck_2718_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2709_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2718_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2714_; lean_object* v___x_2716_; 
lean_inc(v_ref_2708_);
v___x_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2714_, 0, v_ref_2708_);
lean_ctor_set(v___x_2714_, 1, v_a_2710_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set_tag(v___x_2712_, 1);
lean_ctor_set(v___x_2712_, 0, v___x_2714_);
v___x_2716_ = v___x_2712_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg___boxed(lean_object* v_msg_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v_msg_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
return v_res_2725_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__1(void){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2727_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__0));
v___x_2728_ = l_Lean_stringToMessageData(v___x_2727_);
return v___x_2728_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__6(void){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2736_ = lean_box(0);
v___x_2737_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__5));
v___x_2738_ = l_Lean_mkConst(v___x_2737_, v___x_2736_);
return v___x_2738_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__9(void){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2743_ = lean_box(0);
v___x_2744_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__8));
v___x_2745_ = l_Lean_mkConst(v___x_2744_, v___x_2743_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(lean_object* v_00_u03c6_2746_, lean_object* v_i_2747_, lean_object* v_lo_2748_, lean_object* v_hi_2749_, lean_object* v_k_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___x_2765_; lean_object* v___x_2766_; uint8_t v___x_2767_; 
v___x_2765_ = lean_unsigned_to_nat(1u);
v___x_2766_ = lean_nat_add(v_lo_2748_, v___x_2765_);
v___x_2767_ = lean_nat_dec_eq(v_hi_2749_, v___x_2766_);
lean_dec(v___x_2766_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2768_; uint8_t v___x_2769_; 
v___x_2768_ = l_Lean_Expr_cleanupAnnotations(v_00_u03c6_2746_);
v___x_2769_ = l_Lean_Expr_isApp(v___x_2768_);
if (v___x_2769_ == 0)
{
lean_dec_ref(v___x_2768_);
lean_dec_ref(v_k_2750_);
v___y_2757_ = v_a_2751_;
v___y_2758_ = v_a_2752_;
v___y_2759_ = v_a_2753_;
v___y_2760_ = v_a_2754_;
goto v___jp_2756_;
}
else
{
lean_object* v___x_2770_; uint8_t v___x_2771_; 
v___x_2770_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2768_);
v___x_2771_ = l_Lean_Expr_isApp(v___x_2770_);
if (v___x_2771_ == 0)
{
lean_dec_ref(v___x_2770_);
lean_dec_ref(v___x_2768_);
lean_dec_ref(v_k_2750_);
v___y_2757_ = v_a_2751_;
v___y_2758_ = v_a_2752_;
v___y_2759_ = v_a_2753_;
v___y_2760_ = v_a_2754_;
goto v___jp_2756_;
}
else
{
lean_object* v___x_2772_; lean_object* v___x_2773_; uint8_t v___x_2774_; 
v___x_2772_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2770_);
v___x_2773_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__3));
v___x_2774_ = l_Lean_Expr_isConstOf(v___x_2772_, v___x_2773_);
lean_dec_ref(v___x_2772_);
if (v___x_2774_ == 0)
{
lean_dec_ref(v___x_2770_);
lean_dec_ref(v___x_2768_);
lean_dec_ref(v_k_2750_);
v___y_2757_ = v_a_2751_;
v___y_2758_ = v_a_2752_;
v___y_2759_ = v_a_2753_;
v___y_2760_ = v_a_2754_;
goto v___jp_2756_;
}
else
{
lean_object* v_arg_2775_; lean_object* v_arg_2776_; lean_object* v___x_2777_; lean_object* v_mid_2778_; uint8_t v___x_2779_; 
lean_dec_ref(v_00_u03c6_2746_);
v_arg_2775_ = lean_ctor_get(v___x_2768_, 1);
lean_inc_ref(v_arg_2775_);
lean_dec_ref(v___x_2768_);
v_arg_2776_ = lean_ctor_get(v___x_2770_, 1);
lean_inc_ref(v_arg_2776_);
lean_dec_ref(v___x_2770_);
v___x_2777_ = lean_nat_add(v_lo_2748_, v_hi_2749_);
v_mid_2778_ = lean_nat_shiftr(v___x_2777_, v___x_2765_);
lean_dec(v___x_2777_);
v___x_2779_ = lean_nat_dec_lt(v_i_2747_, v_mid_2778_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; 
lean_inc_ref(v_arg_2775_);
v___x_2780_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(v_arg_2775_, v_i_2747_, v_mid_2778_, v_hi_2749_, v_k_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_);
lean_dec(v_mid_2778_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2790_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2783_ = v___x_2780_;
v_isShared_2784_ = v_isSharedCheck_2790_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2780_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2790_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2788_; 
v___x_2785_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__6, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__6_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__6);
v___x_2786_ = l_Lean_mkApp3(v___x_2785_, v_arg_2776_, v_arg_2775_, v_a_2781_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v___x_2786_);
v___x_2788_ = v___x_2783_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
else
{
lean_dec_ref(v_arg_2776_);
lean_dec_ref(v_arg_2775_);
return v___x_2780_;
}
}
else
{
lean_object* v___x_2791_; 
lean_inc_ref(v_arg_2776_);
v___x_2791_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(v_arg_2776_, v_i_2747_, v_lo_2748_, v_mid_2778_, v_k_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_);
lean_dec(v_mid_2778_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2801_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2794_ = v___x_2791_;
v_isShared_2795_ = v_isSharedCheck_2801_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2801_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2799_; 
v___x_2796_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__9, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__9);
v___x_2797_ = l_Lean_mkApp3(v___x_2796_, v_arg_2776_, v_arg_2775_, v_a_2792_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 0, v___x_2797_);
v___x_2799_ = v___x_2794_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
else
{
lean_dec_ref(v_arg_2776_);
lean_dec_ref(v_arg_2775_);
return v___x_2791_;
}
}
}
}
}
}
else
{
lean_object* v___x_2802_; 
lean_inc(v_a_2754_);
lean_inc_ref(v_a_2753_);
lean_inc(v_a_2752_);
lean_inc_ref(v_a_2751_);
v___x_2802_ = lean_apply_6(v_k_2750_, v_00_u03c6_2746_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, lean_box(0));
return v___x_2802_;
}
v___jp_2756_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2761_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__1, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___closed__1);
v___x_2762_ = l_Lean_indentExpr(v_00_u03c6_2746_);
v___x_2763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2761_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v___x_2763_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
return v___x_2764_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro___boxed(lean_object* v_00_u03c6_2803_, lean_object* v_i_2804_, lean_object* v_lo_2805_, lean_object* v_hi_2806_, lean_object* v_k_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(v_00_u03c6_2803_, v_i_2804_, v_lo_2805_, v_hi_2806_, v_k_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_);
lean_dec(v_a_2811_);
lean_dec_ref(v_a_2810_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
lean_dec(v_hi_2806_);
lean_dec(v_lo_2805_);
lean_dec(v_i_2804_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0(lean_object* v_00_u03b1_2814_, lean_object* v_msg_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v___x_2821_; 
v___x_2821_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v_msg_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___boxed(lean_object* v_00_u03b1_2822_, lean_object* v_msg_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0(v_00_u03b1_2822_, v_msg_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(lean_object* v_lctx_2830_, lean_object* v_localInsts_2831_, lean_object* v_x_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v___f_2845_; lean_object* v___x_2846_; 
lean_inc(v___y_2839_);
lean_inc_ref(v___y_2838_);
lean_inc(v___y_2837_);
lean_inc_ref(v___y_2836_);
lean_inc(v___y_2835_);
lean_inc(v___y_2834_);
lean_inc_ref(v___y_2833_);
v___f_2845_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_2845_, 0, v_x_2832_);
lean_closure_set(v___f_2845_, 1, v___y_2833_);
lean_closure_set(v___f_2845_, 2, v___y_2834_);
lean_closure_set(v___f_2845_, 3, v___y_2835_);
lean_closure_set(v___f_2845_, 4, v___y_2836_);
lean_closure_set(v___f_2845_, 5, v___y_2837_);
lean_closure_set(v___f_2845_, 6, v___y_2838_);
lean_closure_set(v___f_2845_, 7, v___y_2839_);
v___x_2846_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2830_, v_localInsts_2831_, v___f_2845_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
if (lean_obj_tag(v___x_2846_) == 0)
{
return v___x_2846_;
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2846_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2846_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg___boxed(lean_object* v_lctx_2855_, lean_object* v_localInsts_2856_, lean_object* v_x_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(v_lctx_2855_, v_localInsts_2856_, v_x_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6(lean_object* v_00_u03b1_2871_, lean_object* v_lctx_2872_, lean_object* v_localInsts_2873_, lean_object* v_x_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(v_lctx_2872_, v_localInsts_2873_, v_x_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___boxed(lean_object* v_00_u03b1_2888_, lean_object* v_lctx_2889_, lean_object* v_localInsts_2890_, lean_object* v_x_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6(v_00_u03b1_2888_, v_lctx_2889_, v_localInsts_2890_, v_x_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
lean_dec(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg(lean_object* v_a_2905_, lean_object* v_x_2906_){
_start:
{
if (lean_obj_tag(v_x_2906_) == 0)
{
lean_object* v___x_2907_; 
v___x_2907_ = lean_box(0);
return v___x_2907_;
}
else
{
lean_object* v_key_2908_; lean_object* v_value_2909_; lean_object* v_tail_2910_; uint8_t v___x_2911_; 
v_key_2908_ = lean_ctor_get(v_x_2906_, 0);
v_value_2909_ = lean_ctor_get(v_x_2906_, 1);
v_tail_2910_ = lean_ctor_get(v_x_2906_, 2);
v___x_2911_ = l_Lean_instBEqFVarId_beq(v_key_2908_, v_a_2905_);
if (v___x_2911_ == 0)
{
v_x_2906_ = v_tail_2910_;
goto _start;
}
else
{
lean_object* v___x_2913_; 
lean_inc(v_value_2909_);
v___x_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2913_, 0, v_value_2909_);
return v___x_2913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg___boxed(lean_object* v_a_2914_, lean_object* v_x_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg(v_a_2914_, v_x_2915_);
lean_dec(v_x_2915_);
lean_dec(v_a_2914_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg(lean_object* v_m_2917_, lean_object* v_a_2918_){
_start:
{
lean_object* v_buckets_2919_; lean_object* v___x_2920_; uint64_t v___x_2921_; uint64_t v___x_2922_; uint64_t v___x_2923_; uint64_t v_fold_2924_; uint64_t v___x_2925_; uint64_t v___x_2926_; uint64_t v___x_2927_; size_t v___x_2928_; size_t v___x_2929_; size_t v___x_2930_; size_t v___x_2931_; size_t v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v_buckets_2919_ = lean_ctor_get(v_m_2917_, 1);
v___x_2920_ = lean_array_get_size(v_buckets_2919_);
v___x_2921_ = l_Lean_instHashableFVarId_hash(v_a_2918_);
v___x_2922_ = 32ULL;
v___x_2923_ = lean_uint64_shift_right(v___x_2921_, v___x_2922_);
v_fold_2924_ = lean_uint64_xor(v___x_2921_, v___x_2923_);
v___x_2925_ = 16ULL;
v___x_2926_ = lean_uint64_shift_right(v_fold_2924_, v___x_2925_);
v___x_2927_ = lean_uint64_xor(v_fold_2924_, v___x_2926_);
v___x_2928_ = lean_uint64_to_usize(v___x_2927_);
v___x_2929_ = lean_usize_of_nat(v___x_2920_);
v___x_2930_ = ((size_t)1ULL);
v___x_2931_ = lean_usize_sub(v___x_2929_, v___x_2930_);
v___x_2932_ = lean_usize_land(v___x_2928_, v___x_2931_);
v___x_2933_ = lean_array_uget_borrowed(v_buckets_2919_, v___x_2932_);
v___x_2934_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg(v_a_2918_, v___x_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg___boxed(lean_object* v_m_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg(v_m_2935_, v_a_2936_);
lean_dec(v_a_2936_);
lean_dec_ref(v_m_2935_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4___redArg(lean_object* v_a_2938_, lean_object* v_b_2939_, lean_object* v_x_2940_){
_start:
{
if (lean_obj_tag(v_x_2940_) == 0)
{
lean_dec(v_b_2939_);
lean_dec(v_a_2938_);
return v_x_2940_;
}
else
{
lean_object* v_key_2941_; lean_object* v_value_2942_; lean_object* v_tail_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2955_; 
v_key_2941_ = lean_ctor_get(v_x_2940_, 0);
v_value_2942_ = lean_ctor_get(v_x_2940_, 1);
v_tail_2943_ = lean_ctor_get(v_x_2940_, 2);
v_isSharedCheck_2955_ = !lean_is_exclusive(v_x_2940_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2945_ = v_x_2940_;
v_isShared_2946_ = v_isSharedCheck_2955_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_tail_2943_);
lean_inc(v_value_2942_);
lean_inc(v_key_2941_);
lean_dec(v_x_2940_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2955_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
uint8_t v___x_2947_; 
v___x_2947_ = l_Lean_instBEqFVarId_beq(v_key_2941_, v_a_2938_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; lean_object* v___x_2950_; 
v___x_2948_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4___redArg(v_a_2938_, v_b_2939_, v_tail_2943_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 2, v___x_2948_);
v___x_2950_ = v___x_2945_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_key_2941_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v_value_2942_);
lean_ctor_set(v_reuseFailAlloc_2951_, 2, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
else
{
lean_object* v___x_2953_; 
lean_dec(v_value_2942_);
lean_dec(v_key_2941_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 1, v_b_2939_);
lean_ctor_set(v___x_2945_, 0, v_a_2938_);
v___x_2953_ = v___x_2945_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2938_);
lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_b_2939_);
lean_ctor_set(v_reuseFailAlloc_2954_, 2, v_tail_2943_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg(lean_object* v_a_2956_, lean_object* v_x_2957_){
_start:
{
if (lean_obj_tag(v_x_2957_) == 0)
{
uint8_t v___x_2958_; 
v___x_2958_ = 0;
return v___x_2958_;
}
else
{
lean_object* v_key_2959_; lean_object* v_tail_2960_; uint8_t v___x_2961_; 
v_key_2959_ = lean_ctor_get(v_x_2957_, 0);
v_tail_2960_ = lean_ctor_get(v_x_2957_, 2);
v___x_2961_ = l_Lean_instBEqFVarId_beq(v_key_2959_, v_a_2956_);
if (v___x_2961_ == 0)
{
v_x_2957_ = v_tail_2960_;
goto _start;
}
else
{
return v___x_2961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg___boxed(lean_object* v_a_2963_, lean_object* v_x_2964_){
_start:
{
uint8_t v_res_2965_; lean_object* v_r_2966_; 
v_res_2965_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg(v_a_2963_, v_x_2964_);
lean_dec(v_x_2964_);
lean_dec(v_a_2963_);
v_r_2966_ = lean_box(v_res_2965_);
return v_r_2966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5_spec__11___redArg(lean_object* v_x_2967_, lean_object* v_x_2968_){
_start:
{
if (lean_obj_tag(v_x_2968_) == 0)
{
return v_x_2967_;
}
else
{
lean_object* v_key_2969_; lean_object* v_value_2970_; lean_object* v_tail_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2994_; 
v_key_2969_ = lean_ctor_get(v_x_2968_, 0);
v_value_2970_ = lean_ctor_get(v_x_2968_, 1);
v_tail_2971_ = lean_ctor_get(v_x_2968_, 2);
v_isSharedCheck_2994_ = !lean_is_exclusive(v_x_2968_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2973_ = v_x_2968_;
v_isShared_2974_ = v_isSharedCheck_2994_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_tail_2971_);
lean_inc(v_value_2970_);
lean_inc(v_key_2969_);
lean_dec(v_x_2968_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2994_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2975_; uint64_t v___x_2976_; uint64_t v___x_2977_; uint64_t v___x_2978_; uint64_t v_fold_2979_; uint64_t v___x_2980_; uint64_t v___x_2981_; uint64_t v___x_2982_; size_t v___x_2983_; size_t v___x_2984_; size_t v___x_2985_; size_t v___x_2986_; size_t v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2990_; 
v___x_2975_ = lean_array_get_size(v_x_2967_);
v___x_2976_ = l_Lean_instHashableFVarId_hash(v_key_2969_);
v___x_2977_ = 32ULL;
v___x_2978_ = lean_uint64_shift_right(v___x_2976_, v___x_2977_);
v_fold_2979_ = lean_uint64_xor(v___x_2976_, v___x_2978_);
v___x_2980_ = 16ULL;
v___x_2981_ = lean_uint64_shift_right(v_fold_2979_, v___x_2980_);
v___x_2982_ = lean_uint64_xor(v_fold_2979_, v___x_2981_);
v___x_2983_ = lean_uint64_to_usize(v___x_2982_);
v___x_2984_ = lean_usize_of_nat(v___x_2975_);
v___x_2985_ = ((size_t)1ULL);
v___x_2986_ = lean_usize_sub(v___x_2984_, v___x_2985_);
v___x_2987_ = lean_usize_land(v___x_2983_, v___x_2986_);
v___x_2988_ = lean_array_uget_borrowed(v_x_2967_, v___x_2987_);
lean_inc(v___x_2988_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 2, v___x_2988_);
v___x_2990_ = v___x_2973_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_key_2969_);
lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_value_2970_);
lean_ctor_set(v_reuseFailAlloc_2993_, 2, v___x_2988_);
v___x_2990_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
lean_object* v___x_2991_; 
v___x_2991_ = lean_array_uset(v_x_2967_, v___x_2987_, v___x_2990_);
v_x_2967_ = v___x_2991_;
v_x_2968_ = v_tail_2971_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5___redArg(lean_object* v_i_2995_, lean_object* v_source_2996_, lean_object* v_target_2997_){
_start:
{
lean_object* v___x_2998_; uint8_t v___x_2999_; 
v___x_2998_ = lean_array_get_size(v_source_2996_);
v___x_2999_ = lean_nat_dec_lt(v_i_2995_, v___x_2998_);
if (v___x_2999_ == 0)
{
lean_dec_ref(v_source_2996_);
lean_dec(v_i_2995_);
return v_target_2997_;
}
else
{
lean_object* v_es_3000_; lean_object* v___x_3001_; lean_object* v_source_3002_; lean_object* v_target_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v_es_3000_ = lean_array_fget(v_source_2996_, v_i_2995_);
v___x_3001_ = lean_box(0);
v_source_3002_ = lean_array_fset(v_source_2996_, v_i_2995_, v___x_3001_);
v_target_3003_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5_spec__11___redArg(v_target_2997_, v_es_3000_);
v___x_3004_ = lean_unsigned_to_nat(1u);
v___x_3005_ = lean_nat_add(v_i_2995_, v___x_3004_);
lean_dec(v_i_2995_);
v_i_2995_ = v___x_3005_;
v_source_2996_ = v_source_3002_;
v_target_2997_ = v_target_3003_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3___redArg(lean_object* v_data_3007_){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v_nbuckets_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3008_ = lean_array_get_size(v_data_3007_);
v___x_3009_ = lean_unsigned_to_nat(2u);
v_nbuckets_3010_ = lean_nat_mul(v___x_3008_, v___x_3009_);
v___x_3011_ = lean_unsigned_to_nat(0u);
v___x_3012_ = lean_box(0);
v___x_3013_ = lean_mk_array(v_nbuckets_3010_, v___x_3012_);
v___x_3014_ = lean_array_propagate_mark(v_data_3007_, v___x_3013_);
v___x_3015_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5___redArg(v___x_3011_, v_data_3007_, v___x_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1___redArg(lean_object* v_m_3016_, lean_object* v_a_3017_, lean_object* v_b_3018_){
_start:
{
lean_object* v_size_3019_; lean_object* v_buckets_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3063_; 
v_size_3019_ = lean_ctor_get(v_m_3016_, 0);
v_buckets_3020_ = lean_ctor_get(v_m_3016_, 1);
v_isSharedCheck_3063_ = !lean_is_exclusive(v_m_3016_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3022_ = v_m_3016_;
v_isShared_3023_ = v_isSharedCheck_3063_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_buckets_3020_);
lean_inc(v_size_3019_);
lean_dec(v_m_3016_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3063_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3024_; uint64_t v___x_3025_; uint64_t v___x_3026_; uint64_t v___x_3027_; uint64_t v_fold_3028_; uint64_t v___x_3029_; uint64_t v___x_3030_; uint64_t v___x_3031_; size_t v___x_3032_; size_t v___x_3033_; size_t v___x_3034_; size_t v___x_3035_; size_t v___x_3036_; lean_object* v_bkt_3037_; uint8_t v___x_3038_; 
v___x_3024_ = lean_array_get_size(v_buckets_3020_);
v___x_3025_ = l_Lean_instHashableFVarId_hash(v_a_3017_);
v___x_3026_ = 32ULL;
v___x_3027_ = lean_uint64_shift_right(v___x_3025_, v___x_3026_);
v_fold_3028_ = lean_uint64_xor(v___x_3025_, v___x_3027_);
v___x_3029_ = 16ULL;
v___x_3030_ = lean_uint64_shift_right(v_fold_3028_, v___x_3029_);
v___x_3031_ = lean_uint64_xor(v_fold_3028_, v___x_3030_);
v___x_3032_ = lean_uint64_to_usize(v___x_3031_);
v___x_3033_ = lean_usize_of_nat(v___x_3024_);
v___x_3034_ = ((size_t)1ULL);
v___x_3035_ = lean_usize_sub(v___x_3033_, v___x_3034_);
v___x_3036_ = lean_usize_land(v___x_3032_, v___x_3035_);
v_bkt_3037_ = lean_array_uget_borrowed(v_buckets_3020_, v___x_3036_);
v___x_3038_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg(v_a_3017_, v_bkt_3037_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; lean_object* v_size_x27_3040_; lean_object* v___x_3041_; lean_object* v_buckets_x27_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; uint8_t v___x_3048_; 
v___x_3039_ = lean_unsigned_to_nat(1u);
v_size_x27_3040_ = lean_nat_add(v_size_3019_, v___x_3039_);
lean_dec(v_size_3019_);
lean_inc(v_bkt_3037_);
v___x_3041_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3041_, 0, v_a_3017_);
lean_ctor_set(v___x_3041_, 1, v_b_3018_);
lean_ctor_set(v___x_3041_, 2, v_bkt_3037_);
v_buckets_x27_3042_ = lean_array_uset(v_buckets_3020_, v___x_3036_, v___x_3041_);
v___x_3043_ = lean_unsigned_to_nat(4u);
v___x_3044_ = lean_nat_mul(v_size_x27_3040_, v___x_3043_);
v___x_3045_ = lean_unsigned_to_nat(3u);
v___x_3046_ = lean_nat_div(v___x_3044_, v___x_3045_);
lean_dec(v___x_3044_);
v___x_3047_ = lean_array_get_size(v_buckets_x27_3042_);
v___x_3048_ = lean_nat_dec_le(v___x_3046_, v___x_3047_);
lean_dec(v___x_3046_);
if (v___x_3048_ == 0)
{
lean_object* v_val_3049_; lean_object* v___x_3051_; 
v_val_3049_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3___redArg(v_buckets_x27_3042_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 1, v_val_3049_);
lean_ctor_set(v___x_3022_, 0, v_size_x27_3040_);
v___x_3051_ = v___x_3022_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_size_x27_3040_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v_val_3049_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
else
{
lean_object* v___x_3054_; 
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 1, v_buckets_x27_3042_);
lean_ctor_set(v___x_3022_, 0, v_size_x27_3040_);
v___x_3054_ = v___x_3022_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_size_x27_3040_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_buckets_x27_3042_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
else
{
lean_object* v___x_3056_; lean_object* v_buckets_x27_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3061_; 
lean_inc(v_bkt_3037_);
v___x_3056_ = lean_box(0);
v_buckets_x27_3057_ = lean_array_uset(v_buckets_3020_, v___x_3036_, v___x_3056_);
v___x_3058_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4___redArg(v_a_3017_, v_b_3018_, v_bkt_3037_);
v___x_3059_ = lean_array_uset(v_buckets_x27_3057_, v___x_3036_, v___x_3058_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 1, v___x_3059_);
v___x_3061_ = v___x_3022_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_size_3019_);
lean_ctor_set(v_reuseFailAlloc_3062_, 1, v___x_3059_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg(lean_object* v_jumps_3064_, lean_object* v_i_3065_, lean_object* v_range_3066_, lean_object* v_b_3067_, lean_object* v_i_3068_){
_start:
{
lean_object* v_stop_3070_; lean_object* v_step_3071_; lean_object* v_a_3073_; lean_object* v_groups_3077_; lean_object* v_byLocal_3078_; uint8_t v___x_3084_; 
v_stop_3070_ = lean_ctor_get(v_range_3066_, 1);
v_step_3071_ = lean_ctor_get(v_range_3066_, 2);
v___x_3084_ = lean_nat_dec_lt(v_i_3068_, v_stop_3070_);
if (v___x_3084_ == 0)
{
lean_object* v___x_3085_; 
lean_dec(v_i_3068_);
v___x_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3085_, 0, v_b_3067_);
return v___x_3085_;
}
else
{
lean_object* v_fst_3086_; lean_object* v_snd_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3113_; 
v_fst_3086_ = lean_ctor_get(v_b_3067_, 0);
v_snd_3087_ = lean_ctor_get(v_b_3067_, 1);
v_isSharedCheck_3113_ = !lean_is_exclusive(v_b_3067_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3089_ = v_b_3067_;
v_isShared_3090_ = v_isSharedCheck_3113_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_snd_3087_);
lean_inc(v_fst_3086_);
lean_dec(v_b_3067_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3113_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___y_3092_; lean_object* v___x_3096_; lean_object* v_snd_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; 
v___x_3096_ = lean_array_fget_borrowed(v_jumps_3064_, v_i_3068_);
v_snd_3097_ = lean_ctor_get(v___x_3096_, 1);
v___x_3098_ = lean_array_get_size(v_snd_3097_);
v___x_3099_ = lean_nat_dec_lt(v_i_3065_, v___x_3098_);
if (v___x_3099_ == 0)
{
lean_del_object(v___x_3089_);
v_groups_3077_ = v_fst_3086_;
v_byLocal_3078_ = v_snd_3087_;
goto v___jp_3076_;
}
else
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3100_ = lean_array_fget_borrowed(v_snd_3097_, v_i_3065_);
v___x_3101_ = l_Lean_LocalDecl_fvarId(v___x_3100_);
v___x_3102_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg(v_snd_3087_, v___x_3101_);
if (lean_obj_tag(v___x_3102_) == 1)
{
lean_object* v_val_3103_; lean_object* v___x_3104_; uint8_t v___x_3105_; 
lean_dec(v___x_3101_);
v_val_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_val_3103_);
lean_dec_ref_known(v___x_3102_, 1);
v___x_3104_ = lean_array_get_size(v_fst_3086_);
v___x_3105_ = lean_nat_dec_lt(v_val_3103_, v___x_3104_);
if (v___x_3105_ == 0)
{
lean_dec(v_val_3103_);
v___y_3092_ = v_fst_3086_;
goto v___jp_3091_;
}
else
{
lean_object* v_v_3106_; lean_object* v___x_3107_; lean_object* v_xs_x27_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v_v_3106_ = lean_array_fget(v_fst_3086_, v_val_3103_);
v___x_3107_ = lean_box(0);
v_xs_x27_3108_ = lean_array_fset(v_fst_3086_, v_val_3103_, v___x_3107_);
lean_inc(v_i_3068_);
v___x_3109_ = lean_array_push(v_v_3106_, v_i_3068_);
v___x_3110_ = lean_array_fset(v_xs_x27_3108_, v_val_3103_, v___x_3109_);
lean_dec(v_val_3103_);
v___y_3092_ = v___x_3110_;
goto v___jp_3091_;
}
}
else
{
lean_object* v___x_3111_; lean_object* v_byLocal_3112_; 
lean_dec(v___x_3102_);
lean_del_object(v___x_3089_);
v___x_3111_ = lean_array_get_size(v_fst_3086_);
v_byLocal_3112_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1___redArg(v_snd_3087_, v___x_3101_, v___x_3111_);
v_groups_3077_ = v_fst_3086_;
v_byLocal_3078_ = v_byLocal_3112_;
goto v___jp_3076_;
}
}
v___jp_3091_:
{
lean_object* v___x_3094_; 
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v___y_3092_);
v___x_3094_ = v___x_3089_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___y_3092_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_snd_3087_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
v_a_3073_ = v___x_3094_;
goto v___jp_3072_;
}
}
}
}
v___jp_3072_:
{
lean_object* v___x_3074_; 
v___x_3074_ = lean_nat_add(v_i_3068_, v_step_3071_);
lean_dec(v_i_3068_);
v_b_3067_ = v_a_3073_;
v_i_3068_ = v___x_3074_;
goto _start;
}
v___jp_3076_:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v_groups_3082_; lean_object* v___x_3083_; 
v___x_3079_ = lean_unsigned_to_nat(1u);
v___x_3080_ = lean_mk_empty_array_with_capacity(v___x_3079_);
lean_inc(v_i_3068_);
v___x_3081_ = lean_array_push(v___x_3080_, v_i_3068_);
v_groups_3082_ = lean_array_push(v_groups_3077_, v___x_3081_);
v___x_3083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3083_, 0, v_groups_3082_);
lean_ctor_set(v___x_3083_, 1, v_byLocal_3078_);
v_a_3073_ = v___x_3083_;
goto v___jp_3072_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg___boxed(lean_object* v_jumps_3114_, lean_object* v_i_3115_, lean_object* v_range_3116_, lean_object* v_b_3117_, lean_object* v_i_3118_, lean_object* v___y_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg(v_jumps_3114_, v_i_3115_, v_range_3116_, v_b_3117_, v_i_3118_);
lean_dec_ref(v_range_3116_);
lean_dec(v_i_3115_);
lean_dec_ref(v_jumps_3114_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(lean_object* v_xs_3127_, lean_object* v_fst_3128_, lean_object* v_range_3129_, lean_object* v_b_3130_, lean_object* v_i_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v_stop_3139_; lean_object* v_step_3140_; lean_object* v_a_3142_; uint8_t v___x_3145_; 
v_stop_3139_ = lean_ctor_get(v_range_3129_, 1);
v_step_3140_ = lean_ctor_get(v_range_3129_, 2);
v___x_3145_ = lean_nat_dec_lt(v_i_3131_, v_stop_3139_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; 
lean_dec(v_i_3131_);
v___x_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3146_, 0, v_b_3130_);
return v___x_3146_;
}
else
{
lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3147_ = l_Lean_instInhabitedExpr;
v___x_3148_ = lean_array_fget_borrowed(v_xs_3127_, v_i_3131_);
lean_inc(v___x_3148_);
v___x_3149_ = l_Lean_Meta_Sym_inferType(v___x_3148_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3149_) == 0)
{
lean_object* v_a_3150_; lean_object* v___x_3151_; uint8_t v___x_3152_; 
v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
lean_inc(v_a_3150_);
lean_dec_ref_known(v___x_3149_, 1);
v___x_3151_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__1));
v___x_3152_ = l_Lean_Expr_isConstOf(v_a_3150_, v___x_3151_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3153_; 
lean_inc(v_a_3150_);
v___x_3153_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_3150_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; lean_object* v_args_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3154_);
lean_dec_ref_known(v___x_3153_, 1);
v_args_3155_ = lean_ctor_get(v_fst_3128_, 1);
v___x_3156_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__3));
v___x_3157_ = lean_box(0);
v___x_3158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3158_, 0, v_a_3154_);
lean_ctor_set(v___x_3158_, 1, v___x_3157_);
v___x_3159_ = l_Lean_mkConst(v___x_3156_, v___x_3158_);
v___x_3160_ = lean_array_get_borrowed(v___x_3147_, v_args_3155_, v_i_3131_);
lean_inc(v___x_3160_);
lean_inc(v___x_3148_);
v___x_3161_ = l_Lean_mkApp3(v___x_3159_, v_a_3150_, v___x_3148_, v___x_3160_);
v___x_3162_ = lean_array_push(v_b_3130_, v___x_3161_);
v_a_3142_ = v___x_3162_;
goto v___jp_3141_;
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_dec(v_a_3150_);
lean_dec(v_i_3131_);
lean_dec_ref(v_b_3130_);
v_a_3163_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3153_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3153_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
else
{
lean_dec(v_a_3150_);
v_a_3142_ = v_b_3130_;
goto v___jp_3141_;
}
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
lean_dec(v_i_3131_);
lean_dec_ref(v_b_3130_);
v_a_3171_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3149_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3149_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
v___jp_3141_:
{
lean_object* v___x_3143_; 
v___x_3143_ = lean_nat_add(v_i_3131_, v_step_3140_);
lean_dec(v_i_3131_);
v_b_3130_ = v_a_3142_;
v_i_3131_ = v___x_3143_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___boxed(lean_object* v_xs_3179_, lean_object* v_fst_3180_, lean_object* v_range_3181_, lean_object* v_b_3182_, lean_object* v_i_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(v_xs_3179_, v_fst_3180_, v_range_3181_, v_b_3182_, v_i_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec_ref(v_range_3181_);
lean_dec_ref(v_fst_3180_);
lean_dec_ref(v_xs_3179_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(lean_object* v_g_3192_, lean_object* v___x_3193_, lean_object* v_as_3194_, size_t v_sz_3195_, size_t v_i_3196_, lean_object* v_b_3197_){
_start:
{
uint8_t v___x_3199_; 
v___x_3199_ = lean_usize_dec_lt(v_i_3196_, v_sz_3195_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; 
lean_dec(v___x_3193_);
lean_dec(v_g_3192_);
v___x_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3200_, 0, v_b_3197_);
return v___x_3200_;
}
else
{
lean_object* v_a_3201_; lean_object* v_fst_3202_; lean_object* v_snd_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3215_; 
v_a_3201_ = lean_array_uget(v_as_3194_, v_i_3196_);
v_fst_3202_ = lean_ctor_get(v_a_3201_, 0);
v_snd_3203_ = lean_ctor_get(v_a_3201_, 1);
v_isSharedCheck_3215_ = !lean_is_exclusive(v_a_3201_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3205_ = v_a_3201_;
v_isShared_3206_ = v_isSharedCheck_3215_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_snd_3203_);
lean_inc(v_fst_3202_);
lean_dec(v_a_3201_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3215_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
lean_inc(v___x_3193_);
lean_inc(v_g_3192_);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 1, v___x_3193_);
lean_ctor_set(v___x_3205_, 0, v_g_3192_);
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_g_3192_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v___x_3193_);
v___x_3208_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; size_t v___x_3211_; size_t v___x_3212_; 
v___x_3209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
lean_ctor_set(v___x_3209_, 1, v_snd_3203_);
v___x_3210_ = lean_array_set(v_b_3197_, v_fst_3202_, v___x_3209_);
lean_dec(v_fst_3202_);
v___x_3211_ = ((size_t)1ULL);
v___x_3212_ = lean_usize_add(v_i_3196_, v___x_3211_);
v_i_3196_ = v___x_3212_;
v_b_3197_ = v___x_3210_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg___boxed(lean_object* v_g_3216_, lean_object* v___x_3217_, lean_object* v_as_3218_, lean_object* v_sz_3219_, lean_object* v_i_3220_, lean_object* v_b_3221_, lean_object* v___y_3222_){
_start:
{
size_t v_sz_boxed_3223_; size_t v_i_boxed_3224_; lean_object* v_res_3225_; 
v_sz_boxed_3223_ = lean_unbox_usize(v_sz_3219_);
lean_dec(v_sz_3219_);
v_i_boxed_3224_ = lean_unbox_usize(v_i_3220_);
lean_dec(v_i_3220_);
v_res_3225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(v_g_3216_, v___x_3217_, v_as_3218_, v_sz_boxed_3223_, v_i_boxed_3224_, v_b_3221_);
lean_dec_ref(v_as_3218_);
return v_res_3225_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3226_; 
v___x_3226_ = l_Array_instInhabited___redArg();
return v___x_3226_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1(void){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3227_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__0);
v___x_3228_ = l_Lean_Elab_Tactic_VCGen_instInhabitedJump_default;
v___x_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
lean_ctor_set(v___x_3229_, 1, v___x_3227_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5(lean_object* v_jumps_3230_, size_t v_sz_3231_, size_t v_i_3232_, lean_object* v_bs_3233_){
_start:
{
uint8_t v___x_3234_; 
v___x_3234_ = lean_usize_dec_lt(v_i_3232_, v_sz_3231_);
if (v___x_3234_ == 0)
{
return v_bs_3233_;
}
else
{
lean_object* v___x_3235_; lean_object* v_v_3236_; lean_object* v___x_3237_; lean_object* v_bs_x27_3238_; lean_object* v___x_3239_; size_t v___x_3240_; size_t v___x_3241_; lean_object* v___x_3242_; 
v___x_3235_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1);
v_v_3236_ = lean_array_uget(v_bs_3233_, v_i_3232_);
v___x_3237_ = lean_unsigned_to_nat(0u);
v_bs_x27_3238_ = lean_array_uset(v_bs_3233_, v_i_3232_, v___x_3237_);
v___x_3239_ = lean_array_get_borrowed(v___x_3235_, v_jumps_3230_, v_v_3236_);
lean_dec(v_v_3236_);
v___x_3240_ = ((size_t)1ULL);
v___x_3241_ = lean_usize_add(v_i_3232_, v___x_3240_);
lean_inc(v___x_3239_);
v___x_3242_ = lean_array_uset(v_bs_x27_3238_, v_i_3232_, v___x_3239_);
v_i_3232_ = v___x_3241_;
v_bs_3233_ = v___x_3242_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___boxed(lean_object* v_jumps_3244_, lean_object* v_sz_3245_, lean_object* v_i_3246_, lean_object* v_bs_3247_){
_start:
{
size_t v_sz_boxed_3248_; size_t v_i_boxed_3249_; lean_object* v_res_3250_; 
v_sz_boxed_3248_ = lean_unbox_usize(v_sz_3245_);
lean_dec(v_sz_3245_);
v_i_boxed_3249_ = lean_unbox_usize(v_i_3246_);
lean_dec(v_i_3246_);
v_res_3250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5(v_jumps_3244_, v_sz_boxed_3248_, v_i_boxed_3249_, v_bs_3247_);
lean_dec_ref(v_jumps_3244_);
return v_res_3250_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__1(void){
_start:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3253_ = lean_box(0);
v___x_3254_ = lean_unsigned_to_nat(16u);
v___x_3255_ = lean_mk_array(v___x_3254_, v___x_3253_);
return v___x_3255_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__2(void){
_start:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v_byLocal_3258_; 
v___x_3256_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__1, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__1);
v___x_3257_ = lean_unsigned_to_nat(0u);
v_byLocal_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byLocal_3258_, 0, v___x_3257_);
lean_ctor_set(v_byLocal_3258_, 1, v___x_3256_);
return v_byLocal_3258_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__3(void){
_start:
{
lean_object* v_byLocal_3259_; lean_object* v_groups_3260_; lean_object* v___x_3261_; 
v_byLocal_3259_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__2, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__2_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__2);
v_groups_3260_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__0));
v___x_3261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3261_, 0, v_groups_3260_);
lean_ctor_set(v___x_3261_, 1, v_byLocal_3259_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg(lean_object* v___x_3268_, lean_object* v_jumps_3269_, lean_object* v___x_3270_, lean_object* v_i_3271_, lean_object* v_xs_3272_, lean_object* v_range_3273_, lean_object* v_b_3274_, lean_object* v_i_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v_stop_3288_; lean_object* v_step_3289_; uint8_t v___x_3290_; 
v_stop_3288_ = lean_ctor_get(v_range_3273_, 1);
v_step_3289_ = lean_ctor_get(v_range_3273_, 2);
v___x_3290_ = lean_nat_dec_lt(v_i_3275_, v_stop_3288_);
if (v___x_3290_ == 0)
{
lean_object* v___x_3291_; 
lean_dec(v_i_3275_);
lean_dec(v___x_3270_);
v___x_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3291_, 0, v_b_3274_);
return v___x_3291_;
}
else
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v_fst_3297_; lean_object* v_snd_3298_; lean_object* v_fst_3299_; lean_object* v_snd_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3397_; 
v___x_3292_ = lean_unsigned_to_nat(0u);
v___x_3293_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1);
v___x_3294_ = lean_array_fget_borrowed(v___x_3268_, v_i_3275_);
v___x_3295_ = lean_array_get_borrowed(v___x_3292_, v___x_3294_, v___x_3292_);
v___x_3296_ = lean_array_get_borrowed(v___x_3293_, v_jumps_3269_, v___x_3295_);
v_fst_3297_ = lean_ctor_get(v___x_3296_, 0);
v_snd_3298_ = lean_ctor_get(v___x_3296_, 1);
v_fst_3299_ = lean_ctor_get(v_b_3274_, 0);
v_snd_3300_ = lean_ctor_get(v_b_3274_, 1);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_b_3274_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3302_ = v_b_3274_;
v_isShared_3303_ = v_isSharedCheck_3397_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_snd_3300_);
lean_inc(v_fst_3299_);
lean_dec(v_b_3274_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3397_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v_fst_3305_; lean_object* v_snd_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___x_3337_; lean_object* v___x_3338_; uint8_t v___x_3339_; 
v___x_3337_ = lean_unsigned_to_nat(1u);
v___x_3338_ = lean_array_get_size(v_snd_3298_);
v___x_3339_ = lean_nat_dec_lt(v_i_3271_, v___x_3338_);
if (v___x_3339_ == 0)
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3340_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__0));
v___x_3341_ = lean_array_get_size(v_xs_3272_);
v___x_3342_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3292_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
lean_ctor_set(v___x_3342_, 2, v___x_3337_);
v___x_3343_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(v_xs_3272_, v_fst_3297_, v___x_3342_, v___x_3340_, v___x_3292_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
lean_dec_ref_known(v___x_3342_, 3);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
lean_inc(v_a_3344_);
lean_dec_ref_known(v___x_3343_, 1);
v___x_3345_ = lean_array_to_list(v_a_3344_);
v___x_3346_ = l_Lean_mkAndN(v___x_3345_);
v___x_3347_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__1));
v_fst_3305_ = v___x_3346_;
v_snd_3306_ = v___x_3347_;
v___y_3307_ = v___y_3276_;
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
goto v___jp_3304_;
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
lean_del_object(v___x_3302_);
lean_dec(v_snd_3300_);
lean_dec(v_fst_3299_);
lean_dec(v_i_3275_);
lean_dec(v___x_3270_);
v_a_3348_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3343_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3343_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
else
{
lean_object* v___x_3356_; size_t v_sz_3357_; size_t v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3356_ = lean_array_fget_borrowed(v_snd_3298_, v_i_3271_);
v_sz_3357_ = lean_array_size(v___x_3294_);
v___x_3358_ = ((size_t)0ULL);
lean_inc(v___x_3294_);
v___x_3359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5(v_jumps_3269_, v_sz_3357_, v___x_3358_, v___x_3294_);
v___x_3360_ = lean_nat_add(v_i_3271_, v___x_3337_);
v___x_3361_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(v_xs_3272_, v___x_3359_, v___x_3360_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
lean_dec(v___x_3360_);
lean_dec_ref(v___x_3359_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v_fst_3363_; lean_object* v_snd_3364_; lean_object* v_proof_3365_; lean_object* v___x_3366_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref_known(v___x_3361_, 1);
v_fst_3363_ = lean_ctor_get(v_a_3362_, 0);
lean_inc(v_fst_3363_);
v_snd_3364_ = lean_ctor_get(v_a_3362_, 1);
lean_inc(v_snd_3364_);
lean_dec(v_a_3362_);
v_proof_3365_ = lean_ctor_get(v_fst_3297_, 0);
lean_inc(v_proof_3365_);
v___x_3366_ = l_Lean_MVarId_getDecl(v_proof_3365_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v_lctx_3368_; lean_object* v_localInstances_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_a_3367_);
lean_dec_ref_known(v___x_3366_, 1);
v_lctx_3368_ = lean_ctor_get(v_a_3367_, 1);
lean_inc_ref(v_lctx_3368_);
v_localInstances_3369_ = lean_ctor_get(v_a_3367_, 4);
lean_inc_ref(v_localInstances_3369_);
lean_dec(v_a_3367_);
lean_inc(v___x_3356_);
v___x_3370_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___boxed), 14, 2);
lean_closure_set(v___x_3370_, 0, v___x_3356_);
lean_closure_set(v___x_3370_, 1, v_fst_3363_);
v___x_3371_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(v_lctx_3368_, v_localInstances_3369_, v___x_3370_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_a_3372_; 
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
lean_inc(v_a_3372_);
lean_dec_ref_known(v___x_3371_, 1);
v_fst_3305_ = v_a_3372_;
v_snd_3306_ = v_snd_3364_;
v___y_3307_ = v___y_3276_;
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
goto v___jp_3304_;
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
lean_dec(v_snd_3364_);
lean_del_object(v___x_3302_);
lean_dec(v_snd_3300_);
lean_dec(v_fst_3299_);
lean_dec(v_i_3275_);
lean_dec(v___x_3270_);
v_a_3373_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3371_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3371_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
lean_dec(v_snd_3364_);
lean_dec(v_fst_3363_);
lean_del_object(v___x_3302_);
lean_dec(v_snd_3300_);
lean_dec(v_fst_3299_);
lean_dec(v_i_3275_);
lean_dec(v___x_3270_);
v_a_3381_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3366_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3366_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_del_object(v___x_3302_);
lean_dec(v_snd_3300_);
lean_dec(v_fst_3299_);
lean_dec(v_i_3275_);
lean_dec(v___x_3270_);
v_a_3389_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3361_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3361_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
v___jp_3304_:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; size_t v_sz_3320_; size_t v___x_3321_; lean_object* v___x_3322_; 
v___x_3318_ = lean_array_push(v_fst_3299_, v_fst_3305_);
v___x_3319_ = l_Array_zip___redArg(v___x_3294_, v_snd_3306_);
lean_dec_ref(v_snd_3306_);
v_sz_3320_ = lean_array_size(v___x_3319_);
v___x_3321_ = ((size_t)0ULL);
lean_inc(v___x_3270_);
lean_inc(v_i_3275_);
v___x_3322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(v_i_3275_, v___x_3270_, v___x_3319_, v_sz_3320_, v___x_3321_, v_snd_3300_);
lean_dec_ref(v___x_3319_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; lean_object* v___x_3325_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3323_);
lean_dec_ref_known(v___x_3322_, 1);
if (v_isShared_3303_ == 0)
{
lean_ctor_set(v___x_3302_, 1, v_a_3323_);
lean_ctor_set(v___x_3302_, 0, v___x_3318_);
v___x_3325_ = v___x_3302_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3318_);
lean_ctor_set(v_reuseFailAlloc_3328_, 1, v_a_3323_);
v___x_3325_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
lean_object* v___x_3326_; 
v___x_3326_ = lean_nat_add(v_i_3275_, v_step_3289_);
lean_dec(v_i_3275_);
v_b_3274_ = v___x_3325_;
v_i_3275_ = v___x_3326_;
goto _start;
}
}
else
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
lean_dec_ref(v___x_3318_);
lean_del_object(v___x_3302_);
lean_dec(v_i_3275_);
lean_dec(v___x_3270_);
v_a_3329_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___x_3322_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3322_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_a_3329_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg(lean_object* v___x_3398_, lean_object* v___x_3399_, lean_object* v_jumps_3400_, lean_object* v_xs_3401_, lean_object* v_i_3402_, lean_object* v_range_3403_, lean_object* v_b_3404_, lean_object* v_i_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v_stop_3418_; lean_object* v_step_3419_; uint8_t v___x_3420_; 
v_stop_3418_ = lean_ctor_get(v_range_3403_, 1);
v_step_3419_ = lean_ctor_get(v_range_3403_, 2);
v___x_3420_ = lean_nat_dec_lt(v_i_3405_, v_stop_3418_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; 
lean_dec(v_i_3405_);
lean_dec(v___x_3398_);
v___x_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3421_, 0, v_b_3404_);
return v___x_3421_;
}
else
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v_fst_3427_; lean_object* v_snd_3428_; lean_object* v_fst_3429_; lean_object* v_snd_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3528_; 
v___x_3422_ = lean_unsigned_to_nat(0u);
v___x_3423_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5___closed__1);
v___x_3424_ = lean_array_fget_borrowed(v___x_3399_, v_i_3405_);
v___x_3425_ = lean_array_get_borrowed(v___x_3422_, v___x_3424_, v___x_3422_);
v___x_3426_ = lean_array_get_borrowed(v___x_3423_, v_jumps_3400_, v___x_3425_);
v_fst_3427_ = lean_ctor_get(v___x_3426_, 0);
v_snd_3428_ = lean_ctor_get(v___x_3426_, 1);
v_fst_3429_ = lean_ctor_get(v_b_3404_, 0);
v_snd_3430_ = lean_ctor_get(v_b_3404_, 1);
v_isSharedCheck_3528_ = !lean_is_exclusive(v_b_3404_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3432_ = v_b_3404_;
v_isShared_3433_ = v_isSharedCheck_3528_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_snd_3430_);
lean_inc(v_fst_3429_);
lean_dec(v_b_3404_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3528_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v_fst_3435_; lean_object* v_snd_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___x_3467_; lean_object* v___x_3468_; uint8_t v___x_3469_; 
v___x_3467_ = lean_unsigned_to_nat(1u);
v___x_3468_ = lean_array_get_size(v_snd_3428_);
v___x_3469_ = lean_nat_dec_lt(v_i_3402_, v___x_3468_);
if (v___x_3469_ == 0)
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3470_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__0));
v___x_3471_ = lean_array_get_size(v_xs_3401_);
v___x_3472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3422_);
lean_ctor_set(v___x_3472_, 1, v___x_3471_);
lean_ctor_set(v___x_3472_, 2, v___x_3467_);
v___x_3473_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(v_xs_3401_, v_fst_3427_, v___x_3472_, v___x_3470_, v___x_3422_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
lean_dec_ref_known(v___x_3472_, 3);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_a_3474_);
lean_dec_ref_known(v___x_3473_, 1);
v___x_3475_ = lean_array_to_list(v_a_3474_);
v___x_3476_ = l_Lean_mkAndN(v___x_3475_);
v___x_3477_ = lean_mk_empty_array_with_capacity(v___x_3467_);
lean_dec_ref(v___x_3477_);
v___x_3478_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___closed__1));
v_fst_3435_ = v___x_3476_;
v_snd_3436_ = v___x_3478_;
v___y_3437_ = v___y_3406_;
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
goto v___jp_3434_;
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_del_object(v___x_3432_);
lean_dec(v_snd_3430_);
lean_dec(v_fst_3429_);
lean_dec(v_i_3405_);
lean_dec(v___x_3398_);
v_a_3479_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3473_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3473_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
else
{
lean_object* v___x_3487_; size_t v_sz_3488_; size_t v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3487_ = lean_array_fget_borrowed(v_snd_3428_, v_i_3402_);
v_sz_3488_ = lean_array_size(v___x_3424_);
v___x_3489_ = ((size_t)0ULL);
lean_inc(v___x_3424_);
v___x_3490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__5(v_jumps_3400_, v_sz_3488_, v___x_3489_, v___x_3424_);
v___x_3491_ = lean_nat_add(v_i_3402_, v___x_3467_);
v___x_3492_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(v_xs_3401_, v___x_3490_, v___x_3491_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
lean_dec(v___x_3491_);
lean_dec_ref(v___x_3490_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v_fst_3494_; lean_object* v_snd_3495_; lean_object* v_proof_3496_; lean_object* v___x_3497_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v___x_3492_, 1);
v_fst_3494_ = lean_ctor_get(v_a_3493_, 0);
lean_inc(v_fst_3494_);
v_snd_3495_ = lean_ctor_get(v_a_3493_, 1);
lean_inc(v_snd_3495_);
lean_dec(v_a_3493_);
v_proof_3496_ = lean_ctor_get(v_fst_3427_, 0);
lean_inc(v_proof_3496_);
v___x_3497_ = l_Lean_MVarId_getDecl(v_proof_3496_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v_lctx_3499_; lean_object* v_localInstances_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___x_3497_, 1);
v_lctx_3499_ = lean_ctor_get(v_a_3498_, 1);
lean_inc_ref(v_lctx_3499_);
v_localInstances_3500_ = lean_ctor_get(v_a_3498_, 4);
lean_inc_ref(v_localInstances_3500_);
lean_dec(v_a_3498_);
lean_inc(v___x_3487_);
v___x_3501_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___boxed), 14, 2);
lean_closure_set(v___x_3501_, 0, v___x_3487_);
lean_closure_set(v___x_3501_, 1, v_fst_3494_);
v___x_3502_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__6___redArg(v_lctx_3499_, v_localInstances_3500_, v___x_3501_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3503_);
lean_dec_ref_known(v___x_3502_, 1);
v_fst_3435_ = v_a_3503_;
v_snd_3436_ = v_snd_3495_;
v___y_3437_ = v___y_3406_;
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
goto v___jp_3434_;
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_dec(v_snd_3495_);
lean_del_object(v___x_3432_);
lean_dec(v_snd_3430_);
lean_dec(v_fst_3429_);
lean_dec(v_i_3405_);
lean_dec(v___x_3398_);
v_a_3504_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3502_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3502_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
lean_dec(v_snd_3495_);
lean_dec(v_fst_3494_);
lean_del_object(v___x_3432_);
lean_dec(v_snd_3430_);
lean_dec(v_fst_3429_);
lean_dec(v_i_3405_);
lean_dec(v___x_3398_);
v_a_3512_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3497_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3497_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_del_object(v___x_3432_);
lean_dec(v_snd_3430_);
lean_dec(v_fst_3429_);
lean_dec(v_i_3405_);
lean_dec(v___x_3398_);
v_a_3520_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3492_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3492_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
v___jp_3434_:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; size_t v_sz_3450_; size_t v___x_3451_; lean_object* v___x_3452_; 
v___x_3448_ = lean_array_push(v_fst_3429_, v_fst_3435_);
v___x_3449_ = l_Array_zip___redArg(v___x_3424_, v_snd_3436_);
lean_dec_ref(v_snd_3436_);
v_sz_3450_ = lean_array_size(v___x_3449_);
v___x_3451_ = ((size_t)0ULL);
lean_inc(v___x_3398_);
lean_inc(v_i_3405_);
v___x_3452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(v_i_3405_, v___x_3398_, v___x_3449_, v_sz_3450_, v___x_3451_, v_snd_3430_);
lean_dec_ref(v___x_3449_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; lean_object* v___x_3455_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3453_);
lean_dec_ref_known(v___x_3452_, 1);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v_a_3453_);
lean_ctor_set(v___x_3432_, 0, v___x_3448_);
v___x_3455_ = v___x_3432_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3448_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_a_3453_);
v___x_3455_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3456_ = lean_nat_add(v_i_3405_, v_step_3419_);
lean_dec(v_i_3405_);
v___x_3457_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg(v___x_3399_, v_jumps_3400_, v___x_3398_, v_i_3402_, v_xs_3401_, v_range_3403_, v___x_3455_, v___x_3456_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
return v___x_3457_;
}
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec_ref(v___x_3448_);
lean_del_object(v___x_3432_);
lean_dec(v_i_3405_);
lean_dec(v___x_3398_);
v_a_3459_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3452_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3452_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(lean_object* v_xs_3529_, lean_object* v_jumps_3530_, lean_object* v_i_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_){
_start:
{
lean_object* v___x_3544_; lean_object* v_groups_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3544_ = lean_unsigned_to_nat(0u);
v_groups_3545_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__0));
v___x_3546_ = lean_array_get_size(v_jumps_3530_);
v___x_3547_ = lean_unsigned_to_nat(1u);
v___x_3548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3544_);
lean_ctor_set(v___x_3548_, 1, v___x_3546_);
lean_ctor_set(v___x_3548_, 2, v___x_3547_);
v___x_3549_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__3, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___closed__3);
v___x_3550_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg(v_jumps_3530_, v_i_3531_, v___x_3548_, v___x_3549_, v___x_3544_);
lean_dec_ref_known(v___x_3548_, 3);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v_fst_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3591_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3551_);
lean_dec_ref_known(v___x_3550_, 1);
v_fst_3552_ = lean_ctor_get(v_a_3551_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v_a_3551_);
if (v_isSharedCheck_3591_ == 0)
{
lean_object* v_unused_3592_; 
v_unused_3592_ = lean_ctor_get(v_a_3551_, 1);
lean_dec(v_unused_3592_);
v___x_3554_ = v_a_3551_;
v_isShared_3555_ = v_isSharedCheck_3591_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_fst_3552_);
lean_dec(v_a_3551_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3591_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3561_; 
v___x_3556_ = lean_box(0);
v___x_3557_ = lean_mk_array(v___x_3546_, v___x_3556_);
v___x_3558_ = lean_array_get_size(v_fst_3552_);
v___x_3559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3544_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
lean_ctor_set(v___x_3559_, 2, v___x_3547_);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 1, v___x_3557_);
lean_ctor_set(v___x_3554_, 0, v_groups_3545_);
v___x_3561_ = v___x_3554_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_groups_3545_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v___x_3557_);
v___x_3561_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
lean_object* v___x_3562_; 
v___x_3562_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg(v___x_3558_, v_fst_3552_, v_jumps_3530_, v_xs_3529_, v_i_3531_, v___x_3559_, v___x_3561_, v___x_3544_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
lean_dec_ref_known(v___x_3559_, 3);
lean_dec(v_fst_3552_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3581_; 
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3565_ = v___x_3562_;
v_isShared_3566_ = v_isSharedCheck_3581_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3562_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3581_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v_fst_3567_; lean_object* v_snd_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3580_; 
v_fst_3567_ = lean_ctor_get(v_a_3563_, 0);
v_snd_3568_ = lean_ctor_get(v_a_3563_, 1);
v_isSharedCheck_3580_ = !lean_is_exclusive(v_a_3563_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3570_ = v_a_3563_;
v_isShared_3571_ = v_isSharedCheck_3580_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_snd_3568_);
lean_inc(v_fst_3567_);
lean_dec(v_a_3563_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3580_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3575_; 
v___x_3572_ = lean_array_get_size(v_fst_3567_);
v___x_3573_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrTree(v_fst_3567_, v___x_3544_, v___x_3572_);
lean_dec(v_fst_3567_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 0, v___x_3573_);
v___x_3575_ = v___x_3570_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3573_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_snd_3568_);
v___x_3575_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
lean_object* v___x_3577_; 
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 0, v___x_3575_);
v___x_3577_ = v___x_3565_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3575_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
}
else
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
v_a_3582_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v___x_3562_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3562_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
}
}
else
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3600_; 
v_a_3593_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3595_ = v___x_3550_;
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v___x_3550_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3598_; 
if (v_isShared_3596_ == 0)
{
v___x_3598_ = v___x_3595_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3593_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie___boxed(lean_object* v_xs_3601_, lean_object* v_jumps_3602_, lean_object* v_i_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(v_xs_3601_, v_jumps_3602_, v_i_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_);
lean_dec(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec(v_a_3612_);
lean_dec_ref(v_a_3611_);
lean_dec(v_a_3610_);
lean_dec_ref(v_a_3609_);
lean_dec(v_a_3608_);
lean_dec_ref(v_a_3607_);
lean_dec(v_a_3606_);
lean_dec(v_a_3605_);
lean_dec_ref(v_a_3604_);
lean_dec(v_i_3603_);
lean_dec_ref(v_jumps_3602_);
lean_dec_ref(v_xs_3601_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg___boxed(lean_object** _args){
lean_object* v___x_3617_ = _args[0];
lean_object* v_jumps_3618_ = _args[1];
lean_object* v___x_3619_ = _args[2];
lean_object* v_i_3620_ = _args[3];
lean_object* v_xs_3621_ = _args[4];
lean_object* v_range_3622_ = _args[5];
lean_object* v_b_3623_ = _args[6];
lean_object* v_i_3624_ = _args[7];
lean_object* v___y_3625_ = _args[8];
lean_object* v___y_3626_ = _args[9];
lean_object* v___y_3627_ = _args[10];
lean_object* v___y_3628_ = _args[11];
lean_object* v___y_3629_ = _args[12];
lean_object* v___y_3630_ = _args[13];
lean_object* v___y_3631_ = _args[14];
lean_object* v___y_3632_ = _args[15];
lean_object* v___y_3633_ = _args[16];
lean_object* v___y_3634_ = _args[17];
lean_object* v___y_3635_ = _args[18];
lean_object* v___y_3636_ = _args[19];
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg(v___x_3617_, v_jumps_3618_, v___x_3619_, v_i_3620_, v_xs_3621_, v_range_3622_, v_b_3623_, v_i_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec_ref(v_range_3622_);
lean_dec_ref(v_xs_3621_);
lean_dec(v_i_3620_);
lean_dec_ref(v_jumps_3618_);
lean_dec_ref(v___x_3617_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg___boxed(lean_object** _args){
lean_object* v___x_3638_ = _args[0];
lean_object* v___x_3639_ = _args[1];
lean_object* v_jumps_3640_ = _args[2];
lean_object* v_xs_3641_ = _args[3];
lean_object* v_i_3642_ = _args[4];
lean_object* v_range_3643_ = _args[5];
lean_object* v_b_3644_ = _args[6];
lean_object* v_i_3645_ = _args[7];
lean_object* v___y_3646_ = _args[8];
lean_object* v___y_3647_ = _args[9];
lean_object* v___y_3648_ = _args[10];
lean_object* v___y_3649_ = _args[11];
lean_object* v___y_3650_ = _args[12];
lean_object* v___y_3651_ = _args[13];
lean_object* v___y_3652_ = _args[14];
lean_object* v___y_3653_ = _args[15];
lean_object* v___y_3654_ = _args[16];
lean_object* v___y_3655_ = _args[17];
lean_object* v___y_3656_ = _args[18];
lean_object* v___y_3657_ = _args[19];
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg(v___x_3638_, v___x_3639_, v_jumps_3640_, v_xs_3641_, v_i_3642_, v_range_3643_, v_b_3644_, v_i_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec_ref(v_range_3643_);
lean_dec(v_i_3642_);
lean_dec_ref(v_xs_3641_);
lean_dec_ref(v_jumps_3640_);
lean_dec_ref(v___x_3639_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0(lean_object* v_00_u03b2_3659_, lean_object* v_m_3660_, lean_object* v_a_3661_){
_start:
{
lean_object* v___x_3662_; 
v___x_3662_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___redArg(v_m_3660_, v_a_3661_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0___boxed(lean_object* v_00_u03b2_3663_, lean_object* v_m_3664_, lean_object* v_a_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0(v_00_u03b2_3663_, v_m_3664_, v_a_3665_);
lean_dec(v_a_3665_);
lean_dec_ref(v_m_3664_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1(lean_object* v_00_u03b2_3667_, lean_object* v_m_3668_, lean_object* v_a_3669_, lean_object* v_b_3670_){
_start:
{
lean_object* v___x_3671_; 
v___x_3671_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1___redArg(v_m_3668_, v_a_3669_, v_b_3670_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2(lean_object* v_jumps_3672_, lean_object* v_i_3673_, lean_object* v_range_3674_, lean_object* v_b_3675_, lean_object* v_i_3676_, lean_object* v_hs_3677_, lean_object* v_hl_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
lean_object* v___x_3691_; 
v___x_3691_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___redArg(v_jumps_3672_, v_i_3673_, v_range_3674_, v_b_3675_, v_i_3676_);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2___boxed(lean_object** _args){
lean_object* v_jumps_3692_ = _args[0];
lean_object* v_i_3693_ = _args[1];
lean_object* v_range_3694_ = _args[2];
lean_object* v_b_3695_ = _args[3];
lean_object* v_i_3696_ = _args[4];
lean_object* v_hs_3697_ = _args[5];
lean_object* v_hl_3698_ = _args[6];
lean_object* v___y_3699_ = _args[7];
lean_object* v___y_3700_ = _args[8];
lean_object* v___y_3701_ = _args[9];
lean_object* v___y_3702_ = _args[10];
lean_object* v___y_3703_ = _args[11];
lean_object* v___y_3704_ = _args[12];
lean_object* v___y_3705_ = _args[13];
lean_object* v___y_3706_ = _args[14];
lean_object* v___y_3707_ = _args[15];
lean_object* v___y_3708_ = _args[16];
lean_object* v___y_3709_ = _args[17];
lean_object* v___y_3710_ = _args[18];
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__2(v_jumps_3692_, v_i_3693_, v_range_3694_, v_b_3695_, v_i_3696_, v_hs_3697_, v_hl_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v___y_3701_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec_ref(v_range_3694_);
lean_dec(v_i_3693_);
lean_dec_ref(v_jumps_3692_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3(lean_object* v_g_3712_, lean_object* v___x_3713_, lean_object* v_as_3714_, size_t v_sz_3715_, size_t v_i_3716_, lean_object* v_b_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___redArg(v_g_3712_, v___x_3713_, v_as_3714_, v_sz_3715_, v_i_3716_, v_b_3717_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3___boxed(lean_object** _args){
lean_object* v_g_3731_ = _args[0];
lean_object* v___x_3732_ = _args[1];
lean_object* v_as_3733_ = _args[2];
lean_object* v_sz_3734_ = _args[3];
lean_object* v_i_3735_ = _args[4];
lean_object* v_b_3736_ = _args[5];
lean_object* v___y_3737_ = _args[6];
lean_object* v___y_3738_ = _args[7];
lean_object* v___y_3739_ = _args[8];
lean_object* v___y_3740_ = _args[9];
lean_object* v___y_3741_ = _args[10];
lean_object* v___y_3742_ = _args[11];
lean_object* v___y_3743_ = _args[12];
lean_object* v___y_3744_ = _args[13];
lean_object* v___y_3745_ = _args[14];
lean_object* v___y_3746_ = _args[15];
lean_object* v___y_3747_ = _args[16];
lean_object* v___y_3748_ = _args[17];
_start:
{
size_t v_sz_boxed_3749_; size_t v_i_boxed_3750_; lean_object* v_res_3751_; 
v_sz_boxed_3749_ = lean_unbox_usize(v_sz_3734_);
lean_dec(v_sz_3734_);
v_i_boxed_3750_ = lean_unbox_usize(v_i_3735_);
lean_dec(v_i_3735_);
v_res_3751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__3(v_g_3731_, v___x_3732_, v_as_3733_, v_sz_boxed_3749_, v_i_boxed_3750_, v_b_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec_ref(v_as_3733_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4(lean_object* v_xs_3752_, lean_object* v_fst_3753_, lean_object* v_range_3754_, lean_object* v_b_3755_, lean_object* v_i_3756_, lean_object* v_hs_3757_, lean_object* v_hl_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
lean_object* v___x_3771_; 
v___x_3771_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg(v_xs_3752_, v_fst_3753_, v_range_3754_, v_b_3755_, v_i_3756_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___boxed(lean_object** _args){
lean_object* v_xs_3772_ = _args[0];
lean_object* v_fst_3773_ = _args[1];
lean_object* v_range_3774_ = _args[2];
lean_object* v_b_3775_ = _args[3];
lean_object* v_i_3776_ = _args[4];
lean_object* v_hs_3777_ = _args[5];
lean_object* v_hl_3778_ = _args[6];
lean_object* v___y_3779_ = _args[7];
lean_object* v___y_3780_ = _args[8];
lean_object* v___y_3781_ = _args[9];
lean_object* v___y_3782_ = _args[10];
lean_object* v___y_3783_ = _args[11];
lean_object* v___y_3784_ = _args[12];
lean_object* v___y_3785_ = _args[13];
lean_object* v___y_3786_ = _args[14];
lean_object* v___y_3787_ = _args[15];
lean_object* v___y_3788_ = _args[16];
lean_object* v___y_3789_ = _args[17];
lean_object* v___y_3790_ = _args[18];
_start:
{
lean_object* v_res_3791_; 
v_res_3791_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4(v_xs_3772_, v_fst_3773_, v_range_3774_, v_b_3775_, v_i_3776_, v_hs_3777_, v_hl_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec_ref(v_range_3774_);
lean_dec_ref(v_fst_3773_);
lean_dec_ref(v_xs_3772_);
return v_res_3791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7(lean_object* v___x_3792_, lean_object* v___x_3793_, lean_object* v_jumps_3794_, lean_object* v_xs_3795_, lean_object* v_i_3796_, lean_object* v_range_3797_, lean_object* v_b_3798_, lean_object* v_i_3799_, lean_object* v_hs_3800_, lean_object* v_hl_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v___x_3814_; 
v___x_3814_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___redArg(v___x_3792_, v___x_3793_, v_jumps_3794_, v_xs_3795_, v_i_3796_, v_range_3797_, v_b_3798_, v_i_3799_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7___boxed(lean_object** _args){
lean_object* v___x_3815_ = _args[0];
lean_object* v___x_3816_ = _args[1];
lean_object* v_jumps_3817_ = _args[2];
lean_object* v_xs_3818_ = _args[3];
lean_object* v_i_3819_ = _args[4];
lean_object* v_range_3820_ = _args[5];
lean_object* v_b_3821_ = _args[6];
lean_object* v_i_3822_ = _args[7];
lean_object* v_hs_3823_ = _args[8];
lean_object* v_hl_3824_ = _args[9];
lean_object* v___y_3825_ = _args[10];
lean_object* v___y_3826_ = _args[11];
lean_object* v___y_3827_ = _args[12];
lean_object* v___y_3828_ = _args[13];
lean_object* v___y_3829_ = _args[14];
lean_object* v___y_3830_ = _args[15];
lean_object* v___y_3831_ = _args[16];
lean_object* v___y_3832_ = _args[17];
lean_object* v___y_3833_ = _args[18];
lean_object* v___y_3834_ = _args[19];
lean_object* v___y_3835_ = _args[20];
lean_object* v___y_3836_ = _args[21];
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7(v___x_3815_, v___x_3816_, v_jumps_3817_, v_xs_3818_, v_i_3819_, v_range_3820_, v_b_3821_, v_i_3822_, v_hs_3823_, v_hl_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec(v___y_3827_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec_ref(v_range_3820_);
lean_dec(v_i_3819_);
lean_dec_ref(v_xs_3818_);
lean_dec_ref(v_jumps_3817_);
lean_dec_ref(v___x_3816_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0(lean_object* v_00_u03b2_3838_, lean_object* v_a_3839_, lean_object* v_x_3840_){
_start:
{
lean_object* v___x_3841_; 
v___x_3841_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___redArg(v_a_3839_, v_x_3840_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3842_, lean_object* v_a_3843_, lean_object* v_x_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__0_spec__0(v_00_u03b2_3842_, v_a_3843_, v_x_3844_);
lean_dec(v_x_3844_);
lean_dec(v_a_3843_);
return v_res_3845_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2(lean_object* v_00_u03b2_3846_, lean_object* v_a_3847_, lean_object* v_x_3848_){
_start:
{
uint8_t v___x_3849_; 
v___x_3849_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___redArg(v_a_3847_, v_x_3848_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3850_, lean_object* v_a_3851_, lean_object* v_x_3852_){
_start:
{
uint8_t v_res_3853_; lean_object* v_r_3854_; 
v_res_3853_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__2(v_00_u03b2_3850_, v_a_3851_, v_x_3852_);
lean_dec(v_x_3852_);
lean_dec(v_a_3851_);
v_r_3854_ = lean_box(v_res_3853_);
return v_r_3854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3(lean_object* v_00_u03b2_3855_, lean_object* v_data_3856_){
_start:
{
lean_object* v___x_3857_; 
v___x_3857_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3___redArg(v_data_3856_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4(lean_object* v_00_u03b2_3858_, lean_object* v_a_3859_, lean_object* v_b_3860_, lean_object* v_x_3861_){
_start:
{
lean_object* v___x_3862_; 
v___x_3862_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__4___redArg(v_a_3859_, v_b_3860_, v_x_3861_);
return v___x_3862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11(lean_object* v___x_3863_, lean_object* v_jumps_3864_, lean_object* v___x_3865_, lean_object* v_i_3866_, lean_object* v_xs_3867_, lean_object* v_range_3868_, lean_object* v_b_3869_, lean_object* v_i_3870_, lean_object* v_hs_3871_, lean_object* v_hl_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v___x_3885_; 
v___x_3885_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___redArg(v___x_3863_, v_jumps_3864_, v___x_3865_, v_i_3866_, v_xs_3867_, v_range_3868_, v_b_3869_, v_i_3870_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11___boxed(lean_object** _args){
lean_object* v___x_3886_ = _args[0];
lean_object* v_jumps_3887_ = _args[1];
lean_object* v___x_3888_ = _args[2];
lean_object* v_i_3889_ = _args[3];
lean_object* v_xs_3890_ = _args[4];
lean_object* v_range_3891_ = _args[5];
lean_object* v_b_3892_ = _args[6];
lean_object* v_i_3893_ = _args[7];
lean_object* v_hs_3894_ = _args[8];
lean_object* v_hl_3895_ = _args[9];
lean_object* v___y_3896_ = _args[10];
lean_object* v___y_3897_ = _args[11];
lean_object* v___y_3898_ = _args[12];
lean_object* v___y_3899_ = _args[13];
lean_object* v___y_3900_ = _args[14];
lean_object* v___y_3901_ = _args[15];
lean_object* v___y_3902_ = _args[16];
lean_object* v___y_3903_ = _args[17];
lean_object* v___y_3904_ = _args[18];
lean_object* v___y_3905_ = _args[19];
lean_object* v___y_3906_ = _args[20];
lean_object* v___y_3907_ = _args[21];
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__7_spec__11(v___x_3886_, v_jumps_3887_, v___x_3888_, v_i_3889_, v_xs_3890_, v_range_3891_, v_b_3892_, v_i_3893_, v_hs_3894_, v_hl_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec_ref(v_range_3891_);
lean_dec_ref(v_xs_3890_);
lean_dec(v_i_3889_);
lean_dec_ref(v_jumps_3887_);
lean_dec_ref(v___x_3886_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_3909_, lean_object* v_i_3910_, lean_object* v_source_3911_, lean_object* v_target_3912_){
_start:
{
lean_object* v___x_3913_; 
v___x_3913_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5___redArg(v_i_3910_, v_source_3911_, v_target_3912_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_3914_, lean_object* v_x_3915_, lean_object* v_x_3916_){
_start:
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__1_spec__3_spec__5_spec__11___redArg(v_x_3915_, v_x_3916_);
return v___x_3917_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__1(void){
_start:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3919_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__0));
v___x_3920_ = l_Lean_stringToMessageData(v___x_3919_);
return v___x_3920_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10(void){
_start:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3935_ = lean_box(0);
v___x_3936_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__9));
v___x_3937_ = l_Lean_mkConst(v___x_3936_, v___x_3935_);
return v___x_3937_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__12(void){
_start:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v___x_3941_ = lean_box(0);
v___x_3942_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__11));
v___x_3943_ = l_Lean_mkConst(v___x_3942_, v___x_3941_);
return v___x_3943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(lean_object* v_00_u03c6_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_){
_start:
{
lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___x_3959_; 
lean_inc_ref(v_00_u03c6_3944_);
v___x_3959_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_00_u03c6_3944_, v_a_3946_);
if (lean_obj_tag(v___x_3959_) == 0)
{
lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_4005_; 
v_a_3960_ = lean_ctor_get(v___x_3959_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3959_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_3962_ = v___x_3959_;
v_isShared_3963_ = v_isSharedCheck_4005_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___x_3959_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_4005_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; uint8_t v___x_3966_; 
v___x_3964_ = l_Lean_Expr_cleanupAnnotations(v_a_3960_);
lean_dec(v_a_3960_);
v___x_3965_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__3));
v___x_3966_ = l_Lean_Expr_isConstOf(v___x_3964_, v___x_3965_);
if (v___x_3966_ == 0)
{
uint8_t v___x_3967_; 
v___x_3967_ = l_Lean_Expr_isApp(v___x_3964_);
if (v___x_3967_ == 0)
{
lean_dec_ref(v___x_3964_);
lean_del_object(v___x_3962_);
v___y_3951_ = v_a_3945_;
v___y_3952_ = v_a_3946_;
v___y_3953_ = v_a_3947_;
v___y_3954_ = v_a_3948_;
goto v___jp_3950_;
}
else
{
lean_object* v___x_3968_; uint8_t v___x_3969_; 
v___x_3968_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3964_);
v___x_3969_ = l_Lean_Expr_isApp(v___x_3968_);
if (v___x_3969_ == 0)
{
lean_dec_ref(v___x_3968_);
lean_dec_ref(v___x_3964_);
lean_del_object(v___x_3962_);
v___y_3951_ = v_a_3945_;
v___y_3952_ = v_a_3946_;
v___y_3953_ = v_a_3947_;
v___y_3954_ = v_a_3948_;
goto v___jp_3950_;
}
else
{
lean_object* v_arg_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; uint8_t v___x_3973_; 
v_arg_3970_ = lean_ctor_get(v___x_3968_, 1);
lean_inc_ref(v_arg_3970_);
v___x_3971_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3968_);
lean_dec_ref(v___x_3968_);
v___x_3972_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__5));
v___x_3973_ = l_Lean_Expr_isConstOf(v___x_3971_, v___x_3972_);
if (v___x_3973_ == 0)
{
uint8_t v___x_3974_; 
lean_dec_ref(v___x_3964_);
v___x_3974_ = l_Lean_Expr_isApp(v___x_3971_);
if (v___x_3974_ == 0)
{
lean_dec_ref(v___x_3971_);
lean_dec_ref(v_arg_3970_);
lean_del_object(v___x_3962_);
v___y_3951_ = v_a_3945_;
v___y_3952_ = v_a_3946_;
v___y_3953_ = v_a_3947_;
v___y_3954_ = v_a_3948_;
goto v___jp_3950_;
}
else
{
lean_object* v___x_3975_; lean_object* v___x_3976_; uint8_t v___x_3977_; 
v___x_3975_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3971_);
v___x_3976_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie_spec__4___redArg___closed__3));
v___x_3977_ = l_Lean_Expr_isConstOf(v___x_3975_, v___x_3976_);
lean_dec_ref(v___x_3975_);
if (v___x_3977_ == 0)
{
lean_dec_ref(v___x_3971_);
lean_dec_ref(v_arg_3970_);
lean_del_object(v___x_3962_);
v___y_3951_ = v_a_3945_;
v___y_3952_ = v_a_3946_;
v___y_3953_ = v_a_3947_;
v___y_3954_ = v_a_3948_;
goto v___jp_3950_;
}
else
{
lean_object* v_arg_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3985_; 
v_arg_3978_ = lean_ctor_get(v___x_3971_, 1);
lean_inc_ref(v_arg_3978_);
lean_dec_ref(v___x_3971_);
v___x_3979_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__7));
v___x_3980_ = l_Lean_Expr_getAppFn(v_00_u03c6_3944_);
lean_dec_ref(v_00_u03c6_3944_);
v___x_3981_ = l_Lean_Expr_constLevels_x21(v___x_3980_);
lean_dec_ref(v___x_3980_);
v___x_3982_ = l_Lean_mkConst(v___x_3979_, v___x_3981_);
v___x_3983_ = l_Lean_mkAppB(v___x_3982_, v_arg_3978_, v_arg_3970_);
if (v_isShared_3963_ == 0)
{
lean_ctor_set(v___x_3962_, 0, v___x_3983_);
v___x_3985_ = v___x_3962_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v___x_3983_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
else
{
lean_object* v_arg_3987_; lean_object* v___x_3988_; 
lean_dec_ref(v___x_3971_);
lean_del_object(v___x_3962_);
lean_dec_ref(v_00_u03c6_3944_);
v_arg_3987_ = lean_ctor_get(v___x_3964_, 1);
lean_inc_ref(v_arg_3987_);
lean_dec_ref(v___x_3964_);
lean_inc_ref(v_arg_3970_);
v___x_3988_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(v_arg_3970_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v_a_3989_; lean_object* v___x_3990_; 
v_a_3989_ = lean_ctor_get(v___x_3988_, 0);
lean_inc(v_a_3989_);
lean_dec_ref_known(v___x_3988_, 1);
lean_inc_ref(v_arg_3987_);
v___x_3990_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(v_arg_3987_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_4000_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3993_ = v___x_3990_;
v_isShared_3994_ = v_isSharedCheck_4000_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3990_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_4000_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3998_; 
v___x_3995_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10);
v___x_3996_ = l_Lean_mkApp4(v___x_3995_, v_arg_3970_, v_arg_3987_, v_a_3989_, v_a_3991_);
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 0, v___x_3996_);
v___x_3998_ = v___x_3993_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3996_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
else
{
lean_dec(v_a_3989_);
lean_dec_ref(v_arg_3987_);
lean_dec_ref(v_arg_3970_);
return v___x_3990_;
}
}
else
{
lean_dec_ref(v_arg_3987_);
lean_dec_ref(v_arg_3970_);
return v___x_3988_;
}
}
}
}
}
else
{
lean_object* v___x_4001_; lean_object* v___x_4003_; 
lean_dec_ref(v___x_3964_);
lean_dec_ref(v_00_u03c6_3944_);
v___x_4001_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__12, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__12_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__12);
if (v_isShared_3963_ == 0)
{
lean_ctor_set(v___x_3962_, 0, v___x_4001_);
v___x_4003_ = v___x_3962_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v___x_4001_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
else
{
lean_dec_ref(v_00_u03c6_3944_);
return v___x_3959_;
}
v___jp_3950_:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3955_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__1, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__1);
v___x_3956_ = l_Lean_indentExpr(v_00_u03c6_3944_);
v___x_3957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3955_);
lean_ctor_set(v___x_3957_, 1, v___x_3956_);
v___x_3958_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v___x_3957_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
return v___x_3958_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___boxed(lean_object* v_00_u03c6_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_){
_start:
{
lean_object* v_res_4012_; 
v_res_4012_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(v_00_u03c6_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_);
lean_dec(v_a_4010_);
lean_dec_ref(v_a_4009_);
lean_dec(v_a_4008_);
lean_dec_ref(v_a_4007_);
return v_res_4012_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__1(void){
_start:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4014_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__0));
v___x_4015_ = l_Lean_stringToMessageData(v___x_4014_);
return v___x_4015_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4017_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__0));
v___x_4018_ = l_Lean_stringToMessageData(v___x_4017_);
return v___x_4018_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4023_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__3));
v___x_4024_ = l_Lean_stringToMessageData(v___x_4023_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0(lean_object* v_tail_4025_, lean_object* v_locals_4026_, lean_object* v_00_u03c6_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; uint8_t v___x_4042_; 
v___x_4042_ = l_List_isEmpty___redArg(v_tail_4025_);
if (v___x_4042_ == 0)
{
if (lean_obj_tag(v_locals_4026_) == 1)
{
lean_object* v_head_4043_; lean_object* v_tail_4044_; lean_object* v___x_4045_; 
v_head_4043_ = lean_ctor_get(v_locals_4026_, 0);
lean_inc(v_head_4043_);
v_tail_4044_ = lean_ctor_get(v_locals_4026_, 1);
lean_inc(v_tail_4044_);
lean_dec_ref_known(v_locals_4026_, 2);
v___x_4045_ = l_Lean_LocalDecl_value_x3f(v_head_4043_, v___x_4042_);
if (lean_obj_tag(v___x_4045_) == 0)
{
lean_object* v_w_4046_; lean_object* v___x_4047_; 
v_w_4046_ = l_Lean_LocalDecl_toExpr(v_head_4043_);
lean_inc_ref(v_00_u03c6_4027_);
v___x_4047_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_00_u03c6_4027_, v___y_4029_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_a_4048_; lean_object* v___x_4049_; uint8_t v___x_4050_; 
v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
lean_inc(v_a_4048_);
lean_dec_ref_known(v___x_4047_, 1);
v___x_4049_ = l_Lean_Expr_cleanupAnnotations(v_a_4048_);
lean_dec(v_a_4048_);
v___x_4050_ = l_Lean_Expr_isApp(v___x_4049_);
if (v___x_4050_ == 0)
{
lean_dec_ref(v___x_4049_);
lean_dec_ref(v_w_4046_);
lean_dec(v_tail_4044_);
lean_dec(v_tail_4025_);
v___y_4034_ = v___y_4028_;
v___y_4035_ = v___y_4029_;
v___y_4036_ = v___y_4030_;
v___y_4037_ = v___y_4031_;
goto v___jp_4033_;
}
else
{
lean_object* v___x_4051_; uint8_t v___x_4052_; 
v___x_4051_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4049_);
v___x_4052_ = l_Lean_Expr_isApp(v___x_4051_);
if (v___x_4052_ == 0)
{
lean_dec_ref(v___x_4051_);
lean_dec_ref(v___x_4049_);
lean_dec_ref(v_w_4046_);
lean_dec(v_tail_4044_);
lean_dec(v_tail_4025_);
v___y_4034_ = v___y_4028_;
v___y_4035_ = v___y_4029_;
v___y_4036_ = v___y_4030_;
v___y_4037_ = v___y_4031_;
goto v___jp_4033_;
}
else
{
lean_object* v_arg_4053_; lean_object* v_arg_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; uint8_t v___x_4057_; 
v_arg_4053_ = lean_ctor_get(v___x_4049_, 1);
lean_inc_ref(v_arg_4053_);
lean_dec_ref(v___x_4049_);
v_arg_4054_ = lean_ctor_get(v___x_4051_, 1);
lean_inc_ref(v_arg_4054_);
v___x_4055_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4051_);
lean_dec_ref(v___x_4051_);
v___x_4056_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__5));
v___x_4057_ = l_Lean_Expr_isConstOf(v___x_4055_, v___x_4056_);
if (v___x_4057_ == 0)
{
lean_object* v___x_4058_; uint8_t v___x_4059_; 
v___x_4058_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_bindLocal___redArg___closed__1));
v___x_4059_ = l_Lean_Expr_isConstOf(v___x_4055_, v___x_4058_);
lean_dec_ref(v___x_4055_);
if (v___x_4059_ == 0)
{
lean_dec_ref(v_arg_4054_);
lean_dec_ref(v_arg_4053_);
lean_dec_ref(v_w_4046_);
lean_dec(v_tail_4044_);
lean_dec(v_tail_4025_);
v___y_4034_ = v___y_4028_;
v___y_4035_ = v___y_4029_;
v___y_4036_ = v___y_4030_;
v___y_4037_ = v___y_4031_;
goto v___jp_4033_;
}
else
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4060_ = lean_unsigned_to_nat(1u);
v___x_4061_ = lean_mk_empty_array_with_capacity(v___x_4060_);
lean_inc_ref(v_w_4046_);
v___x_4062_ = lean_array_push(v___x_4061_, v_w_4046_);
lean_inc_ref(v_arg_4053_);
v___x_4063_ = l_Lean_Expr_beta(v_arg_4053_, v___x_4062_);
v___x_4064_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v___x_4063_, v_tail_4025_, v_tail_4044_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
if (lean_obj_tag(v___x_4064_) == 0)
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4077_; 
v_a_4065_ = lean_ctor_get(v___x_4064_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4064_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4067_ = v___x_4064_;
v_isShared_4068_ = v_isSharedCheck_4077_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4064_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4077_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4075_; 
v___x_4069_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__2));
v___x_4070_ = l_Lean_Expr_getAppFn(v_00_u03c6_4027_);
lean_dec_ref(v_00_u03c6_4027_);
v___x_4071_ = l_Lean_Expr_constLevels_x21(v___x_4070_);
lean_dec_ref(v___x_4070_);
v___x_4072_ = l_Lean_mkConst(v___x_4069_, v___x_4071_);
v___x_4073_ = l_Lean_mkApp4(v___x_4072_, v_arg_4054_, v_arg_4053_, v_w_4046_, v_a_4065_);
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 0, v___x_4073_);
v___x_4075_ = v___x_4067_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4073_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
else
{
lean_dec_ref(v_arg_4054_);
lean_dec_ref(v_arg_4053_);
lean_dec_ref(v_w_4046_);
lean_dec_ref(v_00_u03c6_4027_);
return v___x_4064_;
}
}
}
else
{
lean_object* v___x_4078_; 
lean_dec_ref(v___x_4055_);
lean_dec_ref(v_00_u03c6_4027_);
lean_inc_ref(v_arg_4053_);
v___x_4078_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v_arg_4053_, v_tail_4025_, v_tail_4044_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4088_; 
v_a_4079_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4081_ = v___x_4078_;
v_isShared_4082_ = v_isSharedCheck_4088_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_4078_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4088_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4086_; 
v___x_4083_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof___closed__10);
v___x_4084_ = l_Lean_mkApp4(v___x_4083_, v_arg_4054_, v_arg_4053_, v_w_4046_, v_a_4079_);
if (v_isShared_4082_ == 0)
{
lean_ctor_set(v___x_4081_, 0, v___x_4084_);
v___x_4086_ = v___x_4081_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v___x_4084_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
else
{
lean_dec_ref(v_arg_4054_);
lean_dec_ref(v_arg_4053_);
lean_dec_ref(v_w_4046_);
return v___x_4078_;
}
}
}
}
}
else
{
lean_dec_ref(v_w_4046_);
lean_dec(v_tail_4044_);
lean_dec_ref(v_00_u03c6_4027_);
lean_dec(v_tail_4025_);
return v___x_4047_;
}
}
else
{
lean_dec_ref_known(v___x_4045_, 1);
lean_dec(v_head_4043_);
if (lean_obj_tag(v_00_u03c6_4027_) == 8)
{
lean_object* v_value_4089_; lean_object* v_body_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
v_value_4089_ = lean_ctor_get(v_00_u03c6_4027_, 2);
lean_inc_ref(v_value_4089_);
v_body_4090_ = lean_ctor_get(v_00_u03c6_4027_, 3);
lean_inc_ref(v_body_4090_);
lean_dec_ref_known(v_00_u03c6_4027_, 4);
v___x_4091_ = lean_expr_instantiate1(v_body_4090_, v_value_4089_);
lean_dec_ref(v_value_4089_);
lean_dec_ref(v_body_4090_);
v___x_4092_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v___x_4091_, v_tail_4025_, v_tail_4044_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
return v___x_4092_;
}
else
{
lean_object* v___x_4093_; 
v___x_4093_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v_00_u03c6_4027_, v_tail_4025_, v_tail_4044_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
return v___x_4093_;
}
}
}
else
{
lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
lean_dec(v_locals_4026_);
lean_dec(v_tail_4025_);
v___x_4094_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__4, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__4_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__4);
v___x_4095_ = l_Lean_indentExpr(v_00_u03c6_4027_);
v___x_4096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4094_);
lean_ctor_set(v___x_4096_, 1, v___x_4095_);
v___x_4097_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v___x_4096_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
return v___x_4097_;
}
}
else
{
lean_object* v___x_4098_; 
lean_dec(v_locals_4026_);
lean_dec(v_tail_4025_);
v___x_4098_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkEqsProof(v_00_u03c6_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
return v___x_4098_;
}
v___jp_4033_:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4038_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__1, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___closed__1);
v___x_4039_ = l_Lean_indentExpr(v_00_u03c6_4027_);
v___x_4040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4038_);
lean_ctor_set(v___x_4040_, 1, v___x_4039_);
v___x_4041_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v___x_4040_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
return v___x_4041_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___boxed(lean_object* v_tail_4099_, lean_object* v_locals_4100_, lean_object* v_00_u03c6_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0(v_tail_4099_, v_locals_4100_, v_00_u03c6_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_);
lean_dec(v___y_4105_);
lean_dec_ref(v___y_4104_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(lean_object* v_00_u03c6_4108_, lean_object* v_path_4109_, lean_object* v_locals_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_){
_start:
{
if (lean_obj_tag(v_path_4109_) == 1)
{
lean_object* v_head_4116_; lean_object* v_tail_4117_; lean_object* v_fst_4118_; lean_object* v_snd_4119_; lean_object* v___f_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v_head_4116_ = lean_ctor_get(v_path_4109_, 0);
lean_inc(v_head_4116_);
v_tail_4117_ = lean_ctor_get(v_path_4109_, 1);
lean_inc(v_tail_4117_);
lean_dec_ref_known(v_path_4109_, 2);
v_fst_4118_ = lean_ctor_get(v_head_4116_, 0);
lean_inc(v_fst_4118_);
v_snd_4119_ = lean_ctor_get(v_head_4116_, 1);
lean_inc(v_snd_4119_);
lean_dec(v_head_4116_);
v___f_4120_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4120_, 0, v_tail_4117_);
lean_closure_set(v___f_4120_, 1, v_locals_4110_);
v___x_4121_ = lean_unsigned_to_nat(0u);
v___x_4122_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro(v_00_u03c6_4108_, v_fst_4118_, v___x_4121_, v_snd_4119_, v___f_4120_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
lean_dec(v_snd_4119_);
lean_dec(v_fst_4118_);
return v___x_4122_;
}
else
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
lean_dec(v_locals_4110_);
lean_dec(v_path_4109_);
v___x_4123_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__1, &l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___closed__1);
v___x_4124_ = l_Lean_indentExpr(v_00_u03c6_4108_);
v___x_4125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4123_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
v___x_4126_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkOrIntro_spec__0___redArg(v___x_4125_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
return v___x_4126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof___boxed(lean_object* v_00_u03c6_4127_, lean_object* v_path_4128_, lean_object* v_locals_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_){
_start:
{
lean_object* v_res_4135_; 
v_res_4135_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v_00_u03c6_4127_, v_path_4128_, v_locals_4129_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_);
lean_dec(v_a_4133_);
lean_dec_ref(v_a_4132_);
lean_dec(v_a_4131_);
lean_dec_ref(v_a_4130_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg(lean_object* v_type_4136_, lean_object* v_k_4137_, uint8_t v_cleanupAnnotations_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
lean_object* v___f_4151_; uint8_t v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
lean_inc(v___y_4145_);
lean_inc_ref(v___y_4144_);
lean_inc(v___y_4143_);
lean_inc_ref(v___y_4142_);
lean_inc(v___y_4141_);
lean_inc(v___y_4140_);
lean_inc_ref(v___y_4139_);
v___f_4151_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__3___redArg___lam__0___boxed), 15, 8);
lean_closure_set(v___f_4151_, 0, v_k_4137_);
lean_closure_set(v___f_4151_, 1, v___y_4139_);
lean_closure_set(v___f_4151_, 2, v___y_4140_);
lean_closure_set(v___f_4151_, 3, v___y_4141_);
lean_closure_set(v___f_4151_, 4, v___y_4142_);
lean_closure_set(v___f_4151_, 5, v___y_4143_);
lean_closure_set(v___f_4151_, 6, v___y_4144_);
lean_closure_set(v___f_4151_, 7, v___y_4145_);
v___x_4152_ = 0;
v___x_4153_ = lean_box(0);
v___x_4154_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_4152_, v___x_4153_, v_type_4136_, v___f_4151_, v_cleanupAnnotations_4138_, v___x_4152_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
if (lean_obj_tag(v___x_4154_) == 0)
{
return v___x_4154_;
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4157_ = v___x_4154_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4154_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg___boxed(lean_object* v_type_4163_, lean_object* v_k_4164_, lean_object* v_cleanupAnnotations_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4178_; lean_object* v_res_4179_; 
v_cleanupAnnotations_boxed_4178_ = lean_unbox(v_cleanupAnnotations_4165_);
v_res_4179_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg(v_type_4163_, v_k_4164_, v_cleanupAnnotations_boxed_4178_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec(v___y_4167_);
lean_dec_ref(v___y_4166_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1(lean_object* v_00_u03b1_4180_, lean_object* v_type_4181_, lean_object* v_k_4182_, uint8_t v_cleanupAnnotations_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v___x_4196_; 
v___x_4196_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg(v_type_4181_, v_k_4182_, v_cleanupAnnotations_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___boxed(lean_object* v_00_u03b1_4197_, lean_object* v_type_4198_, lean_object* v_k_4199_, lean_object* v_cleanupAnnotations_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4213_; lean_object* v_res_4214_; 
v_cleanupAnnotations_boxed_4213_ = lean_unbox(v_cleanupAnnotations_4200_);
v_res_4214_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1(v_00_u03b1_4197_, v_type_4198_, v_k_4199_, v_cleanupAnnotations_boxed_4213_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec(v___y_4202_);
lean_dec_ref(v___y_4201_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___redArg(lean_object* v_e_4215_, lean_object* v___y_4216_){
_start:
{
uint8_t v___x_4218_; 
v___x_4218_ = l_Lean_Expr_hasMVar(v_e_4215_);
if (v___x_4218_ == 0)
{
lean_object* v___x_4219_; 
v___x_4219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4219_, 0, v_e_4215_);
return v___x_4219_;
}
else
{
lean_object* v___x_4220_; lean_object* v_mctx_4221_; lean_object* v___x_4222_; lean_object* v_fst_4223_; lean_object* v_snd_4224_; lean_object* v___x_4225_; lean_object* v_cache_4226_; lean_object* v_zetaDeltaFVarIds_4227_; lean_object* v_postponed_4228_; lean_object* v_diag_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4238_; 
v___x_4220_ = lean_st_ref_get(v___y_4216_);
v_mctx_4221_ = lean_ctor_get(v___x_4220_, 0);
lean_inc_ref(v_mctx_4221_);
lean_dec(v___x_4220_);
v___x_4222_ = l_Lean_instantiateMVarsCore(v_mctx_4221_, v_e_4215_);
v_fst_4223_ = lean_ctor_get(v___x_4222_, 0);
lean_inc(v_fst_4223_);
v_snd_4224_ = lean_ctor_get(v___x_4222_, 1);
lean_inc(v_snd_4224_);
lean_dec_ref(v___x_4222_);
v___x_4225_ = lean_st_ref_take(v___y_4216_);
v_cache_4226_ = lean_ctor_get(v___x_4225_, 1);
v_zetaDeltaFVarIds_4227_ = lean_ctor_get(v___x_4225_, 2);
v_postponed_4228_ = lean_ctor_get(v___x_4225_, 3);
v_diag_4229_ = lean_ctor_get(v___x_4225_, 4);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4238_ == 0)
{
lean_object* v_unused_4239_; 
v_unused_4239_ = lean_ctor_get(v___x_4225_, 0);
lean_dec(v_unused_4239_);
v___x_4231_ = v___x_4225_;
v_isShared_4232_ = v_isSharedCheck_4238_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_diag_4229_);
lean_inc(v_postponed_4228_);
lean_inc(v_zetaDeltaFVarIds_4227_);
lean_inc(v_cache_4226_);
lean_dec(v___x_4225_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4238_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
lean_ctor_set(v___x_4231_, 0, v_snd_4224_);
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_snd_4224_);
lean_ctor_set(v_reuseFailAlloc_4237_, 1, v_cache_4226_);
lean_ctor_set(v_reuseFailAlloc_4237_, 2, v_zetaDeltaFVarIds_4227_);
lean_ctor_set(v_reuseFailAlloc_4237_, 3, v_postponed_4228_);
lean_ctor_set(v_reuseFailAlloc_4237_, 4, v_diag_4229_);
v___x_4234_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; 
v___x_4235_ = lean_st_ref_put(v___y_4216_, v___x_4234_);
v___x_4236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4236_, 0, v_fst_4223_);
return v___x_4236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___redArg___boxed(lean_object* v_e_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
lean_object* v_res_4243_; 
v_res_4243_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___redArg(v_e_4240_, v___y_4241_);
lean_dec(v___y_4241_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2(lean_object* v_e_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_){
_start:
{
lean_object* v___x_4257_; 
v___x_4257_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___redArg(v_e_4244_, v___y_4253_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___boxed(lean_object* v_e_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
lean_object* v_res_4271_; 
v_res_4271_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2(v_e_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec(v___y_4263_);
lean_dec_ref(v___y_4262_);
lean_dec(v___y_4261_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
return v_res_4271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___lam__0(lean_object* v_a_4272_, lean_object* v_hyp_4273_, lean_object* v_xs_4274_, lean_object* v_x_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_){
_start:
{
lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___x_4288_ = lean_unsigned_to_nat(0u);
v___x_4289_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrie(v_xs_4274_, v_a_4272_, v___x_4288_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4289_) == 0)
{
lean_object* v_a_4290_; lean_object* v_fst_4291_; lean_object* v_snd_4292_; uint8_t v___x_4293_; uint8_t v___x_4294_; uint8_t v___x_4295_; lean_object* v___x_4296_; 
v_a_4290_ = lean_ctor_get(v___x_4289_, 0);
lean_inc(v_a_4290_);
lean_dec_ref_known(v___x_4289_, 1);
v_fst_4291_ = lean_ctor_get(v_a_4290_, 0);
lean_inc(v_fst_4291_);
v_snd_4292_ = lean_ctor_get(v_a_4290_, 1);
lean_inc(v_snd_4292_);
lean_dec(v_a_4290_);
v___x_4293_ = 0;
v___x_4294_ = 1;
v___x_4295_ = 1;
v___x_4296_ = l_Lean_Meta_mkLambdaFVars(v_xs_4274_, v_fst_4291_, v___x_4293_, v___x_4294_, v___x_4293_, v___x_4294_, v___x_4295_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_object* v_a_4297_; lean_object* v___x_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4305_; 
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
lean_inc(v_a_4297_);
lean_dec_ref_known(v___x_4296_, 1);
v___x_4298_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg(v_hyp_4273_, v_a_4297_, v___y_4284_);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4305_ == 0)
{
lean_object* v_unused_4306_; 
v_unused_4306_ = lean_ctor_get(v___x_4298_, 0);
lean_dec(v_unused_4306_);
v___x_4300_ = v___x_4298_;
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
else
{
lean_dec(v___x_4298_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4303_; 
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 0, v_snd_4292_);
v___x_4303_ = v___x_4300_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_snd_4292_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
return v___x_4303_;
}
}
}
else
{
lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4314_; 
lean_dec(v_snd_4292_);
lean_dec(v_hyp_4273_);
v_a_4307_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4309_ = v___x_4296_;
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v___x_4296_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4312_; 
if (v_isShared_4310_ == 0)
{
v___x_4312_ = v___x_4309_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_a_4307_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
return v___x_4312_;
}
}
}
}
else
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4322_; 
lean_dec(v_hyp_4273_);
v_a_4315_ = lean_ctor_get(v___x_4289_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4317_ = v___x_4289_;
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___x_4289_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4320_; 
if (v_isShared_4318_ == 0)
{
v___x_4320_ = v___x_4317_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_a_4315_);
v___x_4320_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
return v___x_4320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___lam__0___boxed(lean_object* v_a_4323_, lean_object* v_hyp_4324_, lean_object* v_xs_4325_, lean_object* v_x_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_){
_start:
{
lean_object* v_res_4339_; 
v_res_4339_ = l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___lam__0(v_a_4323_, v_hyp_4324_, v_xs_4325_, v_x_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
lean_dec(v___y_4335_);
lean_dec_ref(v___y_4334_);
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
lean_dec(v___y_4331_);
lean_dec_ref(v___y_4330_);
lean_dec(v___y_4329_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
lean_dec_ref(v_x_4326_);
lean_dec_ref(v_xs_4325_);
lean_dec_ref(v_a_4323_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg(lean_object* v_jp_4340_, size_t v_sz_4341_, size_t v_i_4342_, lean_object* v_bs_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_){
_start:
{
uint8_t v___x_4349_; 
v___x_4349_ = lean_usize_dec_lt(v_i_4342_, v_sz_4341_);
if (v___x_4349_ == 0)
{
lean_object* v___x_4350_; 
v___x_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4350_, 0, v_bs_4343_);
return v___x_4350_;
}
else
{
lean_object* v_v_4351_; lean_object* v___x_4352_; lean_object* v_bs_x27_4353_; lean_object* v___x_4354_; 
v_v_4351_ = lean_array_uget(v_bs_4343_, v_i_4342_);
v___x_4352_ = lean_unsigned_to_nat(0u);
v_bs_x27_4353_ = lean_array_uset(v_bs_4343_, v_i_4342_, v___x_4352_);
lean_inc(v_v_4351_);
v___x_4354_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_jumpLocals(v_jp_4340_, v_v_4351_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v_a_4355_; lean_object* v___x_4356_; size_t v___x_4357_; size_t v___x_4358_; lean_object* v___x_4359_; 
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
lean_inc(v_a_4355_);
lean_dec_ref_known(v___x_4354_, 1);
v___x_4356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4356_, 0, v_v_4351_);
lean_ctor_set(v___x_4356_, 1, v_a_4355_);
v___x_4357_ = ((size_t)1ULL);
v___x_4358_ = lean_usize_add(v_i_4342_, v___x_4357_);
v___x_4359_ = lean_array_uset(v_bs_x27_4353_, v_i_4342_, v___x_4356_);
v_i_4342_ = v___x_4358_;
v_bs_4343_ = v___x_4359_;
goto _start;
}
else
{
lean_object* v_a_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4368_; 
lean_dec_ref(v_bs_x27_4353_);
lean_dec(v_v_4351_);
v_a_4361_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4368_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4368_ == 0)
{
v___x_4363_ = v___x_4354_;
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_a_4361_);
lean_dec(v___x_4354_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v___x_4366_; 
if (v_isShared_4364_ == 0)
{
v___x_4366_ = v___x_4363_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4367_; 
v_reuseFailAlloc_4367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4367_, 0, v_a_4361_);
v___x_4366_ = v_reuseFailAlloc_4367_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
return v___x_4366_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg___boxed(lean_object* v_jp_4369_, lean_object* v_sz_4370_, lean_object* v_i_4371_, lean_object* v_bs_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
size_t v_sz_boxed_4378_; size_t v_i_boxed_4379_; lean_object* v_res_4380_; 
v_sz_boxed_4378_ = lean_unbox_usize(v_sz_4370_);
lean_dec(v_sz_4370_);
v_i_boxed_4379_ = lean_unbox_usize(v_i_4371_);
lean_dec(v_i_4371_);
v_res_4380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg(v_jp_4369_, v_sz_boxed_4378_, v_i_boxed_4379_, v_bs_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
lean_dec(v___y_4376_);
lean_dec_ref(v___y_4375_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec_ref(v_jp_4369_);
return v_res_4380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___lam__0(lean_object* v_proof_4381_, lean_object* v_snd_4382_, lean_object* v_snd_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_){
_start:
{
lean_object* v___x_4396_; 
lean_inc(v_proof_4381_);
v___x_4396_ = l_Lean_MVarId_getType(v_proof_4381_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
if (lean_obj_tag(v___x_4396_) == 0)
{
lean_object* v_a_4397_; lean_object* v___x_4398_; 
v_a_4397_ = lean_ctor_get(v___x_4396_, 0);
lean_inc(v_a_4397_);
lean_dec_ref_known(v___x_4396_, 1);
v___x_4398_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__2___redArg(v_a_4397_, v___y_4392_);
if (lean_obj_tag(v___x_4398_) == 0)
{
lean_object* v_a_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
v_a_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc(v_a_4399_);
lean_dec_ref_known(v___x_4398_, 1);
v___x_4400_ = lean_array_to_list(v_snd_4382_);
v___x_4401_ = l___private_Lean_Elab_Tactic_VCGen_JoinPoint_0__Lean_Elab_Tactic_VCGen_mkTrieProof(v_a_4399_, v_snd_4383_, v___x_4400_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; lean_object* v___x_4403_; 
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc(v_a_4402_);
lean_dec_ref_known(v___x_4401_, 1);
v___x_4403_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_wpJump_x3f_spec__2___redArg(v_proof_4381_, v_a_4402_, v___y_4392_);
return v___x_4403_;
}
else
{
lean_object* v_a_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4411_; 
lean_dec(v_proof_4381_);
v_a_4404_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4411_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4406_ = v___x_4401_;
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_a_4404_);
lean_dec(v___x_4401_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___x_4409_; 
if (v_isShared_4407_ == 0)
{
v___x_4409_ = v___x_4406_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v_a_4404_);
v___x_4409_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
return v___x_4409_;
}
}
}
}
else
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4419_; 
lean_dec(v_snd_4383_);
lean_dec_ref(v_snd_4382_);
lean_dec(v_proof_4381_);
v_a_4412_ = lean_ctor_get(v___x_4398_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4398_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4414_ = v___x_4398_;
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4398_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4417_; 
if (v_isShared_4415_ == 0)
{
v___x_4417_ = v___x_4414_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4412_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
return v___x_4417_;
}
}
}
}
else
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4427_; 
lean_dec(v_snd_4383_);
lean_dec_ref(v_snd_4382_);
lean_dec(v_proof_4381_);
v_a_4420_ = lean_ctor_get(v___x_4396_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4422_ = v___x_4396_;
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4396_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4425_; 
if (v_isShared_4423_ == 0)
{
v___x_4425_ = v___x_4422_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_a_4420_);
v___x_4425_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
return v___x_4425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___lam__0___boxed(lean_object* v_proof_4428_, lean_object* v_snd_4429_, lean_object* v_snd_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v_res_4443_; 
v_res_4443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___lam__0(v_proof_4428_, v_snd_4429_, v_snd_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
lean_dec(v___y_4441_);
lean_dec_ref(v___y_4440_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3(lean_object* v_as_4444_, size_t v_sz_4445_, size_t v_i_4446_, lean_object* v_b_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
uint8_t v___x_4460_; 
v___x_4460_ = lean_usize_dec_lt(v_i_4446_, v_sz_4445_);
if (v___x_4460_ == 0)
{
lean_object* v___x_4461_; 
v___x_4461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4461_, 0, v_b_4447_);
return v___x_4461_;
}
else
{
lean_object* v_a_4462_; lean_object* v_fst_4463_; lean_object* v_fst_4464_; lean_object* v_snd_4465_; lean_object* v_snd_4466_; lean_object* v_proof_4467_; lean_object* v___x_4468_; lean_object* v___f_4469_; lean_object* v___x_4470_; 
v_a_4462_ = lean_array_uget_borrowed(v_as_4444_, v_i_4446_);
v_fst_4463_ = lean_ctor_get(v_a_4462_, 0);
v_fst_4464_ = lean_ctor_get(v_fst_4463_, 0);
v_snd_4465_ = lean_ctor_get(v_a_4462_, 1);
v_snd_4466_ = lean_ctor_get(v_fst_4463_, 1);
v_proof_4467_ = lean_ctor_get(v_fst_4464_, 0);
v___x_4468_ = lean_box(0);
lean_inc(v_snd_4465_);
lean_inc(v_snd_4466_);
lean_inc_n(v_proof_4467_, 2);
v___f_4469_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___lam__0___boxed), 15, 3);
lean_closure_set(v___f_4469_, 0, v_proof_4467_);
lean_closure_set(v___f_4469_, 1, v_snd_4466_);
lean_closure_set(v___f_4469_, 2, v_snd_4465_);
v___x_4470_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_registerJoinPoint_spec__6___redArg(v_proof_4467_, v___f_4469_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
if (lean_obj_tag(v___x_4470_) == 0)
{
size_t v___x_4471_; size_t v___x_4472_; 
lean_dec_ref_known(v___x_4470_, 1);
v___x_4471_ = ((size_t)1ULL);
v___x_4472_ = lean_usize_add(v_i_4446_, v___x_4471_);
v_i_4446_ = v___x_4472_;
v_b_4447_ = v___x_4468_;
goto _start;
}
else
{
return v___x_4470_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3___boxed(lean_object* v_as_4474_, lean_object* v_sz_4475_, lean_object* v_i_4476_, lean_object* v_b_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_){
_start:
{
size_t v_sz_boxed_4490_; size_t v_i_boxed_4491_; lean_object* v_res_4492_; 
v_sz_boxed_4490_ = lean_unbox_usize(v_sz_4475_);
lean_dec(v_sz_4475_);
v_i_boxed_4491_ = lean_unbox_usize(v_i_4476_);
lean_dec(v_i_4476_);
v_res_4492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3(v_as_4474_, v_sz_boxed_4490_, v_i_boxed_4491_, v_b_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec(v___y_4479_);
lean_dec_ref(v___y_4478_);
lean_dec_ref(v_as_4474_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint(lean_object* v_jp_4493_, lean_object* v_jumps_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_){
_start:
{
size_t v_sz_4507_; size_t v___x_4508_; lean_object* v___x_4509_; 
v_sz_4507_ = lean_array_size(v_jumps_4494_);
v___x_4508_ = ((size_t)0ULL);
v___x_4509_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg(v_jp_4493_, v_sz_4507_, v___x_4508_, v_jumps_4494_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_);
if (lean_obj_tag(v___x_4509_) == 0)
{
lean_object* v_a_4510_; lean_object* v_hyp_4511_; lean_object* v___f_4512_; lean_object* v___x_4513_; 
v_a_4510_ = lean_ctor_get(v___x_4509_, 0);
lean_inc_n(v_a_4510_, 2);
lean_dec_ref_known(v___x_4509_, 1);
v_hyp_4511_ = lean_ctor_get(v_jp_4493_, 2);
lean_inc_n(v_hyp_4511_, 2);
lean_dec_ref(v_jp_4493_);
v___f_4512_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___lam__0___boxed), 16, 2);
lean_closure_set(v___f_4512_, 0, v_a_4510_);
lean_closure_set(v___f_4512_, 1, v_hyp_4511_);
v___x_4513_ = l_Lean_MVarId_getType(v_hyp_4511_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_);
if (lean_obj_tag(v___x_4513_) == 0)
{
lean_object* v_a_4514_; uint8_t v___x_4515_; lean_object* v___x_4516_; 
v_a_4514_ = lean_ctor_get(v___x_4513_, 0);
lean_inc(v_a_4514_);
lean_dec_ref_known(v___x_4513_, 1);
v___x_4515_ = 0;
v___x_4516_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__1___redArg(v_a_4514_, v___f_4512_, v___x_4515_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_);
if (lean_obj_tag(v___x_4516_) == 0)
{
lean_object* v_a_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; size_t v_sz_4520_; lean_object* v___x_4521_; 
v_a_4517_ = lean_ctor_get(v___x_4516_, 0);
lean_inc(v_a_4517_);
lean_dec_ref_known(v___x_4516_, 1);
v___x_4518_ = l_Array_zip___redArg(v_a_4510_, v_a_4517_);
lean_dec(v_a_4517_);
lean_dec(v_a_4510_);
v___x_4519_ = lean_box(0);
v_sz_4520_ = lean_array_size(v___x_4518_);
v___x_4521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__3(v___x_4518_, v_sz_4520_, v___x_4508_, v___x_4519_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_);
lean_dec_ref(v___x_4518_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4528_; 
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4528_ == 0)
{
lean_object* v_unused_4529_; 
v_unused_4529_ = lean_ctor_get(v___x_4521_, 0);
lean_dec(v_unused_4529_);
v___x_4523_ = v___x_4521_;
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
else
{
lean_dec(v___x_4521_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4526_; 
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 0, v___x_4519_);
v___x_4526_ = v___x_4523_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v___x_4519_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
}
else
{
return v___x_4521_;
}
}
else
{
lean_object* v_a_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4537_; 
lean_dec(v_a_4510_);
v_a_4530_ = lean_ctor_get(v___x_4516_, 0);
v_isSharedCheck_4537_ = !lean_is_exclusive(v___x_4516_);
if (v_isSharedCheck_4537_ == 0)
{
v___x_4532_ = v___x_4516_;
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_a_4530_);
lean_dec(v___x_4516_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4535_; 
if (v_isShared_4533_ == 0)
{
v___x_4535_ = v___x_4532_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_a_4530_);
v___x_4535_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
return v___x_4535_;
}
}
}
}
else
{
lean_object* v_a_4538_; lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4545_; 
lean_dec_ref(v___f_4512_);
lean_dec(v_a_4510_);
v_a_4538_ = lean_ctor_get(v___x_4513_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v___x_4513_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4540_ = v___x_4513_;
v_isShared_4541_ = v_isSharedCheck_4545_;
goto v_resetjp_4539_;
}
else
{
lean_inc(v_a_4538_);
lean_dec(v___x_4513_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4545_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
lean_object* v___x_4543_; 
if (v_isShared_4541_ == 0)
{
v___x_4543_ = v___x_4540_;
goto v_reusejp_4542_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4538_);
v___x_4543_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4542_;
}
v_reusejp_4542_:
{
return v___x_4543_;
}
}
}
}
else
{
lean_object* v_a_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4553_; 
lean_dec_ref(v_jp_4493_);
v_a_4546_ = lean_ctor_get(v___x_4509_, 0);
v_isSharedCheck_4553_ = !lean_is_exclusive(v___x_4509_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4548_ = v___x_4509_;
v_isShared_4549_ = v_isSharedCheck_4553_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_a_4546_);
lean_dec(v___x_4509_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4553_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
lean_object* v___x_4551_; 
if (v_isShared_4549_ == 0)
{
v___x_4551_ = v___x_4548_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v_a_4546_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint___boxed(lean_object* v_jp_4554_, lean_object* v_jumps_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_){
_start:
{
lean_object* v_res_4568_; 
v_res_4568_ = l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint(v_jp_4554_, v_jumps_4555_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_);
lean_dec(v_a_4566_);
lean_dec_ref(v_a_4565_);
lean_dec(v_a_4564_);
lean_dec_ref(v_a_4563_);
lean_dec(v_a_4562_);
lean_dec_ref(v_a_4561_);
lean_dec(v_a_4560_);
lean_dec_ref(v_a_4559_);
lean_dec(v_a_4558_);
lean_dec(v_a_4557_);
lean_dec_ref(v_a_4556_);
return v_res_4568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0(lean_object* v_jp_4569_, size_t v_sz_4570_, size_t v_i_4571_, lean_object* v_bs_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_){
_start:
{
lean_object* v___x_4585_; 
v___x_4585_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___redArg(v_jp_4569_, v_sz_4570_, v_i_4571_, v_bs_4572_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
return v___x_4585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0___boxed(lean_object* v_jp_4586_, lean_object* v_sz_4587_, lean_object* v_i_4588_, lean_object* v_bs_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_){
_start:
{
size_t v_sz_boxed_4602_; size_t v_i_boxed_4603_; lean_object* v_res_4604_; 
v_sz_boxed_4602_ = lean_unbox_usize(v_sz_4587_);
lean_dec(v_sz_4587_);
v_i_boxed_4603_ = lean_unbox_usize(v_i_4588_);
lean_dec(v_i_4588_);
v_res_4604_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_finalizeJoinPoint_spec__0(v_jp_4586_, v_sz_boxed_4602_, v_i_boxed_4603_, v_bs_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
lean_dec(v___y_4598_);
lean_dec_ref(v___y_4597_);
lean_dec(v___y_4596_);
lean_dec_ref(v___y_4595_);
lean_dec(v___y_4594_);
lean_dec_ref(v___y_4593_);
lean_dec(v___y_4592_);
lean_dec(v___y_4591_);
lean_dec_ref(v___y_4590_);
lean_dec_ref(v_jp_4586_);
return v_res_4604_;
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
