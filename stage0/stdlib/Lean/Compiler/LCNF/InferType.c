// Lean compiler output
// Module: Lean.Compiler.LCNF.InferType
// Imports: public import Lean.Compiler.LCNF.PhaseExt public import Lean.Compiler.LCNF.OtherDecl import Init.Omega
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
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getOtherDeclType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_erasedExpr;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_anyExpr;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Level_normalize(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
uint8_t l_Lean_Expr_isErased(lean_object*);
uint8_t l_Lean_Expr_isAny(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
extern lean_object* l_Lean_Core_instMonadNameGeneratorCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshFVarId___redArg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(uint8_t);
lean_object* l_Lean_Compiler_LCNF_joinTypes(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isPredicateType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1;
static const lean_closure_object l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3_value;
static const lean_closure_object l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__4_value;
static const lean_closure_object l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__5_value;
static const lean_closure_object l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__6_value;
static const lean_closure_object l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lcErased"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 218, 234, 194, 194, 57, 75, 5)}};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2;
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5;
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__6_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__7_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8;
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__9_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__9_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__10_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11;
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__12_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__12_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__13_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14;
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__15_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__15_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__16_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17;
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__18 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__18_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__18_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__19 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__19_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Compiler.LCNF.InferType.Pure.inferType"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Compiler.LCNF.InferType"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferArgType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "invalid projection"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__1_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__3 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__3_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferProjType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_inferAppType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Compiler.LCNF.inferAppType"};
static const lean_object* l_Lean_Compiler_LCNF_inferAppType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_inferAppType___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_inferAppType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Infer type for impure unimplemented"};
static const lean_object* l_Lean_Compiler_LCNF_inferAppType___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_inferAppType___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_inferAppType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_inferAppType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Arg_inferType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Compiler.LCNF.Arg.inferType"};
static const lean_object* l_Lean_Compiler_LCNF_Arg_inferType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Arg_inferType___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Arg_inferType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Arg_inferType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_inferType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Compiler.LCNF.LetValue.inferType"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_inferType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_inferType___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_LetValue_inferType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_LetValue_inferType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Code_inferType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Compiler.LCNF.Code.inferType"};
static const lean_object* l_Lean_Compiler_LCNF_Code_inferType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_inferType___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_inferType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_inferType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_mkForallParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Compiler.LCNF.mkForallParams"};
static const lean_object* l_Lean_Compiler_LCNF_mkForallParams___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkForallParams___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkForallParams___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkForallParams___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_mkCasesResultType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`Code.bind` failed, empty `cases` found"};
static const lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkCasesResultType___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkCasesResultType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 81, .m_capacity = 81, .m_length = 80, .m_data = "_private.Lean.Compiler.LCNF.InferType.0.Lean.Compiler.LCNF.isErasedCompatible.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_eqvTypes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eqvTypes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getBinderName(lean_object* v_fvarId_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
lean_object* v___x_8_; 
lean_inc(v_fvarId_1_);
lean_inc_ref(v_a_2_);
v___x_8_ = lean_local_ctx_find(v_a_2_, v_fvarId_1_);
if (lean_obj_tag(v___x_8_) == 0)
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_1_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
return v___x_9_;
}
else
{
lean_object* v_val_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_18_; 
lean_dec(v_fvarId_1_);
v_val_10_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_18_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_18_ == 0)
{
v___x_12_ = v___x_8_;
v_isShared_13_ = v_isSharedCheck_18_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_val_10_);
lean_dec(v___x_8_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_18_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_14_; lean_object* v___x_16_; 
v___x_14_ = l_Lean_LocalDecl_userName(v_val_10_);
lean_dec(v_val_10_);
if (v_isShared_13_ == 0)
{
lean_ctor_set_tag(v___x_12_, 0);
lean_ctor_set(v___x_12_, 0, v___x_14_);
v___x_16_ = v___x_12_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v___x_14_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getBinderName___boxed(lean_object* v_fvarId_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Compiler_LCNF_InferType_Pure_getBinderName(v_fvarId_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
lean_dec(v_a_24_);
lean_dec_ref(v_a_23_);
lean_dec(v_a_22_);
lean_dec_ref(v_a_21_);
lean_dec_ref(v_a_20_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getType(lean_object* v_fvarId_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_){
_start:
{
lean_object* v___x_34_; 
lean_inc(v_fvarId_27_);
lean_inc_ref(v_a_28_);
v___x_34_ = lean_local_ctx_find(v_a_28_, v_fvarId_27_);
if (lean_obj_tag(v___x_34_) == 0)
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Compiler_LCNF_getType(v_fvarId_27_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
return v___x_35_;
}
else
{
lean_object* v_val_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_44_; 
lean_dec(v_fvarId_27_);
v_val_36_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_44_ == 0)
{
v___x_38_ = v___x_34_;
v_isShared_39_ = v_isSharedCheck_44_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_val_36_);
lean_dec(v___x_34_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_44_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_40_; lean_object* v___x_42_; 
v___x_40_ = l_Lean_LocalDecl_type(v_val_36_);
lean_dec(v_val_36_);
if (v_isShared_39_ == 0)
{
lean_ctor_set_tag(v___x_38_, 0);
lean_ctor_set(v___x_38_, 0, v___x_40_);
v___x_42_ = v___x_38_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_40_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getType___boxed(lean_object* v_fvarId_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_fvarId_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_a_46_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(lean_object* v_xs_53_, lean_object* v_i_54_, lean_object* v_a_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v_zero_62_; uint8_t v_isZero_63_; 
v_zero_62_ = lean_unsigned_to_nat(0u);
v_isZero_63_ = lean_nat_dec_eq(v_i_54_, v_zero_62_);
if (v_isZero_63_ == 1)
{
lean_object* v___x_64_; 
lean_dec(v_i_54_);
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v_a_55_);
return v___x_64_;
}
else
{
lean_object* v_one_65_; lean_object* v_n_66_; lean_object* v_x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v_one_65_ = lean_unsigned_to_nat(1u);
v_n_66_ = lean_nat_sub(v_i_54_, v_one_65_);
lean_dec(v_i_54_);
v_x_67_ = lean_array_fget_borrowed(v_xs_53_, v_n_66_);
v___x_68_ = l_Lean_Expr_fvarId_x21(v_x_67_);
lean_inc(v___x_68_);
v___x_69_ = l_Lean_Compiler_LCNF_InferType_Pure_getBinderName(v___x_68_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v_a_70_; lean_object* v___x_71_; 
v_a_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc(v_a_70_);
lean_dec_ref_known(v___x_69_, 1);
v___x_71_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v___x_68_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; 
v_a_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_a_72_);
lean_dec_ref_known(v___x_71_, 1);
v___x_73_ = lean_expr_abstract_range(v_a_72_, v_n_66_, v_xs_53_);
lean_dec(v_a_72_);
v___x_74_ = 0;
v___x_75_ = l_Lean_Expr_forallE___override(v_a_70_, v___x_73_, v_a_55_, v___x_74_);
v_i_54_ = v_n_66_;
v_a_55_ = v___x_75_;
goto _start;
}
else
{
lean_dec(v_a_70_);
lean_dec_ref(v_a_55_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_77_; 
v_a_77_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_a_77_);
lean_dec_ref_known(v___x_71_, 1);
v_i_54_ = v_n_66_;
v_a_55_ = v_a_77_;
goto _start;
}
else
{
lean_dec(v_n_66_);
return v___x_71_;
}
}
}
else
{
lean_object* v_a_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_86_; 
lean_dec(v___x_68_);
lean_dec(v_n_66_);
lean_dec_ref(v_a_55_);
v_a_79_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_86_ == 0)
{
v___x_81_ = v___x_69_;
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_a_79_);
lean_dec(v___x_69_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
if (v_isShared_82_ == 0)
{
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_a_79_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg___boxed(lean_object* v_xs_87_, lean_object* v_i_88_, lean_object* v_a_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(v_xs_87_, v_i_88_, v_a_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec_ref(v_xs_87_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(lean_object* v_xs_97_, lean_object* v_type_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v_b_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_b_105_ = lean_expr_abstract(v_type_98_, v_xs_97_);
v___x_106_ = lean_array_get_size(v_xs_97_);
v___x_107_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(v_xs_97_, v___x_106_, v_b_105_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars___boxed(lean_object* v_xs_108_, lean_object* v_type_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v_xs_108_, v_type_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec_ref(v_type_109_);
lean_dec_ref(v_xs_108_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0(lean_object* v_xs_117_, lean_object* v_n_118_, lean_object* v_i_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(v_xs_117_, v_i_119_, v_a_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___boxed(lean_object* v_xs_129_, lean_object* v_n_130_, lean_object* v_i_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0(v_xs_129_, v_n_130_, v_i_131_, v_a_132_, v_a_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v_n_130_);
lean_dec_ref(v_xs_129_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(size_t v_sz_141_, size_t v_i_142_, lean_object* v_bs_143_){
_start:
{
uint8_t v___x_144_; 
v___x_144_ = lean_usize_dec_lt(v_i_142_, v_sz_141_);
if (v___x_144_ == 0)
{
return v_bs_143_;
}
else
{
lean_object* v_v_145_; lean_object* v_fvarId_146_; lean_object* v___x_147_; lean_object* v_bs_x27_148_; lean_object* v___x_149_; size_t v___x_150_; size_t v___x_151_; lean_object* v___x_152_; 
v_v_145_ = lean_array_uget_borrowed(v_bs_143_, v_i_142_);
v_fvarId_146_ = lean_ctor_get(v_v_145_, 0);
lean_inc(v_fvarId_146_);
v___x_147_ = lean_unsigned_to_nat(0u);
v_bs_x27_148_ = lean_array_uset(v_bs_143_, v_i_142_, v___x_147_);
v___x_149_ = l_Lean_Expr_fvar___override(v_fvarId_146_);
v___x_150_ = ((size_t)1ULL);
v___x_151_ = lean_usize_add(v_i_142_, v___x_150_);
v___x_152_ = lean_array_uset(v_bs_x27_148_, v_i_142_, v___x_149_);
v_i_142_ = v___x_151_;
v_bs_143_ = v___x_152_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0___boxed(lean_object* v_sz_154_, lean_object* v_i_155_, lean_object* v_bs_156_){
_start:
{
size_t v_sz_boxed_157_; size_t v_i_boxed_158_; lean_object* v_res_159_; 
v_sz_boxed_157_ = lean_unbox_usize(v_sz_154_);
lean_dec(v_sz_154_);
v_i_boxed_158_ = lean_unbox_usize(v_i_155_);
lean_dec(v_i_155_);
v_res_159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(v_sz_boxed_157_, v_i_boxed_158_, v_bs_156_);
return v_res_159_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0(void){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_160_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = lean_unsigned_to_nat(32u);
v___x_164_ = lean_mk_empty_array_with_capacity(v___x_163_);
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3(void){
_start:
{
size_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_166_ = ((size_t)5ULL);
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = lean_unsigned_to_nat(32u);
v___x_169_ = lean_mk_empty_array_with_capacity(v___x_168_);
v___x_170_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2);
v___x_171_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
lean_ctor_set(v___x_171_, 2, v___x_167_);
lean_ctor_set(v___x_171_, 3, v___x_167_);
lean_ctor_set_usize(v___x_171_, 4, v___x_166_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_172_ = lean_box(1);
v___x_173_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3);
v___x_174_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1);
v___x_175_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_173_);
lean_ctor_set(v___x_175_, 2, v___x_172_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(lean_object* v_params_176_, lean_object* v_type_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
size_t v_sz_183_; size_t v___x_184_; lean_object* v_xs_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v_sz_183_ = lean_array_size(v_params_176_);
v___x_184_ = ((size_t)0ULL);
v_xs_185_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(v_sz_183_, v___x_184_, v_params_176_);
v___x_186_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_187_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v_xs_185_, v_type_177_, v___x_186_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
lean_dec_ref(v_xs_185_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___boxed(lean_object* v_params_188_, lean_object* v_type_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(v_params_188_, v_type_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec_ref(v_type_189_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams(lean_object* v_params_196_, lean_object* v_type_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(v_params_196_, v_type_197_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___boxed(lean_object* v_params_205_, lean_object* v_type_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams(v_params_205_, v_type_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec_ref(v_type_206_);
return v_res_213_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_instMonadEIO(lean_box(0));
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0);
v___x_216_ = l_StateRefT_x27_instMonad___redArg(v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_223_ = l_Lean_Core_instMonadNameGeneratorCoreM;
v___x_224_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__7));
v___x_225_ = l_Lean_monadNameGeneratorLift___redArg(v___x_224_, v___x_223_);
return v___x_225_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9(void){
_start:
{
lean_object* v___x_226_; lean_object* v___f_227_; lean_object* v___x_228_; 
v___x_226_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8);
v___f_227_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__6));
v___x_228_ = l_Lean_monadNameGeneratorLift___redArg(v___f_227_, v___x_226_);
return v___x_228_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10(void){
_start:
{
lean_object* v___x_229_; lean_object* v___f_230_; lean_object* v___x_231_; 
v___x_229_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9);
v___f_230_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__6));
v___x_231_ = l_Lean_monadNameGeneratorLift___redArg(v___f_230_, v___x_229_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg(lean_object* v_binderName_232_, lean_object* v_type_233_, uint8_t v_binderInfo_234_, lean_object* v_k_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v___x_242_; lean_object* v_toApplicative_243_; lean_object* v_toFunctor_244_; lean_object* v_toSeq_245_; lean_object* v_toSeqLeft_246_; lean_object* v_toSeqRight_247_; lean_object* v___f_248_; lean_object* v___f_249_; lean_object* v___f_250_; lean_object* v___f_251_; lean_object* v___x_252_; lean_object* v___f_253_; lean_object* v___f_254_; lean_object* v___f_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v_toApplicative_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_303_; 
v___x_242_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_243_ = lean_ctor_get(v___x_242_, 0);
v_toFunctor_244_ = lean_ctor_get(v_toApplicative_243_, 0);
v_toSeq_245_ = lean_ctor_get(v_toApplicative_243_, 2);
v_toSeqLeft_246_ = lean_ctor_get(v_toApplicative_243_, 3);
v_toSeqRight_247_ = lean_ctor_get(v_toApplicative_243_, 4);
v___f_248_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_249_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_244_, 2);
v___f_250_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_250_, 0, v_toFunctor_244_);
v___f_251_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_251_, 0, v_toFunctor_244_);
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v___f_250_);
lean_ctor_set(v___x_252_, 1, v___f_251_);
lean_inc(v_toSeqRight_247_);
v___f_253_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_253_, 0, v_toSeqRight_247_);
lean_inc(v_toSeqLeft_246_);
v___f_254_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_254_, 0, v_toSeqLeft_246_);
lean_inc(v_toSeq_245_);
v___f_255_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_255_, 0, v_toSeq_245_);
v___x_256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_256_, 0, v___x_252_);
lean_ctor_set(v___x_256_, 1, v___f_248_);
lean_ctor_set(v___x_256_, 2, v___f_255_);
lean_ctor_set(v___x_256_, 3, v___f_254_);
lean_ctor_set(v___x_256_, 4, v___f_253_);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v___f_249_);
v___x_258_ = l_StateRefT_x27_instMonad___redArg(v___x_257_);
v_toApplicative_259_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_303_ == 0)
{
lean_object* v_unused_304_; 
v_unused_304_ = lean_ctor_get(v___x_258_, 1);
lean_dec(v_unused_304_);
v___x_261_ = v___x_258_;
v_isShared_262_ = v_isSharedCheck_303_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_toApplicative_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_303_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v_toFunctor_263_; lean_object* v_toSeq_264_; lean_object* v_toSeqLeft_265_; lean_object* v_toSeqRight_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_301_; 
v_toFunctor_263_ = lean_ctor_get(v_toApplicative_259_, 0);
v_toSeq_264_ = lean_ctor_get(v_toApplicative_259_, 2);
v_toSeqLeft_265_ = lean_ctor_get(v_toApplicative_259_, 3);
v_toSeqRight_266_ = lean_ctor_get(v_toApplicative_259_, 4);
v_isSharedCheck_301_ = !lean_is_exclusive(v_toApplicative_259_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; 
v_unused_302_ = lean_ctor_get(v_toApplicative_259_, 1);
lean_dec(v_unused_302_);
v___x_268_ = v_toApplicative_259_;
v_isShared_269_ = v_isSharedCheck_301_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_toSeqRight_266_);
lean_inc(v_toSeqLeft_265_);
lean_inc(v_toSeq_264_);
lean_inc(v_toFunctor_263_);
lean_dec(v_toApplicative_259_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_301_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___f_270_; lean_object* v___f_271_; lean_object* v___f_272_; lean_object* v___f_273_; lean_object* v___x_274_; lean_object* v___f_275_; lean_object* v___f_276_; lean_object* v___f_277_; lean_object* v___x_279_; 
v___f_270_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__4));
v___f_271_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__5));
lean_inc_ref(v_toFunctor_263_);
v___f_272_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_272_, 0, v_toFunctor_263_);
v___f_273_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_273_, 0, v_toFunctor_263_);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v___f_272_);
lean_ctor_set(v___x_274_, 1, v___f_273_);
v___f_275_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_275_, 0, v_toSeqRight_266_);
v___f_276_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_276_, 0, v_toSeqLeft_265_);
v___f_277_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_277_, 0, v_toSeq_264_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 4, v___f_275_);
lean_ctor_set(v___x_268_, 3, v___f_276_);
lean_ctor_set(v___x_268_, 2, v___f_277_);
lean_ctor_set(v___x_268_, 1, v___f_270_);
lean_ctor_set(v___x_268_, 0, v___x_274_);
v___x_279_ = v___x_268_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v___f_270_);
lean_ctor_set(v_reuseFailAlloc_300_, 2, v___f_277_);
lean_ctor_set(v_reuseFailAlloc_300_, 3, v___f_276_);
lean_ctor_set(v_reuseFailAlloc_300_, 4, v___f_275_);
v___x_279_ = v_reuseFailAlloc_300_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_281_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v___f_271_);
lean_ctor_set(v___x_261_, 0, v___x_279_);
v___x_281_ = v___x_261_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v___f_271_);
v___x_281_ = v_reuseFailAlloc_299_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_157__overap_284_; lean_object* v___x_285_; 
v___x_282_ = l_ReaderT_instMonad___redArg(v___x_281_);
v___x_283_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10);
v___x_157__overap_284_ = l_Lean_mkFreshFVarId___redArg(v___x_282_, v___x_283_);
lean_inc(v_a_240_);
lean_inc_ref(v_a_239_);
lean_inc(v_a_238_);
lean_inc_ref(v_a_237_);
lean_inc_ref(v_a_236_);
v___x_285_ = lean_apply_6(v___x_157__overap_284_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, lean_box(0));
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_287_; uint8_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc_n(v_a_286_, 2);
lean_dec_ref_known(v___x_285_, 1);
v___x_287_ = l_Lean_Expr_fvar___override(v_a_286_);
v___x_288_ = 0;
lean_inc_ref(v_a_236_);
v___x_289_ = l_Lean_LocalContext_mkLocalDecl(v_a_236_, v_a_286_, v_binderName_232_, v_type_233_, v_binderInfo_234_, v___x_288_);
lean_inc(v_a_240_);
lean_inc_ref(v_a_239_);
lean_inc(v_a_238_);
lean_inc_ref(v_a_237_);
v___x_290_ = lean_apply_7(v_k_235_, v___x_287_, v___x_289_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, lean_box(0));
return v___x_290_;
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec_ref(v_k_235_);
lean_dec_ref(v_type_233_);
lean_dec(v_binderName_232_);
v_a_291_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_285_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_285_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___boxed(lean_object* v_binderName_305_, lean_object* v_type_306_, lean_object* v_binderInfo_307_, lean_object* v_k_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
uint8_t v_binderInfo_boxed_315_; lean_object* v_res_316_; 
v_binderInfo_boxed_315_ = lean_unbox(v_binderInfo_307_);
v_res_316_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg(v_binderName_305_, v_type_306_, v_binderInfo_boxed_315_, v_k_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec_ref(v_a_309_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl(lean_object* v_00_u03b1_317_, lean_object* v_binderName_318_, lean_object* v_type_319_, uint8_t v_binderInfo_320_, lean_object* v_k_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_328_; lean_object* v_toApplicative_329_; lean_object* v_toFunctor_330_; lean_object* v_toSeq_331_; lean_object* v_toSeqLeft_332_; lean_object* v_toSeqRight_333_; lean_object* v___f_334_; lean_object* v___f_335_; lean_object* v___f_336_; lean_object* v___f_337_; lean_object* v___x_338_; lean_object* v___f_339_; lean_object* v___f_340_; lean_object* v___f_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v_toApplicative_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_389_; 
v___x_328_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_329_ = lean_ctor_get(v___x_328_, 0);
v_toFunctor_330_ = lean_ctor_get(v_toApplicative_329_, 0);
v_toSeq_331_ = lean_ctor_get(v_toApplicative_329_, 2);
v_toSeqLeft_332_ = lean_ctor_get(v_toApplicative_329_, 3);
v_toSeqRight_333_ = lean_ctor_get(v_toApplicative_329_, 4);
v___f_334_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_335_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_330_, 2);
v___f_336_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_336_, 0, v_toFunctor_330_);
v___f_337_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_337_, 0, v_toFunctor_330_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___f_336_);
lean_ctor_set(v___x_338_, 1, v___f_337_);
lean_inc(v_toSeqRight_333_);
v___f_339_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_339_, 0, v_toSeqRight_333_);
lean_inc(v_toSeqLeft_332_);
v___f_340_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_340_, 0, v_toSeqLeft_332_);
lean_inc(v_toSeq_331_);
v___f_341_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_341_, 0, v_toSeq_331_);
v___x_342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_342_, 0, v___x_338_);
lean_ctor_set(v___x_342_, 1, v___f_334_);
lean_ctor_set(v___x_342_, 2, v___f_341_);
lean_ctor_set(v___x_342_, 3, v___f_340_);
lean_ctor_set(v___x_342_, 4, v___f_339_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___f_335_);
v___x_344_ = l_StateRefT_x27_instMonad___redArg(v___x_343_);
v_toApplicative_345_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_389_ == 0)
{
lean_object* v_unused_390_; 
v_unused_390_ = lean_ctor_get(v___x_344_, 1);
lean_dec(v_unused_390_);
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_389_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_toApplicative_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_389_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v_toFunctor_349_; lean_object* v_toSeq_350_; lean_object* v_toSeqLeft_351_; lean_object* v_toSeqRight_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_387_; 
v_toFunctor_349_ = lean_ctor_get(v_toApplicative_345_, 0);
v_toSeq_350_ = lean_ctor_get(v_toApplicative_345_, 2);
v_toSeqLeft_351_ = lean_ctor_get(v_toApplicative_345_, 3);
v_toSeqRight_352_ = lean_ctor_get(v_toApplicative_345_, 4);
v_isSharedCheck_387_ = !lean_is_exclusive(v_toApplicative_345_);
if (v_isSharedCheck_387_ == 0)
{
lean_object* v_unused_388_; 
v_unused_388_ = lean_ctor_get(v_toApplicative_345_, 1);
lean_dec(v_unused_388_);
v___x_354_ = v_toApplicative_345_;
v_isShared_355_ = v_isSharedCheck_387_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_toSeqRight_352_);
lean_inc(v_toSeqLeft_351_);
lean_inc(v_toSeq_350_);
lean_inc(v_toFunctor_349_);
lean_dec(v_toApplicative_345_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_387_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___f_356_; lean_object* v___f_357_; lean_object* v___f_358_; lean_object* v___f_359_; lean_object* v___x_360_; lean_object* v___f_361_; lean_object* v___f_362_; lean_object* v___f_363_; lean_object* v___x_365_; 
v___f_356_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__4));
v___f_357_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__5));
lean_inc_ref(v_toFunctor_349_);
v___f_358_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_358_, 0, v_toFunctor_349_);
v___f_359_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_359_, 0, v_toFunctor_349_);
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v___f_358_);
lean_ctor_set(v___x_360_, 1, v___f_359_);
v___f_361_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_361_, 0, v_toSeqRight_352_);
v___f_362_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_362_, 0, v_toSeqLeft_351_);
v___f_363_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_363_, 0, v_toSeq_350_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 4, v___f_361_);
lean_ctor_set(v___x_354_, 3, v___f_362_);
lean_ctor_set(v___x_354_, 2, v___f_363_);
lean_ctor_set(v___x_354_, 1, v___f_356_);
lean_ctor_set(v___x_354_, 0, v___x_360_);
v___x_365_ = v___x_354_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v___f_356_);
lean_ctor_set(v_reuseFailAlloc_386_, 2, v___f_363_);
lean_ctor_set(v_reuseFailAlloc_386_, 3, v___f_362_);
lean_ctor_set(v_reuseFailAlloc_386_, 4, v___f_361_);
v___x_365_ = v_reuseFailAlloc_386_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_367_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v___f_357_);
lean_ctor_set(v___x_347_, 0, v___x_365_);
v___x_367_ = v___x_347_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v___f_357_);
v___x_367_ = v_reuseFailAlloc_385_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_226__overap_370_; lean_object* v___x_371_; 
v___x_368_ = l_ReaderT_instMonad___redArg(v___x_367_);
v___x_369_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10);
v___x_226__overap_370_ = l_Lean_mkFreshFVarId___redArg(v___x_368_, v___x_369_);
lean_inc(v_a_326_);
lean_inc_ref(v_a_325_);
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
lean_inc_ref(v_a_322_);
v___x_371_ = lean_apply_6(v___x_226__overap_370_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, lean_box(0));
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_373_; uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc_n(v_a_372_, 2);
lean_dec_ref_known(v___x_371_, 1);
v___x_373_ = l_Lean_Expr_fvar___override(v_a_372_);
v___x_374_ = 0;
lean_inc_ref(v_a_322_);
v___x_375_ = l_Lean_LocalContext_mkLocalDecl(v_a_322_, v_a_372_, v_binderName_318_, v_type_319_, v_binderInfo_320_, v___x_374_);
lean_inc(v_a_326_);
lean_inc_ref(v_a_325_);
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
v___x_376_ = lean_apply_7(v_k_321_, v___x_373_, v___x_375_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, lean_box(0));
return v___x_376_;
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_dec_ref(v_k_321_);
lean_dec_ref(v_type_319_);
lean_dec(v_binderName_318_);
v_a_377_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_371_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_371_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___boxed(lean_object* v_00_u03b1_391_, lean_object* v_binderName_392_, lean_object* v_type_393_, lean_object* v_binderInfo_394_, lean_object* v_k_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
uint8_t v_binderInfo_boxed_402_; lean_object* v_res_403_; 
v_binderInfo_boxed_402_ = lean_unbox(v_binderInfo_394_);
v_res_403_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl(v_00_u03b1_391_, v_binderName_392_, v_type_393_, v_binderInfo_boxed_402_, v_k_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
lean_dec_ref(v_a_396_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(lean_object* v_declName_407_, lean_object* v_us_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__1));
v___x_415_ = lean_name_eq(v_declName_407_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_409_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; uint8_t v___x_418_; lean_object* v___x_419_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_a_417_);
lean_dec_ref_known(v___x_416_, 1);
v___x_418_ = lean_unbox(v_a_417_);
lean_dec(v_a_417_);
lean_inc(v_declName_407_);
v___x_419_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_407_, v___x_418_, v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_430_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_430_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_430_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_430_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
if (lean_obj_tag(v_a_420_) == 1)
{
lean_object* v_val_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
lean_dec(v_declName_407_);
v_val_424_ = lean_ctor_get(v_a_420_, 0);
lean_inc(v_val_424_);
lean_dec_ref_known(v_a_420_, 1);
v___x_425_ = l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg(v_val_424_, v_us_408_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_425_);
v___x_427_ = v___x_422_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
else
{
lean_object* v___x_429_; 
lean_del_object(v___x_422_);
lean_dec(v_a_420_);
v___x_429_ = l_Lean_Compiler_LCNF_getOtherDeclType(v_declName_407_, v_us_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
return v___x_429_;
}
}
}
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
lean_dec(v_us_408_);
lean_dec(v_declName_407_);
v_a_431_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_419_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_419_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
else
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec(v_us_408_);
lean_dec(v_declName_407_);
v_a_439_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_416_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_416_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec(v_us_408_);
lean_dec(v_declName_407_);
v___x_447_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___boxed(lean_object* v_declName_449_, lean_object* v_us_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(v_declName_449_, v_us_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
return v_res_456_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = lean_box(0);
v___x_461_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__1));
v___x_462_ = l_Lean_mkConst(v___x_461_, v___x_460_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = lean_box(0);
v___x_467_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__4));
v___x_468_ = l_Lean_mkConst(v___x_467_, v___x_466_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = lean_box(0);
v___x_473_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__7));
v___x_474_ = l_Lean_mkConst(v___x_473_, v___x_472_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_box(0);
v___x_479_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__10));
v___x_480_ = l_Lean_mkConst(v___x_479_, v___x_478_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_484_ = lean_box(0);
v___x_485_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__13));
v___x_486_ = l_Lean_mkConst(v___x_485_, v___x_484_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = lean_box(0);
v___x_491_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__16));
v___x_492_ = l_Lean_mkConst(v___x_491_, v___x_490_);
return v___x_492_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = lean_box(0);
v___x_497_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__19));
v___x_498_ = l_Lean_mkConst(v___x_497_, v___x_496_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType(lean_object* v_value_499_){
_start:
{
switch(lean_obj_tag(v_value_499_))
{
case 0:
{
lean_object* v___x_500_; 
v___x_500_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2);
return v___x_500_;
}
case 1:
{
lean_object* v___x_501_; 
v___x_501_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5);
return v___x_501_;
}
case 2:
{
lean_object* v___x_502_; 
v___x_502_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8);
return v___x_502_;
}
case 3:
{
lean_object* v___x_503_; 
v___x_503_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11);
return v___x_503_;
}
case 4:
{
lean_object* v___x_504_; 
v___x_504_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14);
return v___x_504_;
}
case 5:
{
lean_object* v___x_505_; 
v___x_505_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17);
return v___x_505_;
}
default: 
{
lean_object* v___x_506_; 
v___x_506_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20);
return v___x_506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___boxed(lean_object* v_value_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType(v_value_507_);
lean_dec_ref(v_value_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(lean_object* v___y_509_){
_start:
{
lean_object* v___x_511_; lean_object* v_ngen_512_; lean_object* v_namePrefix_513_; lean_object* v_idx_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_543_; 
v___x_511_ = lean_st_ref_get(v___y_509_);
v_ngen_512_ = lean_ctor_get(v___x_511_, 2);
lean_inc_ref(v_ngen_512_);
lean_dec(v___x_511_);
v_namePrefix_513_ = lean_ctor_get(v_ngen_512_, 0);
v_idx_514_ = lean_ctor_get(v_ngen_512_, 1);
v_isSharedCheck_543_ = !lean_is_exclusive(v_ngen_512_);
if (v_isSharedCheck_543_ == 0)
{
v___x_516_ = v_ngen_512_;
v_isShared_517_ = v_isSharedCheck_543_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_idx_514_);
lean_inc(v_namePrefix_513_);
lean_dec(v_ngen_512_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_543_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v_env_519_; lean_object* v_nextMacroScope_520_; lean_object* v_auxDeclNGen_521_; lean_object* v_traceState_522_; lean_object* v_cache_523_; lean_object* v_messages_524_; lean_object* v_infoState_525_; lean_object* v_snapshotTasks_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_541_; 
v___x_518_ = lean_st_ref_take(v___y_509_);
v_env_519_ = lean_ctor_get(v___x_518_, 0);
v_nextMacroScope_520_ = lean_ctor_get(v___x_518_, 1);
v_auxDeclNGen_521_ = lean_ctor_get(v___x_518_, 3);
v_traceState_522_ = lean_ctor_get(v___x_518_, 4);
v_cache_523_ = lean_ctor_get(v___x_518_, 5);
v_messages_524_ = lean_ctor_get(v___x_518_, 6);
v_infoState_525_ = lean_ctor_get(v___x_518_, 7);
v_snapshotTasks_526_ = lean_ctor_get(v___x_518_, 8);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_541_ == 0)
{
lean_object* v_unused_542_; 
v_unused_542_ = lean_ctor_get(v___x_518_, 2);
lean_dec(v_unused_542_);
v___x_528_ = v___x_518_;
v_isShared_529_ = v_isSharedCheck_541_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_snapshotTasks_526_);
lean_inc(v_infoState_525_);
lean_inc(v_messages_524_);
lean_inc(v_cache_523_);
lean_inc(v_traceState_522_);
lean_inc(v_auxDeclNGen_521_);
lean_inc(v_nextMacroScope_520_);
lean_inc(v_env_519_);
lean_dec(v___x_518_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_541_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v_r_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
lean_inc(v_idx_514_);
lean_inc(v_namePrefix_513_);
v_r_530_ = l_Lean_Name_num___override(v_namePrefix_513_, v_idx_514_);
v___x_531_ = lean_unsigned_to_nat(1u);
v___x_532_ = lean_nat_add(v_idx_514_, v___x_531_);
lean_dec(v_idx_514_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v___x_532_);
v___x_534_ = v___x_516_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_namePrefix_513_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v___x_532_);
v___x_534_ = v_reuseFailAlloc_540_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_536_; 
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 2, v___x_534_);
v___x_536_ = v___x_528_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_env_519_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_nextMacroScope_520_);
lean_ctor_set(v_reuseFailAlloc_539_, 2, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_539_, 3, v_auxDeclNGen_521_);
lean_ctor_set(v_reuseFailAlloc_539_, 4, v_traceState_522_);
lean_ctor_set(v_reuseFailAlloc_539_, 5, v_cache_523_);
lean_ctor_set(v_reuseFailAlloc_539_, 6, v_messages_524_);
lean_ctor_set(v_reuseFailAlloc_539_, 7, v_infoState_525_);
lean_ctor_set(v_reuseFailAlloc_539_, 8, v_snapshotTasks_526_);
v___x_536_ = v_reuseFailAlloc_539_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_st_ref_put(v___y_509_, v___x_536_);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v_r_530_);
return v___x_538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg___boxed(lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(v___y_544_);
lean_dec(v___y_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___x_553_; lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
v___x_553_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(v___y_551_);
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0___boxed(lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec_ref(v___y_562_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(lean_object* v_msg_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v___x_576_; lean_object* v_toApplicative_577_; lean_object* v_toFunctor_578_; lean_object* v_toSeq_579_; lean_object* v_toSeqLeft_580_; lean_object* v_toSeqRight_581_; lean_object* v___f_582_; lean_object* v___f_583_; lean_object* v___f_584_; lean_object* v___f_585_; lean_object* v___x_586_; lean_object* v___f_587_; lean_object* v___f_588_; lean_object* v___f_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___x_6782__overap_597_; lean_object* v___x_598_; 
v___x_576_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_577_ = lean_ctor_get(v___x_576_, 0);
v_toFunctor_578_ = lean_ctor_get(v_toApplicative_577_, 0);
v_toSeq_579_ = lean_ctor_get(v_toApplicative_577_, 2);
v_toSeqLeft_580_ = lean_ctor_get(v_toApplicative_577_, 3);
v_toSeqRight_581_ = lean_ctor_get(v_toApplicative_577_, 4);
v___f_582_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_583_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_578_, 2);
v___f_584_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_584_, 0, v_toFunctor_578_);
v___f_585_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_585_, 0, v_toFunctor_578_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___f_584_);
lean_ctor_set(v___x_586_, 1, v___f_585_);
lean_inc(v_toSeqRight_581_);
v___f_587_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_587_, 0, v_toSeqRight_581_);
lean_inc(v_toSeqLeft_580_);
v___f_588_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_588_, 0, v_toSeqLeft_580_);
lean_inc(v_toSeq_579_);
v___f_589_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_589_, 0, v_toSeq_579_);
v___x_590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_590_, 0, v___x_586_);
lean_ctor_set(v___x_590_, 1, v___f_582_);
lean_ctor_set(v___x_590_, 2, v___f_589_);
lean_ctor_set(v___x_590_, 3, v___f_588_);
lean_ctor_set(v___x_590_, 4, v___f_587_);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
lean_ctor_set(v___x_591_, 1, v___f_583_);
v___x_592_ = l_StateRefT_x27_instMonad___redArg(v___x_591_);
v___x_593_ = l_Lean_instInhabitedExpr;
v___x_594_ = l_instInhabitedOfMonad___redArg(v___x_592_, v___x_593_);
v___f_595_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_595_, 0, v___x_594_);
v___f_596_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_596_, 0, v___f_595_);
v___x_6782__overap_597_ = lean_panic_fn_borrowed(v___f_596_, v_msg_569_);
lean_dec_ref(v___f_596_);
lean_inc(v___y_574_);
lean_inc_ref(v___y_573_);
lean_inc(v___y_572_);
lean_inc_ref(v___y_571_);
lean_inc_ref(v___y_570_);
v___x_598_ = lean_apply_6(v___x_6782__overap_597_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, lean_box(0));
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2___boxed(lean_object* v_msg_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(v_msg_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec_ref(v___y_600_);
return v_res_606_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(lean_object* v_upperBound_609_, lean_object* v___x_610_, lean_object* v_a_611_, lean_object* v_b_612_){
_start:
{
lean_object* v_a_615_; uint8_t v___x_619_; 
v___x_619_ = lean_nat_dec_lt(v_a_611_, v_upperBound_609_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
lean_dec(v_a_611_);
v___x_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_620_, 0, v_b_612_);
return v___x_620_;
}
else
{
lean_object* v_snd_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_657_; 
v_snd_621_ = lean_ctor_get(v_b_612_, 1);
v_isSharedCheck_657_ = !lean_is_exclusive(v_b_612_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; 
v_unused_658_ = lean_ctor_get(v_b_612_, 0);
lean_dec(v_unused_658_);
v___x_623_ = v_b_612_;
v_isShared_624_ = v_isSharedCheck_657_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_snd_621_);
lean_dec(v_b_612_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_657_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v_fst_625_; lean_object* v_snd_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_656_; 
v_fst_625_ = lean_ctor_get(v_snd_621_, 0);
v_snd_626_ = lean_ctor_get(v_snd_621_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_snd_621_);
if (v_isSharedCheck_656_ == 0)
{
v___x_628_ = v_snd_621_;
v_isShared_629_ = v_isSharedCheck_656_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_snd_626_);
lean_inc(v_fst_625_);
lean_dec(v_snd_621_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_656_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_box(0);
v___x_631_ = l_Lean_Expr_headBeta(v_snd_626_);
if (lean_obj_tag(v___x_631_) == 7)
{
lean_object* v_body_632_; lean_object* v___x_634_; 
v_body_632_ = lean_ctor_get(v___x_631_, 2);
lean_inc_ref(v_body_632_);
lean_dec_ref_known(v___x_631_, 3);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v_body_632_);
v___x_634_ = v___x_628_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_fst_625_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_body_632_);
v___x_634_ = v_reuseFailAlloc_638_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_636_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 1, v___x_634_);
lean_ctor_set(v___x_623_, 0, v___x_630_);
v___x_636_ = v___x_623_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
v_a_615_ = v___x_636_;
goto v___jp_614_;
}
}
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_expr_instantiate_rev_range(v___x_631_, v_fst_625_, v_a_611_, v___x_610_);
lean_dec_ref(v___x_631_);
v___x_640_ = l_Lean_Expr_headBeta(v___x_639_);
if (lean_obj_tag(v___x_640_) == 7)
{
lean_object* v_body_641_; lean_object* v___x_643_; 
lean_dec(v_fst_625_);
v_body_641_ = lean_ctor_get(v___x_640_, 2);
lean_inc_ref(v_body_641_);
lean_dec_ref_known(v___x_640_, 3);
lean_inc(v_a_611_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v_body_641_);
lean_ctor_set(v___x_628_, 0, v_a_611_);
v___x_643_ = v___x_628_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_611_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_body_641_);
v___x_643_ = v_reuseFailAlloc_647_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_645_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 1, v___x_643_);
lean_ctor_set(v___x_623_, 0, v___x_630_);
v___x_645_ = v___x_623_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
v_a_615_ = v___x_645_;
goto v___jp_614_;
}
}
}
else
{
lean_object* v___x_648_; lean_object* v___x_650_; 
lean_dec(v_a_611_);
v___x_648_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v___x_640_);
v___x_650_ = v___x_628_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_fst_625_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v___x_640_);
v___x_650_ = v_reuseFailAlloc_655_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v___x_652_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 1, v___x_650_);
lean_ctor_set(v___x_623_, 0, v___x_648_);
v___x_652_ = v___x_623_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v___x_650_);
v___x_652_ = v_reuseFailAlloc_654_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_653_; 
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
return v___x_653_;
}
}
}
}
}
}
}
v___jp_614_:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_unsigned_to_nat(1u);
v___x_617_ = lean_nat_add(v_a_611_, v___x_616_);
lean_dec(v_a_611_);
v_a_611_ = v___x_617_;
v_b_612_ = v_a_615_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___boxed(lean_object* v_upperBound_659_, lean_object* v___x_660_, lean_object* v_a_661_, lean_object* v_b_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v_upperBound_659_, v___x_660_, v_a_661_, v_b_662_);
lean_dec_ref(v___x_660_);
lean_dec(v_upperBound_659_);
return v_res_664_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0(void){
_start:
{
lean_object* v___x_667_; lean_object* v_dummy_668_; 
v___x_667_ = lean_box(0);
v_dummy_668_ = l_Lean_Expr_sort___override(v___x_667_);
return v_dummy_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(lean_object* v_e_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = l_Lean_Expr_getAppFn(v_e_669_);
v___x_677_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v___x_676_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v_dummy_679_; lean_object* v_nargs_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v___x_677_, 1);
v_dummy_679_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0);
v_nargs_680_ = l_Lean_Expr_getAppNumArgs(v_e_669_);
lean_inc(v_nargs_680_);
v___x_681_ = lean_mk_array(v_nargs_680_, v_dummy_679_);
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = lean_nat_sub(v_nargs_680_, v___x_682_);
lean_dec(v_nargs_680_);
v___x_684_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_669_, v___x_681_, v___x_683_);
v___x_685_ = lean_array_get_size(v___x_684_);
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = lean_box(0);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v_a_678_);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v___x_685_, v___x_684_, v___x_686_, v___x_689_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_708_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_708_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_708_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_708_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v_fst_695_; 
v_fst_695_ = lean_ctor_get(v_a_691_, 0);
if (lean_obj_tag(v_fst_695_) == 0)
{
lean_object* v_snd_696_; lean_object* v_fst_697_; lean_object* v_snd_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
v_snd_696_ = lean_ctor_get(v_a_691_, 1);
lean_inc(v_snd_696_);
lean_dec(v_a_691_);
v_fst_697_ = lean_ctor_get(v_snd_696_, 0);
lean_inc(v_fst_697_);
v_snd_698_ = lean_ctor_get(v_snd_696_, 1);
lean_inc(v_snd_698_);
lean_dec(v_snd_696_);
v___x_699_ = lean_expr_instantiate_rev_range(v_snd_698_, v_fst_697_, v___x_685_, v___x_684_);
lean_dec_ref(v___x_684_);
lean_dec(v_fst_697_);
lean_dec(v_snd_698_);
v___x_700_ = l_Lean_Expr_headBeta(v___x_699_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_700_);
v___x_702_ = v___x_693_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
else
{
lean_object* v_val_704_; lean_object* v___x_706_; 
lean_inc_ref(v_fst_695_);
lean_dec(v_a_691_);
lean_dec_ref(v___x_684_);
v_val_704_ = lean_ctor_get(v_fst_695_, 0);
lean_inc(v_val_704_);
lean_dec_ref_known(v_fst_695_, 1);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v_val_704_);
v___x_706_ = v___x_693_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_val_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec_ref(v___x_684_);
v_a_709_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_690_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_690_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
else
{
lean_dec_ref(v_e_669_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(lean_object* v_e_717_, lean_object* v_fvars_718_, lean_object* v_all_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
switch(lean_obj_tag(v_e_717_))
{
case 6:
{
lean_object* v_binderName_726_; lean_object* v_binderType_727_; lean_object* v_body_728_; uint8_t v_binderInfo_729_; lean_object* v___x_730_; 
v_binderName_726_ = lean_ctor_get(v_e_717_, 0);
lean_inc(v_binderName_726_);
v_binderType_727_ = lean_ctor_get(v_e_717_, 1);
lean_inc_ref(v_binderType_727_);
v_body_728_ = lean_ctor_get(v_e_717_, 2);
lean_inc_ref(v_body_728_);
v_binderInfo_729_ = lean_ctor_get_uint8(v_e_717_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_717_, 3);
v___x_730_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc_n(v_a_731_, 2);
lean_dec_ref_known(v___x_730_, 1);
v___x_732_ = lean_expr_instantiate_rev(v_binderType_727_, v_all_719_);
lean_dec_ref(v_binderType_727_);
v___x_733_ = l_Lean_Expr_fvar___override(v_a_731_);
v___x_734_ = 0;
v___x_735_ = l_Lean_LocalContext_mkLocalDecl(v_a_720_, v_a_731_, v_binderName_726_, v___x_732_, v_binderInfo_729_, v___x_734_);
lean_inc_ref(v___x_733_);
v___x_736_ = lean_array_push(v_fvars_718_, v___x_733_);
v___x_737_ = lean_array_push(v_all_719_, v___x_733_);
v_e_717_ = v_body_728_;
v_fvars_718_ = v___x_736_;
v_all_719_ = v___x_737_;
v_a_720_ = v___x_735_;
goto _start;
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec_ref(v_body_728_);
lean_dec_ref(v_binderType_727_);
lean_dec(v_binderName_726_);
lean_dec_ref(v_a_720_);
lean_dec_ref(v_all_719_);
lean_dec_ref(v_fvars_718_);
v_a_739_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_730_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_730_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
case 8:
{
lean_object* v_declName_747_; lean_object* v_type_748_; lean_object* v_body_749_; lean_object* v___x_750_; 
v_declName_747_ = lean_ctor_get(v_e_717_, 0);
lean_inc(v_declName_747_);
v_type_748_ = lean_ctor_get(v_e_717_, 1);
lean_inc_ref(v_type_748_);
v_body_749_ = lean_ctor_get(v_e_717_, 3);
lean_inc_ref(v_body_749_);
lean_dec_ref_known(v_e_717_, 4);
v___x_750_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_752_; uint8_t v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc_n(v_a_751_, 2);
lean_dec_ref_known(v___x_750_, 1);
v___x_752_ = lean_expr_instantiate_rev(v_type_748_, v_all_719_);
lean_dec_ref(v_type_748_);
v___x_753_ = 0;
v___x_754_ = l_Lean_Expr_fvar___override(v_a_751_);
v___x_755_ = 0;
v___x_756_ = l_Lean_LocalContext_mkLocalDecl(v_a_720_, v_a_751_, v_declName_747_, v___x_752_, v___x_753_, v___x_755_);
v___x_757_ = lean_array_push(v_all_719_, v___x_754_);
v_e_717_ = v_body_749_;
v_all_719_ = v___x_757_;
v_a_720_ = v___x_756_;
goto _start;
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec_ref(v_body_749_);
lean_dec_ref(v_type_748_);
lean_dec(v_declName_747_);
lean_dec_ref(v_a_720_);
lean_dec_ref(v_all_719_);
lean_dec_ref(v_fvars_718_);
v_a_759_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_750_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_750_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
default: 
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_expr_instantiate_rev(v_e_717_, v_all_719_);
lean_dec_ref(v_all_719_);
lean_dec_ref(v_e_717_);
v___x_768_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v___x_767_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_770_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
v___x_770_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v_fvars_718_, v_a_769_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_769_);
lean_dec_ref(v_fvars_718_);
return v___x_770_;
}
else
{
lean_dec_ref(v_a_720_);
lean_dec_ref(v_fvars_718_);
return v___x_768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(lean_object* v_e_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0));
lean_inc_ref(v_a_772_);
v___x_779_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(v_e_771_, v___x_778_, v___x_778_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
return v___x_779_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_783_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2));
v___x_784_ = lean_unsigned_to_nat(73u);
v___x_785_ = lean_unsigned_to_nat(135u);
v___x_786_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__1));
v___x_787_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_788_ = l_mkPanicMessageWithDecl(v___x_787_, v___x_786_, v___x_785_, v___x_784_, v___x_783_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType(lean_object* v_e_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
switch(lean_obj_tag(v_e_789_))
{
case 1:
{
lean_object* v_fvarId_796_; lean_object* v___x_797_; 
v_fvarId_796_ = lean_ctor_get(v_e_789_, 0);
lean_inc(v_fvarId_796_);
lean_dec_ref_known(v_e_789_, 1);
v___x_797_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_fvarId_796_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
return v___x_797_;
}
case 3:
{
lean_object* v_u_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_u_798_ = lean_ctor_get(v_e_789_, 0);
lean_inc(v_u_798_);
lean_dec_ref_known(v_e_789_, 1);
v___x_799_ = l_Lean_Level_succ___override(v_u_798_);
v___x_800_ = l_Lean_Expr_sort___override(v___x_799_);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
case 4:
{
lean_object* v_declName_802_; lean_object* v_us_803_; lean_object* v___x_804_; 
v_declName_802_ = lean_ctor_get(v_e_789_, 0);
lean_inc(v_declName_802_);
v_us_803_ = lean_ctor_get(v_e_789_, 1);
lean_inc(v_us_803_);
lean_dec_ref_known(v_e_789_, 2);
v___x_804_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(v_declName_802_, v_us_803_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
return v___x_804_;
}
case 5:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(v_e_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
return v___x_805_;
}
case 6:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(v_e_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
return v___x_806_;
}
case 7:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(v_e_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
return v___x_807_;
}
default: 
{
lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec_ref(v_e_789_);
v___x_808_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3, &l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3);
v___x_809_ = l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(v___x_808_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
return v___x_809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(lean_object* v_type_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_type_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_831_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_831_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_831_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_831_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
if (lean_obj_tag(v_a_818_) == 3)
{
lean_object* v_u_822_; lean_object* v___x_823_; lean_object* v___x_825_; 
v_u_822_ = lean_ctor_get(v_a_818_, 0);
lean_inc(v_u_822_);
lean_dec_ref_known(v_a_818_, 1);
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v_u_822_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_823_);
v___x_825_ = v___x_820_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
else
{
lean_object* v___x_827_; lean_object* v___x_829_; 
lean_dec(v_a_818_);
v___x_827_ = lean_box(0);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_827_);
v___x_829_ = v___x_820_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
v_a_832_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_817_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_817_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(lean_object* v_as_842_, size_t v_sz_843_, size_t v_i_844_, lean_object* v_b_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
uint8_t v___x_852_; 
v___x_852_ = lean_usize_dec_lt(v_i_844_, v_sz_843_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; 
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v_b_845_);
return v___x_853_;
}
else
{
lean_object* v_a_854_; lean_object* v___x_855_; 
v_a_854_ = lean_array_uget_borrowed(v_as_842_, v_i_844_);
lean_inc(v_a_854_);
v___x_855_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_a_854_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_857_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_855_, 1);
v___x_857_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(v_a_856_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_890_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_890_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_890_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_890_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
if (lean_obj_tag(v_a_858_) == 1)
{
lean_object* v_snd_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_875_; 
lean_del_object(v___x_860_);
v_snd_862_ = lean_ctor_get(v_b_845_, 1);
v_isSharedCheck_875_ = !lean_is_exclusive(v_b_845_);
if (v_isSharedCheck_875_ == 0)
{
lean_object* v_unused_876_; 
v_unused_876_ = lean_ctor_get(v_b_845_, 0);
lean_dec(v_unused_876_);
v___x_864_ = v_b_845_;
v_isShared_865_ = v_isSharedCheck_875_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_snd_862_);
lean_dec(v_b_845_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_875_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v_val_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
v_val_866_ = lean_ctor_get(v_a_858_, 0);
lean_inc(v_val_866_);
lean_dec_ref_known(v_a_858_, 1);
v___x_867_ = lean_box(0);
v___x_868_ = l_Lean_mkLevelIMax_x27(v_val_866_, v_snd_862_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v___x_868_);
lean_ctor_set(v___x_864_, 0, v___x_867_);
v___x_870_ = v___x_864_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v___x_868_);
v___x_870_ = v_reuseFailAlloc_874_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
size_t v___x_871_; size_t v___x_872_; 
v___x_871_ = ((size_t)1ULL);
v___x_872_ = lean_usize_add(v_i_844_, v___x_871_);
v_i_844_ = v___x_872_;
v_b_845_ = v___x_870_;
goto _start;
}
}
}
else
{
lean_object* v_snd_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_888_; 
lean_dec(v_a_858_);
v_snd_877_ = lean_ctor_get(v_b_845_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v_b_845_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; 
v_unused_889_ = lean_ctor_get(v_b_845_, 0);
lean_dec(v_unused_889_);
v___x_879_ = v_b_845_;
v_isShared_880_ = v_isSharedCheck_888_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_snd_877_);
lean_dec(v_b_845_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_888_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_881_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_881_);
v___x_883_ = v___x_879_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_snd_877_);
v___x_883_ = v_reuseFailAlloc_887_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_883_);
v___x_885_ = v___x_860_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec_ref(v_b_845_);
v_a_891_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_857_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_857_);
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
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_dec_ref(v_b_845_);
v_a_899_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_855_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_855_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(lean_object* v_e_907_, lean_object* v_fvars_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
if (lean_obj_tag(v_e_907_) == 7)
{
lean_object* v_binderName_915_; lean_object* v_binderType_916_; lean_object* v_body_917_; uint8_t v_binderInfo_918_; lean_object* v___x_919_; 
v_binderName_915_ = lean_ctor_get(v_e_907_, 0);
lean_inc(v_binderName_915_);
v_binderType_916_ = lean_ctor_get(v_e_907_, 1);
lean_inc_ref(v_binderType_916_);
v_body_917_ = lean_ctor_get(v_e_907_, 2);
lean_inc_ref(v_body_917_);
v_binderInfo_918_ = lean_ctor_get_uint8(v_e_907_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_907_, 3);
v___x_919_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc_n(v_a_920_, 2);
lean_dec_ref_known(v___x_919_, 1);
v___x_921_ = lean_expr_instantiate_rev(v_binderType_916_, v_fvars_908_);
lean_dec_ref(v_binderType_916_);
v___x_922_ = l_Lean_Expr_fvar___override(v_a_920_);
v___x_923_ = 0;
v___x_924_ = l_Lean_LocalContext_mkLocalDecl(v_a_909_, v_a_920_, v_binderName_915_, v___x_921_, v_binderInfo_918_, v___x_923_);
v___x_925_ = lean_array_push(v_fvars_908_, v___x_922_);
v_e_907_ = v_body_917_;
v_fvars_908_ = v___x_925_;
v_a_909_ = v___x_924_;
goto _start;
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec_ref(v_body_917_);
lean_dec_ref(v_binderType_916_);
lean_dec(v_binderName_915_);
lean_dec_ref(v_a_909_);
lean_dec_ref(v_fvars_908_);
v_a_927_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_919_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_919_);
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
lean_object* v_e_935_; lean_object* v___x_936_; 
v_e_935_ = lean_expr_instantiate_rev(v_e_907_, v_fvars_908_);
lean_dec_ref(v_e_907_);
v___x_936_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(v_e_935_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_976_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_976_ == 0)
{
v___x_939_ = v___x_936_;
v_isShared_940_ = v_isSharedCheck_976_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_976_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
if (lean_obj_tag(v_a_937_) == 1)
{
lean_object* v_val_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; size_t v_sz_945_; size_t v___x_946_; lean_object* v___x_947_; 
lean_del_object(v___x_939_);
v_val_941_ = lean_ctor_get(v_a_937_, 0);
lean_inc(v_val_941_);
lean_dec_ref_known(v_a_937_, 1);
v___x_942_ = l_Array_reverse___redArg(v_fvars_908_);
v___x_943_ = lean_box(0);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v_val_941_);
v_sz_945_ = lean_array_size(v___x_942_);
v___x_946_ = ((size_t)0ULL);
v___x_947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(v___x_942_, v_sz_945_, v___x_946_, v___x_944_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
lean_dec_ref(v_a_909_);
lean_dec_ref(v___x_942_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_963_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_963_ == 0)
{
v___x_950_ = v___x_947_;
v_isShared_951_ = v_isSharedCheck_963_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_947_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_963_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v_fst_952_; 
v_fst_952_ = lean_ctor_get(v_a_948_, 0);
if (lean_obj_tag(v_fst_952_) == 0)
{
lean_object* v_snd_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_957_; 
v_snd_953_ = lean_ctor_get(v_a_948_, 1);
lean_inc(v_snd_953_);
lean_dec(v_a_948_);
v___x_954_ = l_Lean_Level_normalize(v_snd_953_);
lean_dec(v_snd_953_);
v___x_955_ = l_Lean_Expr_sort___override(v___x_954_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v___x_955_);
v___x_957_ = v___x_950_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
else
{
lean_object* v_val_959_; lean_object* v___x_961_; 
lean_inc_ref(v_fst_952_);
lean_dec(v_a_948_);
v_val_959_ = lean_ctor_get(v_fst_952_, 0);
lean_inc(v_val_959_);
lean_dec_ref_known(v_fst_952_, 1);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v_val_959_);
v___x_961_ = v___x_950_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_val_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
v_a_964_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_947_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_947_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
else
{
lean_object* v___x_972_; lean_object* v___x_974_; 
lean_dec(v_a_937_);
lean_dec_ref(v_a_909_);
lean_dec_ref(v_fvars_908_);
v___x_972_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_972_);
v___x_974_ = v___x_939_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec_ref(v_a_909_);
lean_dec_ref(v_fvars_908_);
v_a_977_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_936_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_936_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(lean_object* v_e_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0));
lean_inc_ref(v_a_986_);
v___x_993_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(v_e_985_, v___x_992_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___boxed(lean_object* v_e_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(v_e_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec_ref(v_a_995_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType___boxed(lean_object* v_e_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(v_e_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
lean_dec_ref(v_a_1003_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f___boxed(lean_object* v_type_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(v_type_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
lean_dec_ref(v_a_1011_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType___boxed(lean_object* v_e_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_e_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec_ref(v_a_1019_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___boxed(lean_object* v_as_1026_, lean_object* v_sz_1027_, lean_object* v_i_1028_, lean_object* v_b_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
size_t v_sz_boxed_1036_; size_t v_i_boxed_1037_; lean_object* v_res_1038_; 
v_sz_boxed_1036_ = lean_unbox_usize(v_sz_1027_);
lean_dec(v_sz_1027_);
v_i_boxed_1037_ = lean_unbox_usize(v_i_1028_);
lean_dec(v_i_1028_);
v_res_1038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(v_as_1026_, v_sz_boxed_1036_, v_i_boxed_1037_, v_b_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec_ref(v_as_1026_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___boxed(lean_object* v_e_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(v_e_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec_ref(v_a_1040_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go___boxed(lean_object* v_e_1047_, lean_object* v_fvars_1048_, lean_object* v_all_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(v_e_1047_, v_fvars_1048_, v_all_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go___boxed(lean_object* v_e_1057_, lean_object* v_fvars_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(v_e_1057_, v_fvars_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3(lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(v___y_1070_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___boxed(lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3(v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec_ref(v___y_1073_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9(lean_object* v_upperBound_1080_, lean_object* v___x_1081_, lean_object* v_inst_1082_, lean_object* v_R_1083_, lean_object* v_a_1084_, lean_object* v_b_1085_, lean_object* v_c_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v_upperBound_1080_, v___x_1081_, v_a_1084_, v_b_1085_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___boxed(lean_object* v_upperBound_1094_, lean_object* v___x_1095_, lean_object* v_inst_1096_, lean_object* v_R_1097_, lean_object* v_a_1098_, lean_object* v_b_1099_, lean_object* v_c_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9(v_upperBound_1094_, v___x_1095_, v_inst_1096_, v_R_1097_, v_a_1098_, v_b_1099_, v_c_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec_ref(v___x_1095_);
lean_dec(v_upperBound_1094_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(lean_object* v_arg_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
switch(lean_obj_tag(v_arg_1108_))
{
case 0:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
return v___x_1116_;
}
case 1:
{
lean_object* v_fvarId_1117_; lean_object* v___x_1118_; 
v_fvarId_1117_ = lean_ctor_get(v_arg_1108_, 0);
lean_inc(v_fvarId_1117_);
lean_dec_ref_known(v_arg_1108_, 1);
v___x_1118_ = l_Lean_Compiler_LCNF_getType(v_fvarId_1117_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
return v___x_1118_;
}
default: 
{
lean_object* v_expr_1119_; lean_object* v___x_1120_; 
v_expr_1119_ = lean_ctor_get(v_arg_1108_, 0);
lean_inc_ref(v_expr_1119_);
lean_dec_ref_known(v_arg_1108_, 1);
v___x_1120_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_expr_1119_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
return v___x_1120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferArgType___boxed(lean_object* v_arg_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(v_arg_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec_ref(v_a_1122_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(lean_object* v_upperBound_1129_, lean_object* v_args_1130_, lean_object* v_a_1131_, lean_object* v_b_1132_){
_start:
{
lean_object* v_a_1135_; uint8_t v___x_1139_; 
v___x_1139_ = lean_nat_dec_lt(v_a_1131_, v_upperBound_1129_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; 
lean_dec(v_a_1131_);
lean_dec_ref(v_args_1130_);
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v_b_1132_);
return v___x_1140_;
}
else
{
lean_object* v_snd_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1177_; 
v_snd_1141_ = lean_ctor_get(v_b_1132_, 1);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_b_1132_);
if (v_isSharedCheck_1177_ == 0)
{
lean_object* v_unused_1178_; 
v_unused_1178_ = lean_ctor_get(v_b_1132_, 0);
lean_dec(v_unused_1178_);
v___x_1143_ = v_b_1132_;
v_isShared_1144_ = v_isSharedCheck_1177_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_snd_1141_);
lean_dec(v_b_1132_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1177_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v_fst_1145_; lean_object* v_snd_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1176_; 
v_fst_1145_ = lean_ctor_get(v_snd_1141_, 0);
v_snd_1146_ = lean_ctor_get(v_snd_1141_, 1);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_snd_1141_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1148_ = v_snd_1141_;
v_isShared_1149_ = v_isSharedCheck_1176_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_snd_1146_);
lean_inc(v_fst_1145_);
lean_dec(v_snd_1141_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1176_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = lean_box(0);
v___x_1151_ = l_Lean_Expr_headBeta(v_snd_1146_);
if (lean_obj_tag(v___x_1151_) == 7)
{
lean_object* v_body_1152_; lean_object* v___x_1154_; 
v_body_1152_ = lean_ctor_get(v___x_1151_, 2);
lean_inc_ref(v_body_1152_);
lean_dec_ref_known(v___x_1151_, 3);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v_body_1152_);
v___x_1154_ = v___x_1148_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_fst_1145_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_body_1152_);
v___x_1154_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1156_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v___x_1154_);
lean_ctor_set(v___x_1143_, 0, v___x_1150_);
v___x_1156_ = v___x_1143_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
v_a_1135_ = v___x_1156_;
goto v___jp_1134_;
}
}
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_inc_ref(v_args_1130_);
v___x_1159_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(v___x_1151_, v_fst_1145_, v_a_1131_, v_args_1130_);
lean_dec_ref(v___x_1151_);
v___x_1160_ = l_Lean_Expr_headBeta(v___x_1159_);
if (lean_obj_tag(v___x_1160_) == 7)
{
lean_object* v_body_1161_; lean_object* v___x_1163_; 
lean_dec(v_fst_1145_);
v_body_1161_ = lean_ctor_get(v___x_1160_, 2);
lean_inc_ref(v_body_1161_);
lean_dec_ref_known(v___x_1160_, 3);
lean_inc(v_a_1131_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v_body_1161_);
lean_ctor_set(v___x_1148_, 0, v_a_1131_);
v___x_1163_ = v___x_1148_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1131_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_body_1161_);
v___x_1163_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1165_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v___x_1163_);
lean_ctor_set(v___x_1143_, 0, v___x_1150_);
v___x_1165_ = v___x_1143_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
v_a_1135_ = v___x_1165_;
goto v___jp_1134_;
}
}
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1170_; 
lean_dec(v_a_1131_);
lean_dec_ref(v_args_1130_);
v___x_1168_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v___x_1160_);
v___x_1170_ = v___x_1148_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_fst_1145_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v___x_1160_);
v___x_1170_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1172_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v___x_1170_);
lean_ctor_set(v___x_1143_, 0, v___x_1168_);
v___x_1172_ = v___x_1143_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
return v___x_1173_;
}
}
}
}
}
}
}
v___jp_1134_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = lean_unsigned_to_nat(1u);
v___x_1137_ = lean_nat_add(v_a_1131_, v___x_1136_);
lean_dec(v_a_1131_);
v_a_1131_ = v___x_1137_;
v_b_1132_ = v_a_1135_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg___boxed(lean_object* v_upperBound_1179_, lean_object* v_args_1180_, lean_object* v_a_1181_, lean_object* v_b_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v_upperBound_1179_, v_args_1180_, v_a_1181_, v_b_1182_);
lean_dec(v_upperBound_1179_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(lean_object* v_fType_1185_, lean_object* v_args_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1193_ = lean_array_get_size(v_args_1186_);
v___x_1194_ = lean_unsigned_to_nat(0u);
v___x_1195_ = lean_box(0);
v___x_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1194_);
lean_ctor_set(v___x_1196_, 1, v_fType_1185_);
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1195_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
lean_inc_ref(v_args_1186_);
v___x_1198_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v___x_1193_, v_args_1186_, v___x_1194_, v___x_1197_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1216_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1216_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1216_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v_fst_1203_; 
v_fst_1203_ = lean_ctor_get(v_a_1199_, 0);
if (lean_obj_tag(v_fst_1203_) == 0)
{
lean_object* v_snd_1204_; lean_object* v_fst_1205_; lean_object* v_snd_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v_snd_1204_ = lean_ctor_get(v_a_1199_, 1);
lean_inc(v_snd_1204_);
lean_dec(v_a_1199_);
v_fst_1205_ = lean_ctor_get(v_snd_1204_, 0);
lean_inc(v_fst_1205_);
v_snd_1206_ = lean_ctor_get(v_snd_1204_, 1);
lean_inc(v_snd_1206_);
lean_dec(v_snd_1204_);
v___x_1207_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(v_snd_1206_, v_fst_1205_, v___x_1193_, v_args_1186_);
lean_dec(v_fst_1205_);
lean_dec(v_snd_1206_);
v___x_1208_ = l_Lean_Expr_headBeta(v___x_1207_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1208_);
v___x_1210_ = v___x_1201_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
else
{
lean_object* v_val_1212_; lean_object* v___x_1214_; 
lean_inc_ref(v_fst_1203_);
lean_dec(v_a_1199_);
lean_dec_ref(v_args_1186_);
v_val_1212_ = lean_ctor_get(v_fst_1203_, 0);
lean_inc(v_val_1212_);
lean_dec_ref_known(v_fst_1203_, 1);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v_val_1212_);
v___x_1214_ = v___x_1201_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_val_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec_ref(v_args_1186_);
v_a_1217_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1198_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1198_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore___boxed(lean_object* v_fType_1225_, lean_object* v_args_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_fType_1225_, v_args_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec_ref(v_a_1227_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0(lean_object* v_upperBound_1234_, lean_object* v_args_1235_, lean_object* v_inst_1236_, lean_object* v_R_1237_, lean_object* v_a_1238_, lean_object* v_b_1239_, lean_object* v_c_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v_upperBound_1234_, v_args_1235_, v_a_1238_, v_b_1239_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___boxed(lean_object* v_upperBound_1248_, lean_object* v_args_1249_, lean_object* v_inst_1250_, lean_object* v_R_1251_, lean_object* v_a_1252_, lean_object* v_b_1253_, lean_object* v_c_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0(v_upperBound_1248_, v_args_1249_, v_inst_1250_, v_R_1251_, v_a_1252_, v_b_1253_, v_c_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v_upperBound_1248_);
return v_res_1261_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1262_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0);
v___x_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
return v___x_1264_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1);
v___x_1266_ = lean_unsigned_to_nat(0u);
v___x_1267_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
lean_ctor_set(v___x_1267_, 2, v___x_1266_);
lean_ctor_set(v___x_1267_, 3, v___x_1266_);
lean_ctor_set(v___x_1267_, 4, v___x_1265_);
lean_ctor_set(v___x_1267_, 5, v___x_1265_);
lean_ctor_set(v___x_1267_, 6, v___x_1265_);
lean_ctor_set(v___x_1267_, 7, v___x_1265_);
lean_ctor_set(v___x_1267_, 8, v___x_1265_);
lean_ctor_set(v___x_1267_, 9, v___x_1265_);
lean_ctor_set(v___x_1267_, 10, v___x_1265_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(lean_object* v_msg_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_options_1274_; lean_object* v_ref_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v_options_1274_ = lean_ctor_get(v___y_1271_, 1);
v_ref_1275_ = lean_ctor_get(v___y_1271_, 4);
v___x_1276_ = lean_st_ref_get(v___y_1272_);
v___x_1277_ = lean_st_ref_get(v___y_1270_);
v___x_1278_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1269_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1301_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1301_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1301_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v_env_1283_; lean_object* v_lctx_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1299_; 
v_env_1283_ = lean_ctor_get(v___x_1276_, 0);
lean_inc_ref(v_env_1283_);
lean_dec(v___x_1276_);
v_lctx_1284_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1299_ == 0)
{
lean_object* v_unused_1300_; 
v_unused_1300_ = lean_ctor_get(v___x_1277_, 1);
lean_dec(v_unused_1300_);
v___x_1286_ = v___x_1277_;
v_isShared_1287_ = v_isSharedCheck_1299_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_lctx_1284_);
lean_dec(v___x_1277_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1299_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
uint8_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1288_ = lean_unbox(v_a_1279_);
lean_dec(v_a_1279_);
v___x_1289_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1284_, v___x_1288_);
lean_dec_ref(v_lctx_1284_);
v___x_1290_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2);
lean_inc_ref(v_options_1274_);
v___x_1291_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1291_, 0, v_env_1283_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
lean_ctor_set(v___x_1291_, 2, v___x_1289_);
lean_ctor_set(v___x_1291_, 3, v_options_1274_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set_tag(v___x_1286_, 3);
lean_ctor_set(v___x_1286_, 1, v_msg_1268_);
lean_ctor_set(v___x_1286_, 0, v___x_1291_);
v___x_1293_ = v___x_1286_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v_msg_1268_);
v___x_1293_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1294_; lean_object* v___x_1296_; 
lean_inc(v_ref_1275_);
v___x_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1294_, 0, v_ref_1275_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set_tag(v___x_1281_, 1);
lean_ctor_set(v___x_1281_, 0, v___x_1294_);
v___x_1296_ = v___x_1281_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec(v___x_1277_);
lean_dec(v___x_1276_);
lean_dec_ref(v_msg_1268_);
v_a_1302_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1278_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1278_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___boxed(lean_object* v_msg_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v_msg_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0(lean_object* v_00_u03b1_1317_, lean_object* v_msg_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v_msg_1318_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___boxed(lean_object* v_00_u03b1_1326_, lean_object* v_msg_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0(v_00_u03b1_1326_, v_msg_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec_ref(v___y_1328_);
return v_res_1334_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__0));
v___x_1337_ = l_Lean_stringToMessageData(v___x_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(lean_object* v_upperBound_1338_, lean_object* v_s_1339_, lean_object* v_structName_1340_, lean_object* v_idx_1341_, lean_object* v_a_1342_, lean_object* v_b_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_a_1351_; uint8_t v___x_1355_; 
v___x_1355_ = lean_nat_dec_lt(v_a_1342_, v_upperBound_1338_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; 
lean_dec(v_a_1342_);
lean_dec(v_idx_1341_);
lean_dec(v_structName_1340_);
lean_dec(v_s_1339_);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_b_1343_);
return v___x_1356_;
}
else
{
lean_object* v_snd_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1395_; 
v_snd_1357_ = lean_ctor_get(v_b_1343_, 1);
v_isSharedCheck_1395_ = !lean_is_exclusive(v_b_1343_);
if (v_isSharedCheck_1395_ == 0)
{
lean_object* v_unused_1396_; 
v_unused_1396_ = lean_ctor_get(v_b_1343_, 0);
lean_dec(v_unused_1396_);
v___x_1359_ = v_b_1343_;
v_isShared_1360_ = v_isSharedCheck_1395_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_snd_1357_);
lean_dec(v_b_1343_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1395_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_box(0);
if (lean_obj_tag(v_snd_1357_) == 7)
{
lean_object* v_body_1362_; uint8_t v___x_1363_; 
v_body_1362_ = lean_ctor_get(v_snd_1357_, 2);
lean_inc_ref(v_body_1362_);
lean_dec_ref_known(v_snd_1357_, 3);
v___x_1363_ = l_Lean_Expr_hasLooseBVars(v_body_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1365_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 1, v_body_1362_);
lean_ctor_set(v___x_1359_, 0, v___x_1361_);
v___x_1365_ = v___x_1359_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_body_1362_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
v_a_1351_ = v___x_1365_;
goto v___jp_1350_;
}
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1367_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_1368_ = lean_expr_instantiate1(v_body_1362_, v___x_1367_);
lean_dec_ref(v_body_1362_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 1, v___x_1368_);
lean_ctor_set(v___x_1359_, 0, v___x_1361_);
v___x_1370_ = v___x_1359_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
v_a_1351_ = v___x_1370_;
goto v___jp_1350_;
}
}
}
else
{
uint8_t v___x_1372_; 
v___x_1372_ = l_Lean_Expr_isErased(v_snd_1357_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1373_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
lean_inc(v_s_1339_);
v___x_1374_ = l_Lean_mkFVar(v_s_1339_);
lean_inc(v_idx_1341_);
lean_inc(v_structName_1340_);
v___x_1375_ = l_Lean_mkProj(v_structName_1340_, v_idx_1341_, v___x_1374_);
v___x_1376_ = l_Lean_indentExpr(v___x_1375_);
v___x_1377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1373_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v___x_1378_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_1377_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v___x_1380_; 
lean_dec_ref_known(v___x_1378_, 1);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1361_);
v___x_1380_ = v___x_1359_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_snd_1357_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
v_a_1351_ = v___x_1380_;
goto v___jp_1350_;
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_del_object(v___x_1359_);
lean_dec(v_snd_1357_);
lean_dec(v_a_1342_);
lean_dec(v_idx_1341_);
lean_dec(v_structName_1340_);
lean_dec(v_s_1339_);
v_a_1382_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1378_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1378_);
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
lean_object* v___x_1390_; lean_object* v___x_1392_; 
lean_dec(v_a_1342_);
lean_dec(v_idx_1341_);
lean_dec(v_structName_1340_);
lean_dec(v_s_1339_);
v___x_1390_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1390_);
v___x_1392_ = v___x_1359_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_snd_1357_);
v___x_1392_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
return v___x_1393_;
}
}
}
}
}
v___jp_1350_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = lean_unsigned_to_nat(1u);
v___x_1353_ = lean_nat_add(v_a_1342_, v___x_1352_);
lean_dec(v_a_1342_);
v_a_1342_ = v___x_1353_;
v_b_1343_ = v_a_1351_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___boxed(lean_object* v_upperBound_1397_, lean_object* v_s_1398_, lean_object* v_structName_1399_, lean_object* v_idx_1400_, lean_object* v_a_1401_, lean_object* v_b_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_1397_, v_s_1398_, v_structName_1399_, v_idx_1400_, v_a_1401_, v_b_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v_upperBound_1397_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(lean_object* v_upperBound_1410_, lean_object* v_s_1411_, lean_object* v_structName_1412_, lean_object* v_idx_1413_, lean_object* v_a_1414_, lean_object* v_b_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_a_1423_; uint8_t v___x_1427_; 
v___x_1427_ = lean_nat_dec_lt(v_a_1414_, v_upperBound_1410_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; 
lean_dec(v_idx_1413_);
lean_dec(v_structName_1412_);
lean_dec(v_s_1411_);
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v_b_1415_);
return v___x_1428_;
}
else
{
lean_object* v_snd_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1467_; 
v_snd_1429_ = lean_ctor_get(v_b_1415_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_b_1415_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; 
v_unused_1468_ = lean_ctor_get(v_b_1415_, 0);
lean_dec(v_unused_1468_);
v___x_1431_ = v_b_1415_;
v_isShared_1432_ = v_isSharedCheck_1467_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_snd_1429_);
lean_dec(v_b_1415_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1467_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_box(0);
if (lean_obj_tag(v_snd_1429_) == 7)
{
lean_object* v_body_1434_; uint8_t v___x_1435_; 
v_body_1434_ = lean_ctor_get(v_snd_1429_, 2);
lean_inc_ref(v_body_1434_);
lean_dec_ref_known(v_snd_1429_, 3);
v___x_1435_ = l_Lean_Expr_hasLooseBVars(v_body_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1437_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v_body_1434_);
lean_ctor_set(v___x_1431_, 0, v___x_1433_);
v___x_1437_ = v___x_1431_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_body_1434_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
v_a_1423_ = v___x_1437_;
goto v___jp_1422_;
}
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1439_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_1440_ = lean_expr_instantiate1(v_body_1434_, v___x_1439_);
lean_dec_ref(v_body_1434_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v___x_1440_);
lean_ctor_set(v___x_1431_, 0, v___x_1433_);
v___x_1442_ = v___x_1431_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
v_a_1423_ = v___x_1442_;
goto v___jp_1422_;
}
}
}
else
{
uint8_t v___x_1444_; 
v___x_1444_ = l_Lean_Expr_isErased(v_snd_1429_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1445_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
lean_inc(v_s_1411_);
v___x_1446_ = l_Lean_mkFVar(v_s_1411_);
lean_inc(v_idx_1413_);
lean_inc(v_structName_1412_);
v___x_1447_ = l_Lean_mkProj(v_structName_1412_, v_idx_1413_, v___x_1446_);
v___x_1448_ = l_Lean_indentExpr(v___x_1447_);
v___x_1449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1445_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_1449_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v___x_1452_; 
lean_dec_ref_known(v___x_1450_, 1);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1433_);
v___x_1452_ = v___x_1431_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_snd_1429_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
v_a_1423_ = v___x_1452_;
goto v___jp_1422_;
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_del_object(v___x_1431_);
lean_dec(v_snd_1429_);
lean_dec(v_idx_1413_);
lean_dec(v_structName_1412_);
lean_dec(v_s_1411_);
v_a_1454_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1450_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1450_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1464_; 
lean_dec(v_idx_1413_);
lean_dec(v_structName_1412_);
lean_dec(v_s_1411_);
v___x_1462_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1462_);
v___x_1464_ = v___x_1431_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_snd_1429_);
v___x_1464_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
return v___x_1465_;
}
}
}
}
}
v___jp_1422_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1424_ = lean_unsigned_to_nat(1u);
v___x_1425_ = lean_nat_add(v_a_1414_, v___x_1424_);
v___x_1426_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_1410_, v_s_1411_, v_structName_1412_, v_idx_1413_, v___x_1425_, v_a_1423_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
return v___x_1426_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg___boxed(lean_object* v_upperBound_1469_, lean_object* v_s_1470_, lean_object* v_structName_1471_, lean_object* v_idx_1472_, lean_object* v_a_1473_, lean_object* v_b_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_upperBound_1469_, v_s_1470_, v_structName_1471_, v_idx_1472_, v_a_1473_, v_b_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v_a_1473_);
lean_dec(v_upperBound_1469_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_ref_1482_, lean_object* v_msg_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_toCold_1490_; lean_object* v_options_1491_; lean_object* v_currRecDepth_1492_; lean_object* v_maxRecDepth_1493_; lean_object* v_ref_1494_; lean_object* v_currNamespace_1495_; lean_object* v_openDecls_1496_; lean_object* v_initHeartbeats_1497_; lean_object* v_maxHeartbeats_1498_; lean_object* v_currMacroScope_1499_; uint8_t v_diag_1500_; uint8_t v_suppressElabErrors_1501_; lean_object* v_ref_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v_toCold_1490_ = lean_ctor_get(v___y_1487_, 0);
v_options_1491_ = lean_ctor_get(v___y_1487_, 1);
v_currRecDepth_1492_ = lean_ctor_get(v___y_1487_, 2);
v_maxRecDepth_1493_ = lean_ctor_get(v___y_1487_, 3);
v_ref_1494_ = lean_ctor_get(v___y_1487_, 4);
v_currNamespace_1495_ = lean_ctor_get(v___y_1487_, 5);
v_openDecls_1496_ = lean_ctor_get(v___y_1487_, 6);
v_initHeartbeats_1497_ = lean_ctor_get(v___y_1487_, 7);
v_maxHeartbeats_1498_ = lean_ctor_get(v___y_1487_, 8);
v_currMacroScope_1499_ = lean_ctor_get(v___y_1487_, 9);
v_diag_1500_ = lean_ctor_get_uint8(v___y_1487_, sizeof(void*)*10);
v_suppressElabErrors_1501_ = lean_ctor_get_uint8(v___y_1487_, sizeof(void*)*10 + 1);
v_ref_1502_ = l_Lean_replaceRef(v_ref_1482_, v_ref_1494_);
lean_inc(v_currMacroScope_1499_);
lean_inc(v_maxHeartbeats_1498_);
lean_inc(v_initHeartbeats_1497_);
lean_inc(v_openDecls_1496_);
lean_inc(v_currNamespace_1495_);
lean_inc(v_maxRecDepth_1493_);
lean_inc(v_currRecDepth_1492_);
lean_inc_ref(v_options_1491_);
lean_inc_ref(v_toCold_1490_);
v___x_1503_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1503_, 0, v_toCold_1490_);
lean_ctor_set(v___x_1503_, 1, v_options_1491_);
lean_ctor_set(v___x_1503_, 2, v_currRecDepth_1492_);
lean_ctor_set(v___x_1503_, 3, v_maxRecDepth_1493_);
lean_ctor_set(v___x_1503_, 4, v_ref_1502_);
lean_ctor_set(v___x_1503_, 5, v_currNamespace_1495_);
lean_ctor_set(v___x_1503_, 6, v_openDecls_1496_);
lean_ctor_set(v___x_1503_, 7, v_initHeartbeats_1497_);
lean_ctor_set(v___x_1503_, 8, v_maxHeartbeats_1498_);
lean_ctor_set(v___x_1503_, 9, v_currMacroScope_1499_);
lean_ctor_set_uint8(v___x_1503_, sizeof(void*)*10, v_diag_1500_);
lean_ctor_set_uint8(v___x_1503_, sizeof(void*)*10 + 1, v_suppressElabErrors_1501_);
v___x_1504_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v_msg_1483_, v___y_1485_, v___y_1486_, v___x_1503_, v___y_1488_);
lean_dec_ref_known(v___x_1503_, 10);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_ref_1505_, lean_object* v_msg_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_1505_, v_msg_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v_ref_1505_);
return v_res_1513_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1514_ = lean_box(1);
v___x_1515_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3);
v___x_1516_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1);
v___x_1517_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
lean_ctor_set(v___x_1517_, 1, v___x_1515_);
lean_ctor_set(v___x_1517_, 2, v___x_1514_);
return v___x_1517_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__1));
v___x_1520_ = l_Lean_stringToMessageData(v___x_1519_);
return v___x_1520_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__3));
v___x_1523_ = l_Lean_stringToMessageData(v___x_1522_);
return v___x_1523_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6(void){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__5));
v___x_1526_ = l_Lean_stringToMessageData(v___x_1525_);
return v___x_1526_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__7));
v___x_1529_ = l_Lean_stringToMessageData(v___x_1528_);
return v___x_1529_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__9));
v___x_1532_ = l_Lean_stringToMessageData(v___x_1531_);
return v___x_1532_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__11));
v___x_1535_ = l_Lean_stringToMessageData(v___x_1534_);
return v___x_1535_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__13));
v___x_1538_ = l_Lean_stringToMessageData(v___x_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(lean_object* v_msg_1539_, lean_object* v_declHint_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1543_; lean_object* v_env_1544_; uint8_t v___x_1545_; 
v___x_1543_ = lean_st_ref_get(v___y_1541_);
v_env_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc_ref(v_env_1544_);
lean_dec(v___x_1543_);
v___x_1545_ = l_Lean_Name_isAnonymous(v_declHint_1540_);
if (v___x_1545_ == 0)
{
uint8_t v_isExporting_1546_; 
v_isExporting_1546_ = lean_ctor_get_uint8(v_env_1544_, sizeof(void*)*8);
if (v_isExporting_1546_ == 0)
{
lean_object* v___x_1547_; 
lean_dec_ref(v_env_1544_);
lean_dec(v_declHint_1540_);
v___x_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1547_, 0, v_msg_1539_);
return v___x_1547_;
}
else
{
lean_object* v___x_1548_; uint8_t v___x_1549_; 
lean_inc_ref(v_env_1544_);
v___x_1548_ = l_Lean_Environment_setExporting(v_env_1544_, v___x_1545_);
lean_inc(v_declHint_1540_);
lean_inc_ref(v___x_1548_);
v___x_1549_ = l_Lean_Environment_contains(v___x_1548_, v_declHint_1540_, v_isExporting_1546_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; 
lean_dec_ref(v___x_1548_);
lean_dec_ref(v_env_1544_);
lean_dec(v_declHint_1540_);
v___x_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1550_, 0, v_msg_1539_);
return v___x_1550_;
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v_c_1556_; lean_object* v___x_1557_; 
v___x_1551_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2);
v___x_1552_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0);
v___x_1553_ = l_Lean_Options_empty;
v___x_1554_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1548_);
lean_ctor_set(v___x_1554_, 1, v___x_1551_);
lean_ctor_set(v___x_1554_, 2, v___x_1552_);
lean_ctor_set(v___x_1554_, 3, v___x_1553_);
lean_inc(v_declHint_1540_);
v___x_1555_ = l_Lean_MessageData_ofConstName(v_declHint_1540_, v___x_1545_);
v_c_1556_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1556_, 0, v___x_1554_);
lean_ctor_set(v_c_1556_, 1, v___x_1555_);
v___x_1557_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1544_, v_declHint_1540_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_dec_ref(v_env_1544_);
lean_dec(v_declHint_1540_);
v___x_1558_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
lean_ctor_set(v___x_1559_, 1, v_c_1556_);
v___x_1560_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = l_Lean_MessageData_note(v___x_1561_);
v___x_1563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1563_, 0, v_msg_1539_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
return v___x_1564_;
}
else
{
lean_object* v_val_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1600_; 
v_val_1565_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1567_ = v___x_1557_;
v_isShared_1568_ = v_isSharedCheck_1600_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_val_1565_);
lean_dec(v___x_1557_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1600_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v_mod_1572_; uint8_t v___x_1573_; 
v___x_1569_ = lean_box(0);
v___x_1570_ = l_Lean_Environment_header(v_env_1544_);
lean_dec_ref(v_env_1544_);
v___x_1571_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1570_);
v_mod_1572_ = lean_array_get(v___x_1569_, v___x_1571_, v_val_1565_);
lean_dec(v_val_1565_);
lean_dec_ref(v___x_1571_);
v___x_1573_ = l_Lean_isPrivateName(v_declHint_1540_);
lean_dec(v_declHint_1540_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1574_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6);
v___x_1575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
lean_ctor_set(v___x_1575_, 1, v_c_1556_);
v___x_1576_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8);
v___x_1577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = l_Lean_MessageData_ofName(v_mod_1572_);
v___x_1579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1577_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10);
v___x_1581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = l_Lean_MessageData_note(v___x_1581_);
v___x_1583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1583_, 0, v_msg_1539_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set_tag(v___x_1567_, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1583_);
v___x_1585_ = v___x_1567_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1587_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2);
v___x_1588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
lean_ctor_set(v___x_1588_, 1, v_c_1556_);
v___x_1589_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12);
v___x_1590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = l_Lean_MessageData_ofName(v_mod_1572_);
v___x_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14);
v___x_1594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1592_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = l_Lean_MessageData_note(v___x_1594_);
v___x_1596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1596_, 0, v_msg_1539_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set_tag(v___x_1567_, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1596_);
v___x_1598_ = v___x_1567_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1601_; 
lean_dec_ref(v_env_1544_);
lean_dec(v_declHint_1540_);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v_msg_1539_);
return v___x_1601_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_msg_1602_, lean_object* v_declHint_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_1602_, v_declHint_1603_, v___y_1604_);
lean_dec(v___y_1604_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(lean_object* v_msg_1607_, lean_object* v_declHint_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v___x_1615_; lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1625_; 
v___x_1615_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_1607_, v_declHint_1608_, v___y_1613_);
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1625_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1625_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1620_ = l_Lean_unknownIdentifierMessageTag;
v___x_1621_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
lean_ctor_set(v___x_1621_, 1, v_a_1616_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1621_);
v___x_1623_ = v___x_1618_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_msg_1626_, lean_object* v_declHint_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(v_msg_1626_, v_declHint_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec_ref(v___y_1628_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1635_, lean_object* v_msg_1636_, lean_object* v_declHint_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v___x_1644_; lean_object* v_a_1645_; lean_object* v___x_1646_; 
v___x_1644_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(v_msg_1636_, v_declHint_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref(v___x_1644_);
v___x_1646_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_1635_, v_a_1645_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1647_, lean_object* v_msg_1648_, lean_object* v_declHint_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1647_, v_msg_1648_, v_declHint_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v_ref_1647_);
return v_res_1656_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__0));
v___x_1659_ = l_Lean_stringToMessageData(v___x_1658_);
return v___x_1659_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__2));
v___x_1662_ = l_Lean_stringToMessageData(v___x_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(lean_object* v_ref_1663_, lean_object* v_constName_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v___x_1671_; uint8_t v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1671_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_1672_ = 0;
lean_inc(v_constName_1664_);
v___x_1673_ = l_Lean_MessageData_ofConstName(v_constName_1664_, v___x_1672_);
v___x_1674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1671_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3);
v___x_1676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1663_, v___x_1676_, v_constName_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1678_, lean_object* v_constName_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1678_, v_constName_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v_ref_1678_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(lean_object* v_constName_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_ref_1694_; lean_object* v___x_1695_; 
v_ref_1694_ = lean_ctor_get(v___y_1691_, 4);
v___x_1695_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1694_, v_constName_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_constName_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec_ref(v___y_1697_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(lean_object* v_constName_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v___x_1711_; lean_object* v_env_1712_; uint8_t v___x_1713_; lean_object* v___x_1714_; 
v___x_1711_ = lean_st_ref_get(v___y_1709_);
v_env_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc_ref(v_env_1712_);
lean_dec(v___x_1711_);
v___x_1713_ = 0;
lean_inc(v_constName_1704_);
v___x_1714_ = l_Lean_Environment_find_x3f(v_env_1712_, v_constName_1704_, v___x_1713_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
return v___x_1715_;
}
else
{
lean_object* v_val_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec(v_constName_1704_);
v_val_1716_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1714_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_val_1716_);
lean_dec(v___x_1714_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
lean_ctor_set_tag(v___x_1718_, 0);
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_val_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1___boxed(lean_object* v_constName_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(v_constName_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec_ref(v___y_1725_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(lean_object* v_structName_1732_, lean_object* v_idx_1733_, lean_object* v_s_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___x_1753_; 
lean_inc(v_s_1734_);
v___x_1753_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_s_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1849_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1756_ = v___x_1753_;
v_isShared_1757_ = v_isSharedCheck_1849_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1849_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = l_Lean_Expr_headBeta(v_a_1754_);
v___x_1759_ = l_Lean_Expr_isErased(v___x_1758_);
if (v___x_1759_ == 0)
{
uint8_t v___x_1760_; 
v___x_1760_ = l_Lean_Expr_isAny(v___x_1758_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; 
lean_del_object(v___x_1756_);
v___x_1761_ = l_Lean_Expr_getAppFn(v___x_1758_);
if (lean_obj_tag(v___x_1761_) == 4)
{
lean_object* v_declName_1762_; lean_object* v_us_1763_; lean_object* v___x_1764_; lean_object* v_env_1765_; lean_object* v___x_1766_; 
v_declName_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_declName_1762_);
v_us_1763_ = lean_ctor_get(v___x_1761_, 1);
lean_inc(v_us_1763_);
lean_dec_ref_known(v___x_1761_, 2);
v___x_1764_ = lean_st_ref_get(v_a_1739_);
v_env_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc_ref(v_env_1765_);
lean_dec(v___x_1764_);
v___x_1766_ = l_Lean_Environment_find_x3f(v_env_1765_, v_declName_1762_, v___x_1760_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_dec(v_us_1763_);
lean_dec_ref(v___x_1758_);
v___y_1742_ = v_a_1735_;
v___y_1743_ = v_a_1736_;
v___y_1744_ = v_a_1737_;
v___y_1745_ = v_a_1738_;
v___y_1746_ = v_a_1739_;
goto v___jp_1741_;
}
else
{
lean_object* v_val_1767_; 
v_val_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_val_1767_);
lean_dec_ref_known(v___x_1766_, 1);
if (lean_obj_tag(v_val_1767_) == 5)
{
lean_object* v_val_1768_; lean_object* v_ctors_1769_; 
v_val_1768_ = lean_ctor_get(v_val_1767_, 0);
lean_inc_ref(v_val_1768_);
lean_dec_ref_known(v_val_1767_, 1);
v_ctors_1769_ = lean_ctor_get(v_val_1768_, 4);
lean_inc(v_ctors_1769_);
if (lean_obj_tag(v_ctors_1769_) == 1)
{
lean_object* v_tail_1770_; 
v_tail_1770_ = lean_ctor_get(v_ctors_1769_, 1);
if (lean_obj_tag(v_tail_1770_) == 0)
{
lean_object* v_numParams_1771_; lean_object* v_numIndices_1772_; lean_object* v_head_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1839_; 
v_numParams_1771_ = lean_ctor_get(v_val_1768_, 1);
lean_inc(v_numParams_1771_);
v_numIndices_1772_ = lean_ctor_get(v_val_1768_, 2);
lean_inc(v_numIndices_1772_);
lean_dec_ref(v_val_1768_);
v_head_1773_ = lean_ctor_get(v_ctors_1769_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_ctors_1769_);
if (v_isSharedCheck_1839_ == 0)
{
lean_object* v_unused_1840_; 
v_unused_1840_ = lean_ctor_get(v_ctors_1769_, 1);
lean_dec(v_unused_1840_);
v___x_1775_ = v_ctors_1769_;
v_isShared_1776_ = v_isSharedCheck_1839_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_head_1773_);
lean_dec(v_ctors_1769_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1839_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(v_head_1773_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref_known(v___x_1777_, 1);
if (lean_obj_tag(v_a_1778_) == 6)
{
lean_object* v_val_1779_; lean_object* v_dummy_1780_; lean_object* v_nargs_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; 
v_val_1779_ = lean_ctor_get(v_a_1778_, 0);
lean_inc_ref(v_val_1779_);
lean_dec_ref_known(v_a_1778_, 1);
v_dummy_1780_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0);
v_nargs_1781_ = l_Lean_Expr_getAppNumArgs(v___x_1758_);
lean_inc(v_nargs_1781_);
v___x_1782_ = lean_mk_array(v_nargs_1781_, v_dummy_1780_);
v___x_1783_ = lean_unsigned_to_nat(1u);
v___x_1784_ = lean_nat_sub(v_nargs_1781_, v___x_1783_);
lean_dec(v_nargs_1781_);
v___x_1785_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1758_, v___x_1782_, v___x_1784_);
v___x_1786_ = lean_nat_add(v_numParams_1771_, v_numIndices_1772_);
lean_dec(v_numIndices_1772_);
v___x_1787_ = lean_array_get_size(v___x_1785_);
v___x_1788_ = lean_nat_dec_eq(v___x_1786_, v___x_1787_);
lean_dec(v___x_1786_);
if (v___x_1788_ == 0)
{
lean_dec_ref(v___x_1785_);
lean_dec_ref(v_val_1779_);
lean_del_object(v___x_1775_);
lean_dec(v_numParams_1771_);
lean_dec(v_us_1763_);
v___y_1742_ = v_a_1735_;
v___y_1743_ = v_a_1736_;
v___y_1744_ = v_a_1737_;
v___y_1745_ = v_a_1738_;
v___y_1746_ = v_a_1739_;
goto v___jp_1741_;
}
else
{
if (v___x_1760_ == 0)
{
lean_object* v_toConstantVal_1789_; lean_object* v_name_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v_toConstantVal_1789_ = lean_ctor_get(v_val_1779_, 0);
lean_inc_ref(v_toConstantVal_1789_);
lean_dec_ref(v_val_1779_);
v_name_1790_ = lean_ctor_get(v_toConstantVal_1789_, 0);
lean_inc(v_name_1790_);
lean_dec_ref(v_toConstantVal_1789_);
v___x_1791_ = l_Lean_mkConst(v_name_1790_, v_us_1763_);
v___x_1792_ = lean_unsigned_to_nat(0u);
v___x_1793_ = l_Array_toSubarray___redArg(v___x_1785_, v___x_1792_, v_numParams_1771_);
v___x_1794_ = l_Subarray_copy___redArg(v___x_1793_);
v___x_1795_ = l_Lean_mkAppN(v___x_1791_, v___x_1794_);
lean_dec_ref(v___x_1794_);
v___x_1796_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(v___x_1795_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1798_; lean_object* v___x_1800_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v___x_1798_ = lean_box(0);
if (v_isShared_1776_ == 0)
{
lean_ctor_set_tag(v___x_1775_, 0);
lean_ctor_set(v___x_1775_, 1, v_a_1797_);
lean_ctor_set(v___x_1775_, 0, v___x_1798_);
v___x_1800_ = v___x_1775_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1798_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_a_1797_);
v___x_1800_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1801_; 
lean_inc(v_structName_1732_);
lean_inc(v_s_1734_);
lean_inc(v_idx_1733_);
v___x_1801_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_idx_1733_, v_s_1734_, v_structName_1732_, v_idx_1733_, v___x_1792_, v___x_1800_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1821_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1821_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1821_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v_fst_1806_; 
v_fst_1806_ = lean_ctor_get(v_a_1802_, 0);
if (lean_obj_tag(v_fst_1806_) == 0)
{
lean_object* v_snd_1807_; 
v_snd_1807_ = lean_ctor_get(v_a_1802_, 1);
lean_inc(v_snd_1807_);
lean_dec(v_a_1802_);
if (lean_obj_tag(v_snd_1807_) == 7)
{
lean_object* v_binderType_1808_; lean_object* v___x_1810_; 
lean_dec(v_s_1734_);
lean_dec(v_idx_1733_);
lean_dec(v_structName_1732_);
v_binderType_1808_ = lean_ctor_get(v_snd_1807_, 1);
lean_inc_ref(v_binderType_1808_);
lean_dec_ref_known(v_snd_1807_, 3);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v_binderType_1808_);
v___x_1810_ = v___x_1804_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_binderType_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
else
{
uint8_t v___x_1812_; 
v___x_1812_ = l_Lean_Expr_isErased(v_snd_1807_);
lean_dec(v_snd_1807_);
if (v___x_1812_ == 0)
{
lean_del_object(v___x_1804_);
v___y_1742_ = v_a_1735_;
v___y_1743_ = v_a_1736_;
v___y_1744_ = v_a_1737_;
v___y_1745_ = v_a_1738_;
v___y_1746_ = v_a_1739_;
goto v___jp_1741_;
}
else
{
lean_object* v___x_1813_; lean_object* v___x_1815_; 
lean_dec(v_s_1734_);
lean_dec(v_idx_1733_);
lean_dec(v_structName_1732_);
v___x_1813_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1813_);
v___x_1815_ = v___x_1804_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
else
{
lean_object* v_val_1817_; lean_object* v___x_1819_; 
lean_inc_ref(v_fst_1806_);
lean_dec(v_a_1802_);
lean_dec(v_s_1734_);
lean_dec(v_idx_1733_);
lean_dec(v_structName_1732_);
v_val_1817_ = lean_ctor_get(v_fst_1806_, 0);
lean_inc(v_val_1817_);
lean_dec_ref_known(v_fst_1806_, 1);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v_val_1817_);
v___x_1819_ = v___x_1804_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_val_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
lean_dec(v_s_1734_);
lean_dec(v_idx_1733_);
lean_dec(v_structName_1732_);
v_a_1822_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1801_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1801_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
}
else
{
lean_del_object(v___x_1775_);
lean_dec(v_s_1734_);
lean_dec(v_idx_1733_);
lean_dec(v_structName_1732_);
return v___x_1796_;
}
}
else
{
lean_dec_ref(v___x_1785_);
lean_dec_ref(v_val_1779_);
lean_del_object(v___x_1775_);
lean_dec(v_numParams_1771_);
lean_dec(v_us_1763_);
v___y_1742_ = v_a_1735_;
v___y_1743_ = v_a_1736_;
v___y_1744_ = v_a_1737_;
v___y_1745_ = v_a_1738_;
v___y_1746_ = v_a_1739_;
goto v___jp_1741_;
}
}
}
else
{
lean_dec(v_a_1778_);
lean_del_object(v___x_1775_);
lean_dec(v_numIndices_1772_);
lean_dec(v_numParams_1771_);
lean_dec(v_us_1763_);
lean_dec_ref(v___x_1758_);
v___y_1742_ = v_a_1735_;
v___y_1743_ = v_a_1736_;
v___y_1744_ = v_a_1737_;
v___y_1745_ = v_a_1738_;
v___y_1746_ = v_a_1739_;
goto v___jp_1741_;
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
lean_del_object(v___x_1775_);
lean_dec(v_numIndices_1772_);
lean_dec(v_numParams_1771_);
lean_dec(v_us_1763_);
lean_dec_ref(v___x_1758_);
lean_dec(v_s_1734_);
lean_dec(v_idx_1733_);
lean_dec(v_structName_1732_);
v_a_1831_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1777_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1777_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1769_, 2);
lean_dec_ref(v_val_1768_);
lean_dec(v_us_1763_);
lean_dec_ref(v___x_1758_);
v___y_1742_ = v_a_1735_;
v___y_1743_ = v_a_1736_;
v___y_1744_ = v_a_1737_;
v___y_1745_ = v_a_1738_;
v___y_1746_ = v_a_1739_;
goto v___jp_1741_;
}
}
else
{
lean_dec(v_ctors_1769_);
lean_dec_ref(v_val_1768_);
lean_dec(v_us_1763_);
lean_dec_ref(v___x_1758_);
v___y_1742_ = v_a_1735_;
v___y_1743_ = v_a_1736_;
v___y_1744_ = v_a_1737_;
v___y_1745_ = v_a_1738_;
v___y_1746_ = v_a_1739_;
goto v___jp_1741_;
}
}
else
{
lean_dec(v_val_1767_);
lean_dec(v_us_1763_);
lean_dec_ref(v___x_1758_);
v___y_1742_ = v_a_1735_;
v___y_1743_ = v_a_1736_;
v___y_1744_ = v_a_1737_;
v___y_1745_ = v_a_1738_;
v___y_1746_ = v_a_1739_;
goto v___jp_1741_;
}
}
}
else
{
lean_dec_ref(v___x_1761_);
lean_dec_ref(v___x_1758_);
v___y_1742_ = v_a_1735_;
v___y_1743_ = v_a_1736_;
v___y_1744_ = v_a_1737_;
v___y_1745_ = v_a_1738_;
v___y_1746_ = v_a_1739_;
goto v___jp_1741_;
}
}
else
{
lean_object* v___x_1841_; lean_object* v___x_1843_; 
lean_dec_ref(v___x_1758_);
lean_dec(v_s_1734_);
lean_dec(v_idx_1733_);
lean_dec(v_structName_1732_);
v___x_1841_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1841_);
v___x_1843_ = v___x_1756_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1847_; 
lean_dec_ref(v___x_1758_);
lean_dec(v_s_1734_);
lean_dec(v_idx_1733_);
lean_dec(v_structName_1732_);
v___x_1845_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1845_);
v___x_1847_ = v___x_1756_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
else
{
lean_dec(v_s_1734_);
lean_dec(v_idx_1733_);
lean_dec(v_structName_1732_);
return v___x_1753_;
}
v___jp_1741_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1747_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
v___x_1748_ = l_Lean_mkFVar(v_s_1734_);
v___x_1749_ = l_Lean_mkProj(v_structName_1732_, v_idx_1733_, v___x_1748_);
v___x_1750_ = l_Lean_indentExpr(v___x_1749_);
v___x_1751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1747_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
v___x_1752_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_1751_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
return v___x_1752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferProjType___boxed(lean_object* v_structName_1850_, lean_object* v_idx_1851_, lean_object* v_s_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(v_structName_1850_, v_idx_1851_, v_s_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec_ref(v_a_1853_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2(lean_object* v_upperBound_1860_, lean_object* v_s_1861_, lean_object* v_structName_1862_, lean_object* v_idx_1863_, lean_object* v_inst_1864_, lean_object* v_R_1865_, lean_object* v_a_1866_, lean_object* v_b_1867_, lean_object* v_c_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_upperBound_1860_, v_s_1861_, v_structName_1862_, v_idx_1863_, v_a_1866_, v_b_1867_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___boxed(lean_object* v_upperBound_1876_, lean_object* v_s_1877_, lean_object* v_structName_1878_, lean_object* v_idx_1879_, lean_object* v_inst_1880_, lean_object* v_R_1881_, lean_object* v_a_1882_, lean_object* v_b_1883_, lean_object* v_c_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2(v_upperBound_1876_, v_s_1877_, v_structName_1878_, v_idx_1879_, v_inst_1880_, v_R_1881_, v_a_1882_, v_b_1883_, v_c_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v_a_1882_);
lean_dec(v_upperBound_1876_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1(lean_object* v_00_u03b1_1892_, lean_object* v_constName_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___boxed(lean_object* v_00_u03b1_1901_, lean_object* v_constName_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1(v_00_u03b1_1901_, v_constName_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec_ref(v___y_1903_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3(lean_object* v_upperBound_1910_, lean_object* v_s_1911_, lean_object* v_structName_1912_, lean_object* v_idx_1913_, lean_object* v_inst_1914_, lean_object* v_R_1915_, lean_object* v_a_1916_, lean_object* v_b_1917_, lean_object* v_c_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_1910_, v_s_1911_, v_structName_1912_, v_idx_1913_, v_a_1916_, v_b_1917_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___boxed(lean_object* v_upperBound_1926_, lean_object* v_s_1927_, lean_object* v_structName_1928_, lean_object* v_idx_1929_, lean_object* v_inst_1930_, lean_object* v_R_1931_, lean_object* v_a_1932_, lean_object* v_b_1933_, lean_object* v_c_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3(v_upperBound_1926_, v_s_1927_, v_structName_1928_, v_idx_1929_, v_inst_1930_, v_R_1931_, v_a_1932_, v_b_1933_, v_c_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v_upperBound_1926_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_1942_, lean_object* v_ref_1943_, lean_object* v_constName_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1943_, v_constName_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1952_, lean_object* v_ref_1953_, lean_object* v_constName_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2(v_00_u03b1_1952_, v_ref_1953_, v_constName_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v_ref_1953_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1962_, lean_object* v_ref_1963_, lean_object* v_msg_1964_, lean_object* v_declHint_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1963_, v_msg_1964_, v_declHint_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1973_, lean_object* v_ref_1974_, lean_object* v_msg_1975_, lean_object* v_declHint_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4(v_00_u03b1_1973_, v_ref_1974_, v_msg_1975_, v_declHint_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v_ref_1974_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msg_1984_, lean_object* v_declHint_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_1984_, v_declHint_1985_, v___y_1990_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_1993_, lean_object* v_declHint_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_1993_, v_declHint_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec_ref(v___y_1995_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b1_2002_, lean_object* v_ref_2003_, lean_object* v_msg_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_2003_, v_msg_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b1_2012_, lean_object* v_ref_2013_, lean_object* v_msg_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7(v_00_u03b1_2012_, v_ref_2013_, v_msg_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v_ref_2013_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(lean_object* v_e_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_){
_start:
{
switch(lean_obj_tag(v_e_2022_))
{
case 0:
{
lean_object* v_value_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2037_; 
v_value_2029_ = lean_ctor_get(v_e_2022_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_e_2022_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2031_ = v_e_2022_;
v_isShared_2032_ = v_isSharedCheck_2037_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_value_2029_);
lean_dec(v_e_2022_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2037_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2033_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType(v_value_2029_);
lean_dec_ref(v_value_2029_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v___x_2033_);
v___x_2035_ = v___x_2031_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
case 1:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
return v___x_2039_;
}
case 2:
{
lean_object* v_typeName_2040_; lean_object* v_idx_2041_; lean_object* v_struct_2042_; lean_object* v___x_2043_; 
v_typeName_2040_ = lean_ctor_get(v_e_2022_, 0);
lean_inc(v_typeName_2040_);
v_idx_2041_ = lean_ctor_get(v_e_2022_, 1);
lean_inc(v_idx_2041_);
v_struct_2042_ = lean_ctor_get(v_e_2022_, 2);
lean_inc(v_struct_2042_);
lean_dec_ref_known(v_e_2022_, 3);
v___x_2043_ = l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(v_typeName_2040_, v_idx_2041_, v_struct_2042_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_);
return v___x_2043_;
}
case 3:
{
lean_object* v_declName_2044_; lean_object* v_us_2045_; lean_object* v_args_2046_; lean_object* v___x_2047_; 
v_declName_2044_ = lean_ctor_get(v_e_2022_, 0);
lean_inc(v_declName_2044_);
v_us_2045_ = lean_ctor_get(v_e_2022_, 1);
lean_inc(v_us_2045_);
v_args_2046_ = lean_ctor_get(v_e_2022_, 2);
lean_inc_ref(v_args_2046_);
lean_dec_ref_known(v_e_2022_, 3);
v___x_2047_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(v_declName_2044_, v_us_2045_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2049_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2047_, 1);
v___x_2049_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2048_, v_args_2046_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_);
return v___x_2049_;
}
else
{
lean_dec_ref(v_args_2046_);
return v___x_2047_;
}
}
default: 
{
lean_object* v_fvarId_2050_; lean_object* v_args_2051_; lean_object* v___x_2052_; 
v_fvarId_2050_ = lean_ctor_get(v_e_2022_, 0);
lean_inc(v_fvarId_2050_);
v_args_2051_ = lean_ctor_get(v_e_2022_, 1);
lean_inc_ref(v_args_2051_);
lean_dec_ref_known(v_e_2022_, 2);
v___x_2052_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_fvarId_2050_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2054_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref_known(v___x_2052_, 1);
v___x_2054_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2053_, v_args_2051_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_);
return v___x_2054_;
}
else
{
lean_dec_ref(v_args_2051_);
return v___x_2052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType___boxed(lean_object* v_e_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(v_e_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_);
lean_dec(v_a_2060_);
lean_dec_ref(v_a_2059_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
lean_dec_ref(v_a_2056_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType(lean_object* v_e_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2069_ = lean_unsigned_to_nat(32u);
v___x_2070_ = lean_mk_empty_array_with_capacity(v___x_2069_);
lean_dec_ref(v___x_2070_);
v___x_2071_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2072_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_e_2063_, v___x_2071_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType___boxed(lean_object* v_e_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Lean_Compiler_LCNF_inferType(v_e_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(lean_object* v_msg_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v___x_2086_; lean_object* v_toApplicative_2087_; lean_object* v_toFunctor_2088_; lean_object* v_toSeq_2089_; lean_object* v_toSeqLeft_2090_; lean_object* v_toSeqRight_2091_; lean_object* v___f_2092_; lean_object* v___f_2093_; lean_object* v___f_2094_; lean_object* v___f_2095_; lean_object* v___x_2096_; lean_object* v___f_2097_; lean_object* v___f_2098_; lean_object* v___f_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___f_2105_; lean_object* v___x_208__overap_2106_; lean_object* v___x_2107_; 
v___x_2086_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_2087_ = lean_ctor_get(v___x_2086_, 0);
v_toFunctor_2088_ = lean_ctor_get(v_toApplicative_2087_, 0);
v_toSeq_2089_ = lean_ctor_get(v_toApplicative_2087_, 2);
v_toSeqLeft_2090_ = lean_ctor_get(v_toApplicative_2087_, 3);
v_toSeqRight_2091_ = lean_ctor_get(v_toApplicative_2087_, 4);
v___f_2092_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_2093_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2088_, 2);
v___f_2094_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2094_, 0, v_toFunctor_2088_);
v___f_2095_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2095_, 0, v_toFunctor_2088_);
v___x_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___f_2094_);
lean_ctor_set(v___x_2096_, 1, v___f_2095_);
lean_inc(v_toSeqRight_2091_);
v___f_2097_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2097_, 0, v_toSeqRight_2091_);
lean_inc(v_toSeqLeft_2090_);
v___f_2098_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2098_, 0, v_toSeqLeft_2090_);
lean_inc(v_toSeq_2089_);
v___f_2099_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2099_, 0, v_toSeq_2089_);
v___x_2100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2096_);
lean_ctor_set(v___x_2100_, 1, v___f_2092_);
lean_ctor_set(v___x_2100_, 2, v___f_2099_);
lean_ctor_set(v___x_2100_, 3, v___f_2098_);
lean_ctor_set(v___x_2100_, 4, v___f_2097_);
v___x_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
lean_ctor_set(v___x_2101_, 1, v___f_2093_);
v___x_2102_ = l_StateRefT_x27_instMonad___redArg(v___x_2101_);
v___x_2103_ = l_Lean_instInhabitedExpr;
v___x_2104_ = l_instInhabitedOfMonad___redArg(v___x_2102_, v___x_2103_);
v___f_2105_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2105_, 0, v___x_2104_);
v___x_208__overap_2106_ = lean_panic_fn_borrowed(v___f_2105_, v_msg_2080_);
lean_dec_ref(v___f_2105_);
lean_inc(v___y_2084_);
lean_inc_ref(v___y_2083_);
lean_inc(v___y_2082_);
lean_inc_ref(v___y_2081_);
v___x_2107_ = lean_apply_5(v___x_208__overap_2106_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, lean_box(0));
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0___boxed(lean_object* v_msg_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v_msg_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
return v_res_2114_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inferAppType___closed__2(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2117_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2118_ = lean_unsigned_to_nat(15u);
v___x_2119_ = lean_unsigned_to_nat(258u);
v___x_2120_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__0));
v___x_2121_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2122_ = l_mkPanicMessageWithDecl(v___x_2121_, v___x_2120_, v___x_2119_, v___x_2118_, v___x_2117_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType(uint8_t v_pu_2123_, lean_object* v_fnType_2124_, lean_object* v_args_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
if (v_pu_2123_ == 0)
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2132_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_fnType_2124_, v_args_2125_, v___x_2131_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
return v___x_2132_;
}
else
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
lean_dec_ref(v_args_2125_);
lean_dec_ref(v_fnType_2124_);
v___x_2133_ = lean_obj_once(&l_Lean_Compiler_LCNF_inferAppType___closed__2, &l_Lean_Compiler_LCNF_inferAppType___closed__2_once, _init_l_Lean_Compiler_LCNF_inferAppType___closed__2);
v___x_2134_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2133_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
return v___x_2134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType___boxed(lean_object* v_pu_2135_, lean_object* v_fnType_2136_, lean_object* v_args_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_){
_start:
{
uint8_t v_pu_boxed_2143_; lean_object* v_res_2144_; 
v_pu_boxed_2143_ = lean_unbox(v_pu_2135_);
v_res_2144_ = l_Lean_Compiler_LCNF_inferAppType(v_pu_boxed_2143_, v_fnType_2136_, v_args_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
lean_dec(v_a_2139_);
lean_dec_ref(v_a_2138_);
return v_res_2144_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Arg_inferType___closed__1(void){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2146_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2147_ = lean_unsigned_to_nat(15u);
v___x_2148_ = lean_unsigned_to_nat(263u);
v___x_2149_ = ((lean_object*)(l_Lean_Compiler_LCNF_Arg_inferType___closed__0));
v___x_2150_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2151_ = l_mkPanicMessageWithDecl(v___x_2150_, v___x_2149_, v___x_2148_, v___x_2147_, v___x_2146_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType(uint8_t v_pu_2152_, lean_object* v_arg_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_){
_start:
{
if (v_pu_2152_ == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2160_ = l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(v_arg_2153_, v___x_2159_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_);
return v___x_2160_;
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
lean_dec(v_arg_2153_);
v___x_2161_ = lean_obj_once(&l_Lean_Compiler_LCNF_Arg_inferType___closed__1, &l_Lean_Compiler_LCNF_Arg_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_Arg_inferType___closed__1);
v___x_2162_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2161_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_);
return v___x_2162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType___boxed(lean_object* v_pu_2163_, lean_object* v_arg_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_){
_start:
{
uint8_t v_pu_boxed_2170_; lean_object* v_res_2171_; 
v_pu_boxed_2170_ = lean_unbox(v_pu_2163_);
v_res_2171_ = l_Lean_Compiler_LCNF_Arg_inferType(v_pu_boxed_2170_, v_arg_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
return v_res_2171_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LetValue_inferType___closed__1(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2173_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2174_ = lean_unsigned_to_nat(15u);
v___x_2175_ = lean_unsigned_to_nat(268u);
v___x_2176_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_inferType___closed__0));
v___x_2177_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2178_ = l_mkPanicMessageWithDecl(v___x_2177_, v___x_2176_, v___x_2175_, v___x_2174_, v___x_2173_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(uint8_t v_pu_2179_, lean_object* v_e_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_){
_start:
{
if (v_pu_2179_ == 0)
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2187_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(v_e_2180_, v___x_2186_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_);
return v___x_2187_;
}
else
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
lean_dec(v_e_2180_);
v___x_2188_ = lean_obj_once(&l_Lean_Compiler_LCNF_LetValue_inferType___closed__1, &l_Lean_Compiler_LCNF_LetValue_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_LetValue_inferType___closed__1);
v___x_2189_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2188_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_);
return v___x_2189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType___boxed(lean_object* v_pu_2190_, lean_object* v_e_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_){
_start:
{
uint8_t v_pu_boxed_2197_; lean_object* v_res_2198_; 
v_pu_boxed_2197_ = lean_unbox(v_pu_2190_);
v_res_2198_ = l_Lean_Compiler_LCNF_LetValue_inferType(v_pu_boxed_2197_, v_e_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_);
lean_dec(v_a_2195_);
lean_dec_ref(v_a_2194_);
lean_dec(v_a_2193_);
lean_dec_ref(v_a_2192_);
return v_res_2198_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_inferType___closed__1(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2200_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2201_ = lean_unsigned_to_nat(15u);
v___x_2202_ = lean_unsigned_to_nat(279u);
v___x_2203_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_inferType___closed__0));
v___x_2204_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2205_ = l_mkPanicMessageWithDecl(v___x_2204_, v___x_2203_, v___x_2202_, v___x_2201_, v___x_2200_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t v_pu_2206_, lean_object* v_code_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_){
_start:
{
if (v_pu_2206_ == 0)
{
switch(lean_obj_tag(v_code_2207_))
{
case 3:
{
lean_object* v_fvarId_2213_; lean_object* v_args_2214_; lean_object* v___x_2215_; 
v_fvarId_2213_ = lean_ctor_get(v_code_2207_, 0);
lean_inc(v_fvarId_2213_);
v_args_2214_ = lean_ctor_get(v_code_2207_, 1);
lean_inc_ref(v_args_2214_);
lean_dec_ref_known(v_code_2207_, 2);
v___x_2215_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2213_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2215_, 1);
v___x_2217_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2218_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2216_, v_args_2214_, v___x_2217_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_);
return v___x_2218_;
}
else
{
lean_dec_ref(v_args_2214_);
return v___x_2215_;
}
}
case 4:
{
lean_object* v_cases_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2227_; 
v_cases_2219_ = lean_ctor_get(v_code_2207_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_code_2207_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2221_ = v_code_2207_;
v_isShared_2222_ = v_isSharedCheck_2227_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_cases_2219_);
lean_dec(v_code_2207_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2227_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v_resultType_2223_; lean_object* v___x_2225_; 
v_resultType_2223_ = lean_ctor_get(v_cases_2219_, 1);
lean_inc_ref(v_resultType_2223_);
lean_dec_ref(v_cases_2219_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set_tag(v___x_2221_, 0);
lean_ctor_set(v___x_2221_, 0, v_resultType_2223_);
v___x_2225_ = v___x_2221_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_resultType_2223_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
case 5:
{
lean_object* v_fvarId_2228_; lean_object* v___x_2229_; 
v_fvarId_2228_ = lean_ctor_get(v_code_2207_, 0);
lean_inc(v_fvarId_2228_);
lean_dec_ref_known(v_code_2207_, 1);
v___x_2229_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2228_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_);
return v___x_2229_;
}
case 6:
{
lean_object* v_type_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
v_type_2230_ = lean_ctor_get(v_code_2207_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_code_2207_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v_code_2207_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_type_2230_);
lean_dec(v_code_2207_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
lean_ctor_set_tag(v___x_2232_, 0);
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_type_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
default: 
{
lean_object* v_k_2238_; 
v_k_2238_ = lean_ctor_get(v_code_2207_, 1);
lean_inc_ref(v_k_2238_);
lean_dec_ref(v_code_2207_);
v_code_2207_ = v_k_2238_;
goto _start;
}
}
}
else
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
lean_dec_ref(v_code_2207_);
v___x_2240_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_inferType___closed__1, &l_Lean_Compiler_LCNF_Code_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_Code_inferType___closed__1);
v___x_2241_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2240_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_);
return v___x_2241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType___boxed(lean_object* v_pu_2242_, lean_object* v_code_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_){
_start:
{
uint8_t v_pu_boxed_2249_; lean_object* v_res_2250_; 
v_pu_boxed_2249_ = lean_unbox(v_pu_2242_);
v_res_2250_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_boxed_2249_, v_code_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_);
lean_dec(v_a_2247_);
lean_dec_ref(v_a_2246_);
lean_dec(v_a_2245_);
lean_dec_ref(v_a_2244_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg(uint8_t v_pu_2251_, lean_object* v_code_2252_, lean_object* v_h__1_2253_, lean_object* v_h__2_2254_){
_start:
{
if (v_pu_2251_ == 0)
{
lean_object* v___x_2255_; 
lean_dec(v_h__2_2254_);
v___x_2255_ = lean_apply_1(v_h__1_2253_, v_code_2252_);
return v___x_2255_;
}
else
{
lean_object* v___x_2256_; 
lean_dec(v_h__1_2253_);
v___x_2256_ = lean_apply_1(v_h__2_2254_, v_code_2252_);
return v___x_2256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg___boxed(lean_object* v_pu_2257_, lean_object* v_code_2258_, lean_object* v_h__1_2259_, lean_object* v_h__2_2260_){
_start:
{
uint8_t v_pu_32__boxed_2261_; lean_object* v_res_2262_; 
v_pu_32__boxed_2261_ = lean_unbox(v_pu_2257_);
v_res_2262_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg(v_pu_32__boxed_2261_, v_code_2258_, v_h__1_2259_, v_h__2_2260_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter(lean_object* v_motive_2263_, uint8_t v_pu_2264_, lean_object* v_code_2265_, lean_object* v_h__1_2266_, lean_object* v_h__2_2267_){
_start:
{
if (v_pu_2264_ == 0)
{
lean_object* v___x_2268_; 
lean_dec(v_h__2_2267_);
v___x_2268_ = lean_apply_1(v_h__1_2266_, v_code_2265_);
return v___x_2268_;
}
else
{
lean_object* v___x_2269_; 
lean_dec(v_h__1_2266_);
v___x_2269_ = lean_apply_1(v_h__2_2267_, v_code_2265_);
return v___x_2269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___boxed(lean_object* v_motive_2270_, lean_object* v_pu_2271_, lean_object* v_code_2272_, lean_object* v_h__1_2273_, lean_object* v_h__2_2274_){
_start:
{
uint8_t v_pu_39__boxed_2275_; lean_object* v_res_2276_; 
v_pu_39__boxed_2275_ = lean_unbox(v_pu_2271_);
v_res_2276_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter(v_motive_2270_, v_pu_39__boxed_2275_, v_code_2272_, v_h__1_2273_, v_h__2_2274_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__1_splitter___redArg(lean_object* v_code_2277_, lean_object* v_h__1_2278_, lean_object* v_h__2_2279_, lean_object* v_h__3_2280_, lean_object* v_h__4_2281_, lean_object* v_h__5_2282_, lean_object* v_h__6_2283_, lean_object* v_h__7_2284_){
_start:
{
switch(lean_obj_tag(v_code_2277_))
{
case 0:
{
lean_object* v_decl_2285_; lean_object* v_k_2286_; lean_object* v___x_2287_; 
lean_dec(v_h__7_2284_);
lean_dec(v_h__6_2283_);
lean_dec(v_h__5_2282_);
lean_dec(v_h__4_2281_);
lean_dec(v_h__3_2280_);
lean_dec(v_h__2_2279_);
v_decl_2285_ = lean_ctor_get(v_code_2277_, 0);
lean_inc_ref(v_decl_2285_);
v_k_2286_ = lean_ctor_get(v_code_2277_, 1);
lean_inc_ref(v_k_2286_);
lean_dec_ref_known(v_code_2277_, 2);
v___x_2287_ = lean_apply_2(v_h__1_2278_, v_decl_2285_, v_k_2286_);
return v___x_2287_;
}
case 1:
{
lean_object* v_decl_2288_; lean_object* v_k_2289_; lean_object* v___x_2290_; 
lean_dec(v_h__7_2284_);
lean_dec(v_h__6_2283_);
lean_dec(v_h__5_2282_);
lean_dec(v_h__4_2281_);
lean_dec(v_h__3_2280_);
lean_dec(v_h__1_2278_);
v_decl_2288_ = lean_ctor_get(v_code_2277_, 0);
lean_inc_ref(v_decl_2288_);
v_k_2289_ = lean_ctor_get(v_code_2277_, 1);
lean_inc_ref(v_k_2289_);
lean_dec_ref_known(v_code_2277_, 2);
v___x_2290_ = lean_apply_3(v_h__2_2279_, v_decl_2288_, v_k_2289_, lean_box(0));
return v___x_2290_;
}
case 2:
{
lean_object* v_decl_2291_; lean_object* v_k_2292_; lean_object* v___x_2293_; 
lean_dec(v_h__7_2284_);
lean_dec(v_h__6_2283_);
lean_dec(v_h__5_2282_);
lean_dec(v_h__4_2281_);
lean_dec(v_h__2_2279_);
lean_dec(v_h__1_2278_);
v_decl_2291_ = lean_ctor_get(v_code_2277_, 0);
lean_inc_ref(v_decl_2291_);
v_k_2292_ = lean_ctor_get(v_code_2277_, 1);
lean_inc_ref(v_k_2292_);
lean_dec_ref_known(v_code_2277_, 2);
v___x_2293_ = lean_apply_2(v_h__3_2280_, v_decl_2291_, v_k_2292_);
return v___x_2293_;
}
case 3:
{
lean_object* v_fvarId_2294_; lean_object* v_args_2295_; lean_object* v___x_2296_; 
lean_dec(v_h__7_2284_);
lean_dec(v_h__6_2283_);
lean_dec(v_h__4_2281_);
lean_dec(v_h__3_2280_);
lean_dec(v_h__2_2279_);
lean_dec(v_h__1_2278_);
v_fvarId_2294_ = lean_ctor_get(v_code_2277_, 0);
lean_inc(v_fvarId_2294_);
v_args_2295_ = lean_ctor_get(v_code_2277_, 1);
lean_inc_ref(v_args_2295_);
lean_dec_ref_known(v_code_2277_, 2);
v___x_2296_ = lean_apply_2(v_h__5_2282_, v_fvarId_2294_, v_args_2295_);
return v___x_2296_;
}
case 4:
{
lean_object* v_cases_2297_; lean_object* v___x_2298_; 
lean_dec(v_h__6_2283_);
lean_dec(v_h__5_2282_);
lean_dec(v_h__4_2281_);
lean_dec(v_h__3_2280_);
lean_dec(v_h__2_2279_);
lean_dec(v_h__1_2278_);
v_cases_2297_ = lean_ctor_get(v_code_2277_, 0);
lean_inc_ref(v_cases_2297_);
lean_dec_ref_known(v_code_2277_, 1);
v___x_2298_ = lean_apply_1(v_h__7_2284_, v_cases_2297_);
return v___x_2298_;
}
case 5:
{
lean_object* v_fvarId_2299_; lean_object* v___x_2300_; 
lean_dec(v_h__7_2284_);
lean_dec(v_h__6_2283_);
lean_dec(v_h__5_2282_);
lean_dec(v_h__3_2280_);
lean_dec(v_h__2_2279_);
lean_dec(v_h__1_2278_);
v_fvarId_2299_ = lean_ctor_get(v_code_2277_, 0);
lean_inc(v_fvarId_2299_);
lean_dec_ref_known(v_code_2277_, 1);
v___x_2300_ = lean_apply_1(v_h__4_2281_, v_fvarId_2299_);
return v___x_2300_;
}
default: 
{
lean_object* v_type_2301_; lean_object* v___x_2302_; 
lean_dec(v_h__7_2284_);
lean_dec(v_h__5_2282_);
lean_dec(v_h__4_2281_);
lean_dec(v_h__3_2280_);
lean_dec(v_h__2_2279_);
lean_dec(v_h__1_2278_);
v_type_2301_ = lean_ctor_get(v_code_2277_, 0);
lean_inc_ref(v_type_2301_);
lean_dec_ref_known(v_code_2277_, 1);
v___x_2302_ = lean_apply_1(v_h__6_2283_, v_type_2301_);
return v___x_2302_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__1_splitter(lean_object* v_motive_2303_, lean_object* v_code_2304_, lean_object* v_h__1_2305_, lean_object* v_h__2_2306_, lean_object* v_h__3_2307_, lean_object* v_h__4_2308_, lean_object* v_h__5_2309_, lean_object* v_h__6_2310_, lean_object* v_h__7_2311_){
_start:
{
switch(lean_obj_tag(v_code_2304_))
{
case 0:
{
lean_object* v_decl_2312_; lean_object* v_k_2313_; lean_object* v___x_2314_; 
lean_dec(v_h__7_2311_);
lean_dec(v_h__6_2310_);
lean_dec(v_h__5_2309_);
lean_dec(v_h__4_2308_);
lean_dec(v_h__3_2307_);
lean_dec(v_h__2_2306_);
v_decl_2312_ = lean_ctor_get(v_code_2304_, 0);
lean_inc_ref(v_decl_2312_);
v_k_2313_ = lean_ctor_get(v_code_2304_, 1);
lean_inc_ref(v_k_2313_);
lean_dec_ref_known(v_code_2304_, 2);
v___x_2314_ = lean_apply_2(v_h__1_2305_, v_decl_2312_, v_k_2313_);
return v___x_2314_;
}
case 1:
{
lean_object* v_decl_2315_; lean_object* v_k_2316_; lean_object* v___x_2317_; 
lean_dec(v_h__7_2311_);
lean_dec(v_h__6_2310_);
lean_dec(v_h__5_2309_);
lean_dec(v_h__4_2308_);
lean_dec(v_h__3_2307_);
lean_dec(v_h__1_2305_);
v_decl_2315_ = lean_ctor_get(v_code_2304_, 0);
lean_inc_ref(v_decl_2315_);
v_k_2316_ = lean_ctor_get(v_code_2304_, 1);
lean_inc_ref(v_k_2316_);
lean_dec_ref_known(v_code_2304_, 2);
v___x_2317_ = lean_apply_3(v_h__2_2306_, v_decl_2315_, v_k_2316_, lean_box(0));
return v___x_2317_;
}
case 2:
{
lean_object* v_decl_2318_; lean_object* v_k_2319_; lean_object* v___x_2320_; 
lean_dec(v_h__7_2311_);
lean_dec(v_h__6_2310_);
lean_dec(v_h__5_2309_);
lean_dec(v_h__4_2308_);
lean_dec(v_h__2_2306_);
lean_dec(v_h__1_2305_);
v_decl_2318_ = lean_ctor_get(v_code_2304_, 0);
lean_inc_ref(v_decl_2318_);
v_k_2319_ = lean_ctor_get(v_code_2304_, 1);
lean_inc_ref(v_k_2319_);
lean_dec_ref_known(v_code_2304_, 2);
v___x_2320_ = lean_apply_2(v_h__3_2307_, v_decl_2318_, v_k_2319_);
return v___x_2320_;
}
case 3:
{
lean_object* v_fvarId_2321_; lean_object* v_args_2322_; lean_object* v___x_2323_; 
lean_dec(v_h__7_2311_);
lean_dec(v_h__6_2310_);
lean_dec(v_h__4_2308_);
lean_dec(v_h__3_2307_);
lean_dec(v_h__2_2306_);
lean_dec(v_h__1_2305_);
v_fvarId_2321_ = lean_ctor_get(v_code_2304_, 0);
lean_inc(v_fvarId_2321_);
v_args_2322_ = lean_ctor_get(v_code_2304_, 1);
lean_inc_ref(v_args_2322_);
lean_dec_ref_known(v_code_2304_, 2);
v___x_2323_ = lean_apply_2(v_h__5_2309_, v_fvarId_2321_, v_args_2322_);
return v___x_2323_;
}
case 4:
{
lean_object* v_cases_2324_; lean_object* v___x_2325_; 
lean_dec(v_h__6_2310_);
lean_dec(v_h__5_2309_);
lean_dec(v_h__4_2308_);
lean_dec(v_h__3_2307_);
lean_dec(v_h__2_2306_);
lean_dec(v_h__1_2305_);
v_cases_2324_ = lean_ctor_get(v_code_2304_, 0);
lean_inc_ref(v_cases_2324_);
lean_dec_ref_known(v_code_2304_, 1);
v___x_2325_ = lean_apply_1(v_h__7_2311_, v_cases_2324_);
return v___x_2325_;
}
case 5:
{
lean_object* v_fvarId_2326_; lean_object* v___x_2327_; 
lean_dec(v_h__7_2311_);
lean_dec(v_h__6_2310_);
lean_dec(v_h__5_2309_);
lean_dec(v_h__3_2307_);
lean_dec(v_h__2_2306_);
lean_dec(v_h__1_2305_);
v_fvarId_2326_ = lean_ctor_get(v_code_2304_, 0);
lean_inc(v_fvarId_2326_);
lean_dec_ref_known(v_code_2304_, 1);
v___x_2327_ = lean_apply_1(v_h__4_2308_, v_fvarId_2326_);
return v___x_2327_;
}
default: 
{
lean_object* v_type_2328_; lean_object* v___x_2329_; 
lean_dec(v_h__7_2311_);
lean_dec(v_h__5_2309_);
lean_dec(v_h__4_2308_);
lean_dec(v_h__3_2307_);
lean_dec(v_h__2_2306_);
lean_dec(v_h__1_2305_);
v_type_2328_ = lean_ctor_get(v_code_2304_, 0);
lean_inc_ref(v_type_2328_);
lean_dec_ref_known(v_code_2304_, 1);
v___x_2329_ = lean_apply_1(v_h__6_2310_, v_type_2328_);
return v___x_2329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(uint8_t v_pu_2330_, lean_object* v_params_2331_, lean_object* v_code_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2330_, v_code_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; size_t v_sz_2340_; size_t v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2338_, 1);
v_sz_2340_ = lean_array_size(v_params_2331_);
v___x_2341_ = ((size_t)0ULL);
v___x_2342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(v_sz_2340_, v___x_2341_, v_params_2331_);
v___x_2343_ = lean_unsigned_to_nat(32u);
v___x_2344_ = lean_mk_empty_array_with_capacity(v___x_2343_);
lean_dec_ref(v___x_2344_);
v___x_2345_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2346_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v___x_2342_, v_a_2339_, v___x_2345_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
lean_dec(v_a_2339_);
lean_dec_ref(v___x_2342_);
return v___x_2346_;
}
else
{
lean_dec_ref(v_params_2331_);
return v___x_2338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType___boxed(lean_object* v_pu_2347_, lean_object* v_params_2348_, lean_object* v_code_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
uint8_t v_pu_boxed_2355_; lean_object* v_res_2356_; 
v_pu_boxed_2355_ = lean_unbox(v_pu_2347_);
v_res_2356_ = l_Lean_Compiler_LCNF_Code_inferParamType(v_pu_boxed_2355_, v_params_2348_, v_code_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType(uint8_t v_pu_2357_, lean_object* v_alt_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_){
_start:
{
switch(lean_obj_tag(v_alt_2358_))
{
case 0:
{
lean_object* v_code_2364_; lean_object* v___x_2365_; 
v_code_2364_ = lean_ctor_get(v_alt_2358_, 2);
lean_inc_ref(v_code_2364_);
lean_dec_ref_known(v_alt_2358_, 3);
v___x_2365_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2357_, v_code_2364_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
return v___x_2365_;
}
case 1:
{
lean_object* v_code_2366_; lean_object* v___x_2367_; 
v_code_2366_ = lean_ctor_get(v_alt_2358_, 1);
lean_inc_ref(v_code_2366_);
lean_dec_ref_known(v_alt_2358_, 2);
v___x_2367_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2357_, v_code_2366_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
return v___x_2367_;
}
default: 
{
lean_object* v_code_2368_; lean_object* v___x_2369_; 
v_code_2368_ = lean_ctor_get(v_alt_2358_, 0);
lean_inc_ref(v_code_2368_);
lean_dec_ref_known(v_alt_2358_, 1);
v___x_2369_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2357_, v_code_2368_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
return v___x_2369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType___boxed(lean_object* v_pu_2370_, lean_object* v_alt_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
uint8_t v_pu_boxed_2377_; lean_object* v_res_2378_; 
v_pu_boxed_2377_ = lean_unbox(v_pu_2370_);
v_res_2378_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_boxed_2377_, v_alt_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t v_pu_2379_, lean_object* v_e_2380_, lean_object* v_prefixName_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v___x_2387_; 
v___x_2387_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_prefixName_2381_, v_a_2383_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2389_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2387_, 1);
lean_inc(v_e_2380_);
v___x_2389_ = l_Lean_Compiler_LCNF_LetValue_inferType(v_pu_2379_, v_e_2380_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v___x_2391_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2389_, 1);
v___x_2391_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2379_, v_a_2388_, v_a_2390_, v_e_2380_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
return v___x_2391_;
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
lean_dec(v_a_2388_);
lean_dec(v_e_2380_);
v_a_2392_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2389_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2389_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
lean_dec(v_e_2380_);
v_a_2400_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2387_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2387_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl___boxed(lean_object* v_pu_2408_, lean_object* v_e_2409_, lean_object* v_prefixName_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_){
_start:
{
uint8_t v_pu_boxed_2416_; lean_object* v_res_2417_; 
v_pu_boxed_2416_ = lean_unbox(v_pu_2408_);
v_res_2417_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v_pu_boxed_2416_, v_e_2409_, v_prefixName_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_);
lean_dec(v_a_2414_);
lean_dec_ref(v_a_2413_);
lean_dec(v_a_2412_);
lean_dec_ref(v_a_2411_);
return v_res_2417_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkForallParams___closed__1(void){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2419_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2420_ = lean_unsigned_to_nat(15u);
v___x_2421_ = lean_unsigned_to_nat(295u);
v___x_2422_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkForallParams___closed__0));
v___x_2423_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2424_ = l_mkPanicMessageWithDecl(v___x_2423_, v___x_2422_, v___x_2421_, v___x_2420_, v___x_2419_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams(uint8_t v_pu_2425_, lean_object* v_params_2426_, lean_object* v_type_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
if (v_pu_2425_ == 0)
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(v_params_2426_, v_type_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_);
return v___x_2433_;
}
else
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
lean_dec_ref(v_params_2426_);
v___x_2434_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkForallParams___closed__1, &l_Lean_Compiler_LCNF_mkForallParams___closed__1_once, _init_l_Lean_Compiler_LCNF_mkForallParams___closed__1);
v___x_2435_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2434_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_);
return v___x_2435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams___boxed(lean_object* v_pu_2436_, lean_object* v_params_2437_, lean_object* v_type_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_){
_start:
{
uint8_t v_pu_boxed_2444_; lean_object* v_res_2445_; 
v_pu_boxed_2444_ = lean_unbox(v_pu_2436_);
v_res_2445_ = l_Lean_Compiler_LCNF_mkForallParams(v_pu_boxed_2444_, v_params_2437_, v_type_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec_ref(v_type_2438_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(uint8_t v_pu_2446_, lean_object* v_params_2447_, lean_object* v_code_2448_, lean_object* v_prefixName_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_){
_start:
{
lean_object* v___x_2455_; 
lean_inc_ref(v_code_2448_);
v___x_2455_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2446_, v_code_2448_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2457_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___x_2455_, 1);
lean_inc_ref(v_params_2447_);
v___x_2457_ = l_Lean_Compiler_LCNF_mkForallParams(v_pu_2446_, v_params_2447_, v_a_2456_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
lean_dec(v_a_2456_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2459_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref_known(v___x_2457_, 1);
v___x_2459_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_prefixName_2449_, v_a_2451_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v___x_2461_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
lean_dec_ref_known(v___x_2459_, 1);
v___x_2461_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_2446_, v_a_2460_, v_a_2458_, v_params_2447_, v_code_2448_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
return v___x_2461_;
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec(v_a_2458_);
lean_dec_ref(v_code_2448_);
lean_dec_ref(v_params_2447_);
v_a_2462_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2459_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2459_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_dec(v_prefixName_2449_);
lean_dec_ref(v_code_2448_);
lean_dec_ref(v_params_2447_);
v_a_2470_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2457_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2457_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec(v_prefixName_2449_);
lean_dec_ref(v_code_2448_);
lean_dec_ref(v_params_2447_);
v_a_2478_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2455_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2455_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux___boxed(lean_object* v_pu_2486_, lean_object* v_params_2487_, lean_object* v_code_2488_, lean_object* v_prefixName_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_){
_start:
{
uint8_t v_pu_boxed_2495_; lean_object* v_res_2496_; 
v_pu_boxed_2495_ = lean_unbox(v_pu_2486_);
v_res_2496_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_boxed_2495_, v_params_2487_, v_code_2488_, v_prefixName_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object* v_params_2497_, lean_object* v_code_2498_, lean_object* v_prefixName_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_){
_start:
{
uint8_t v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = 0;
v___x_2506_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v___x_2505_, v_params_2497_, v_code_2498_, v_prefixName_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl___boxed(lean_object* v_params_2507_, lean_object* v_code_2508_, lean_object* v_prefixName_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v_params_2507_, v_code_2508_, v_prefixName_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_);
lean_dec(v_a_2513_);
lean_dec_ref(v_a_2512_);
lean_dec(v_a_2511_);
lean_dec_ref(v_a_2510_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(uint8_t v_pu_2516_, lean_object* v_params_2517_, lean_object* v_code_2518_, lean_object* v_prefixName_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_){
_start:
{
lean_object* v___x_2525_; 
v___x_2525_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_2516_, v_params_2517_, v_code_2518_, v_prefixName_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl___boxed(lean_object* v_pu_2526_, lean_object* v_params_2527_, lean_object* v_code_2528_, lean_object* v_prefixName_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_){
_start:
{
uint8_t v_pu_boxed_2535_; lean_object* v_res_2536_; 
v_pu_boxed_2535_ = lean_unbox(v_pu_2526_);
v_res_2536_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v_pu_boxed_2535_, v_params_2527_, v_code_2528_, v_prefixName_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(uint8_t v_pu_2537_, lean_object* v_param_2538_, lean_object* v_code_2539_, lean_object* v_prefixName_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v_params_2548_; lean_object* v___x_2549_; 
v___x_2546_ = lean_unsigned_to_nat(1u);
v___x_2547_ = lean_mk_empty_array_with_capacity(v___x_2546_);
v_params_2548_ = lean_array_push(v___x_2547_, v_param_2538_);
v___x_2549_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_2537_, v_params_2548_, v_code_2539_, v_prefixName_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___boxed(lean_object* v_pu_2550_, lean_object* v_param_2551_, lean_object* v_code_2552_, lean_object* v_prefixName_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_){
_start:
{
uint8_t v_pu_boxed_2559_; lean_object* v_res_2560_; 
v_pu_boxed_2559_ = lean_unbox(v_pu_2550_);
v_res_2560_ = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(v_pu_boxed_2559_, v_param_2551_, v_code_2552_, v_prefixName_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(lean_object* v_msg_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_options_2567_; lean_object* v_ref_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v_options_2567_ = lean_ctor_get(v___y_2564_, 1);
v_ref_2568_ = lean_ctor_get(v___y_2564_, 4);
v___x_2569_ = lean_st_ref_get(v___y_2565_);
v___x_2570_ = lean_st_ref_get(v___y_2563_);
v___x_2571_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_2562_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2594_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2574_ = v___x_2571_;
v_isShared_2575_ = v_isSharedCheck_2594_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2571_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2594_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v_env_2576_; lean_object* v_lctx_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2592_; 
v_env_2576_ = lean_ctor_get(v___x_2569_, 0);
lean_inc_ref(v_env_2576_);
lean_dec(v___x_2569_);
v_lctx_2577_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2592_ == 0)
{
lean_object* v_unused_2593_; 
v_unused_2593_ = lean_ctor_get(v___x_2570_, 1);
lean_dec(v_unused_2593_);
v___x_2579_ = v___x_2570_;
v_isShared_2580_ = v_isSharedCheck_2592_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_lctx_2577_);
lean_dec(v___x_2570_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2592_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
uint8_t v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2581_ = lean_unbox(v_a_2572_);
lean_dec(v_a_2572_);
v___x_2582_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2577_, v___x_2581_);
lean_dec_ref(v_lctx_2577_);
v___x_2583_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2);
lean_inc_ref(v_options_2567_);
v___x_2584_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2584_, 0, v_env_2576_);
lean_ctor_set(v___x_2584_, 1, v___x_2583_);
lean_ctor_set(v___x_2584_, 2, v___x_2582_);
lean_ctor_set(v___x_2584_, 3, v_options_2567_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set_tag(v___x_2579_, 3);
lean_ctor_set(v___x_2579_, 1, v_msg_2561_);
lean_ctor_set(v___x_2579_, 0, v___x_2584_);
v___x_2586_ = v___x_2579_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v_msg_2561_);
v___x_2586_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
lean_object* v___x_2587_; lean_object* v___x_2589_; 
lean_inc(v_ref_2568_);
v___x_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2587_, 0, v_ref_2568_);
lean_ctor_set(v___x_2587_, 1, v___x_2586_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set_tag(v___x_2574_, 1);
lean_ctor_set(v___x_2574_, 0, v___x_2587_);
v___x_2589_ = v___x_2574_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec(v___x_2570_);
lean_dec(v___x_2569_);
lean_dec_ref(v_msg_2561_);
v_a_2595_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2571_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2571_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg___boxed(lean_object* v_msg_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v_msg_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1(lean_object* v_00_u03b1_2610_, lean_object* v_msg_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v_msg_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___boxed(lean_object* v_00_u03b1_2618_, lean_object* v_msg_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1(v_00_u03b1_2618_, v_msg_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(uint8_t v_pu_2626_, lean_object* v_a_2627_, lean_object* v_b_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_array_2634_; lean_object* v_start_2635_; lean_object* v_stop_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2652_; 
v_array_2634_ = lean_ctor_get(v_a_2627_, 0);
v_start_2635_ = lean_ctor_get(v_a_2627_, 1);
v_stop_2636_ = lean_ctor_get(v_a_2627_, 2);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_a_2627_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2638_ = v_a_2627_;
v_isShared_2639_ = v_isSharedCheck_2652_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_stop_2636_);
lean_inc(v_start_2635_);
lean_inc(v_array_2634_);
lean_dec(v_a_2627_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2652_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
uint8_t v___x_2640_; 
v___x_2640_ = lean_nat_dec_lt(v_start_2635_, v_stop_2636_);
if (v___x_2640_ == 0)
{
lean_object* v___x_2641_; 
lean_del_object(v___x_2638_);
lean_dec(v_stop_2636_);
lean_dec(v_start_2635_);
lean_dec_ref(v_array_2634_);
v___x_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2641_, 0, v_b_2628_);
return v___x_2641_;
}
else
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = lean_array_fget_borrowed(v_array_2634_, v_start_2635_);
lean_inc(v___x_2642_);
v___x_2643_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_2626_, v___x_2642_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2648_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___x_2643_, 1);
v___x_2645_ = lean_unsigned_to_nat(1u);
v___x_2646_ = lean_nat_add(v_start_2635_, v___x_2645_);
lean_dec(v_start_2635_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 1, v___x_2646_);
v___x_2648_ = v___x_2638_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_array_2634_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v___x_2646_);
lean_ctor_set(v_reuseFailAlloc_2651_, 2, v_stop_2636_);
v___x_2648_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Lean_Compiler_LCNF_joinTypes(v_b_2628_, v_a_2644_);
v_a_2627_ = v___x_2648_;
v_b_2628_ = v___x_2649_;
goto _start;
}
}
else
{
lean_del_object(v___x_2638_);
lean_dec(v_stop_2636_);
lean_dec(v_start_2635_);
lean_dec_ref(v_array_2634_);
lean_dec_ref(v_b_2628_);
return v___x_2643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg___boxed(lean_object* v_pu_2653_, lean_object* v_a_2654_, lean_object* v_b_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
uint8_t v_pu_boxed_2661_; lean_object* v_res_2662_; 
v_pu_boxed_2661_ = lean_unbox(v_pu_2653_);
v_res_2662_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_boxed_2661_, v_a_2654_, v_b_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
return v_res_2662_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__1(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkCasesResultType___closed__0));
v___x_2665_ = l_Lean_stringToMessageData(v___x_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(uint8_t v_pu_2666_, lean_object* v_alts_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_){
_start:
{
lean_object* v___x_2673_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___x_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; 
v___x_2673_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v_pu_2666_);
v___x_2687_ = lean_array_get_size(v_alts_2667_);
v___x_2688_ = lean_unsigned_to_nat(0u);
v___x_2689_ = lean_nat_dec_eq(v___x_2687_, v___x_2688_);
if (v___x_2689_ == 0)
{
v___y_2675_ = v_a_2668_;
v___y_2676_ = v_a_2669_;
v___y_2677_ = v_a_2670_;
v___y_2678_ = v_a_2671_;
goto v___jp_2674_;
}
else
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_dec_ref(v___x_2673_);
lean_dec_ref(v_alts_2667_);
v___x_2690_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkCasesResultType___closed__1, &l_Lean_Compiler_LCNF_mkCasesResultType___closed__1_once, _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__1);
v___x_2691_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v___x_2690_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2691_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2691_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
v___jp_2674_:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2679_ = lean_unsigned_to_nat(0u);
v___x_2680_ = lean_array_get(v___x_2673_, v_alts_2667_, v___x_2679_);
lean_dec_ref(v___x_2673_);
v___x_2681_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_2666_, v___x_2680_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2682_);
lean_dec_ref_known(v___x_2681_, 1);
v___x_2683_ = lean_unsigned_to_nat(1u);
v___x_2684_ = lean_array_get_size(v_alts_2667_);
v___x_2685_ = l_Array_toSubarray___redArg(v_alts_2667_, v___x_2683_, v___x_2684_);
v___x_2686_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_2666_, v___x_2685_, v_a_2682_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
return v___x_2686_;
}
else
{
lean_dec_ref(v_alts_2667_);
return v___x_2681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___boxed(lean_object* v_pu_2700_, lean_object* v_alts_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_){
_start:
{
uint8_t v_pu_boxed_2707_; lean_object* v_res_2708_; 
v_pu_boxed_2707_ = lean_unbox(v_pu_2700_);
v_res_2708_ = l_Lean_Compiler_LCNF_mkCasesResultType(v_pu_boxed_2707_, v_alts_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
lean_dec(v_a_2705_);
lean_dec_ref(v_a_2704_);
lean_dec(v_a_2703_);
lean_dec_ref(v_a_2702_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0(uint8_t v_pu_2709_, lean_object* v_inst_2710_, lean_object* v_R_2711_, lean_object* v_a_2712_, lean_object* v_b_2713_, lean_object* v_c_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_2709_, v_a_2712_, v_b_2713_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___boxed(lean_object* v_pu_2721_, lean_object* v_inst_2722_, lean_object* v_R_2723_, lean_object* v_a_2724_, lean_object* v_b_2725_, lean_object* v_c_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
uint8_t v_pu_boxed_2732_; lean_object* v_res_2733_; 
v_pu_boxed_2732_ = lean_unbox(v_pu_2721_);
v_res_2733_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0(v_pu_boxed_2732_, v_inst_2722_, v_R_2723_, v_a_2724_, v_b_2725_, v_c_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(lean_object* v_msg_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v___x_2740_; lean_object* v_toApplicative_2741_; lean_object* v_toFunctor_2742_; lean_object* v_toSeq_2743_; lean_object* v_toSeqLeft_2744_; lean_object* v_toSeqRight_2745_; lean_object* v___f_2746_; lean_object* v___f_2747_; lean_object* v___f_2748_; lean_object* v___f_2749_; lean_object* v___x_2750_; lean_object* v___f_2751_; lean_object* v___f_2752_; lean_object* v___f_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; uint8_t v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___f_2760_; lean_object* v___x_970__overap_2761_; lean_object* v___x_2762_; 
v___x_2740_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_2741_ = lean_ctor_get(v___x_2740_, 0);
v_toFunctor_2742_ = lean_ctor_get(v_toApplicative_2741_, 0);
v_toSeq_2743_ = lean_ctor_get(v_toApplicative_2741_, 2);
v_toSeqLeft_2744_ = lean_ctor_get(v_toApplicative_2741_, 3);
v_toSeqRight_2745_ = lean_ctor_get(v_toApplicative_2741_, 4);
v___f_2746_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_2747_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2742_, 2);
v___f_2748_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2748_, 0, v_toFunctor_2742_);
v___f_2749_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2749_, 0, v_toFunctor_2742_);
v___x_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___f_2748_);
lean_ctor_set(v___x_2750_, 1, v___f_2749_);
lean_inc(v_toSeqRight_2745_);
v___f_2751_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2751_, 0, v_toSeqRight_2745_);
lean_inc(v_toSeqLeft_2744_);
v___f_2752_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2752_, 0, v_toSeqLeft_2744_);
lean_inc(v_toSeq_2743_);
v___f_2753_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2753_, 0, v_toSeq_2743_);
v___x_2754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2750_);
lean_ctor_set(v___x_2754_, 1, v___f_2746_);
lean_ctor_set(v___x_2754_, 2, v___f_2753_);
lean_ctor_set(v___x_2754_, 3, v___f_2752_);
lean_ctor_set(v___x_2754_, 4, v___f_2751_);
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2754_);
lean_ctor_set(v___x_2755_, 1, v___f_2747_);
v___x_2756_ = l_StateRefT_x27_instMonad___redArg(v___x_2755_);
v___x_2757_ = 0;
v___x_2758_ = lean_box(v___x_2757_);
v___x_2759_ = l_instInhabitedOfMonad___redArg(v___x_2756_, v___x_2758_);
v___f_2760_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2760_, 0, v___x_2759_);
v___x_970__overap_2761_ = lean_panic_fn_borrowed(v___f_2760_, v_msg_2734_);
lean_dec_ref(v___f_2760_);
lean_inc(v___y_2738_);
lean_inc_ref(v___y_2737_);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
v___x_2762_ = lean_apply_5(v___x_970__overap_2761_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, lean_box(0));
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0___boxed(lean_object* v_msg_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(v_msg_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
return v_res_2769_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2771_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2));
v___x_2772_ = lean_unsigned_to_nat(50u);
v___x_2773_ = lean_unsigned_to_nat(345u);
v___x_2774_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__0));
v___x_2775_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2776_ = l_mkPanicMessageWithDecl(v___x_2775_, v___x_2774_, v___x_2773_, v___x_2772_, v___x_2771_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(lean_object* v_type_2777_, lean_object* v_predVars_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v_t_2785_; lean_object* v_b_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v_type_2795_; 
v_type_2795_ = l_Lean_Expr_headBeta(v_type_2777_);
switch(lean_obj_tag(v_type_2795_))
{
case 0:
{
lean_object* v_deBruijnIndex_2796_; uint8_t v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v_deBruijnIndex_2796_ = lean_ctor_get(v_type_2795_, 0);
lean_inc(v_deBruijnIndex_2796_);
lean_dec_ref_known(v_type_2795_, 1);
v___x_2797_ = 0;
v___x_2798_ = lean_array_get_size(v_predVars_2778_);
v___x_2799_ = lean_nat_sub(v___x_2798_, v_deBruijnIndex_2796_);
lean_dec(v_deBruijnIndex_2796_);
v___x_2800_ = lean_unsigned_to_nat(1u);
v___x_2801_ = lean_nat_sub(v___x_2799_, v___x_2800_);
lean_dec(v___x_2799_);
v___x_2802_ = lean_box(v___x_2797_);
v___x_2803_ = lean_array_get(v___x_2802_, v_predVars_2778_, v___x_2801_);
lean_dec(v___x_2801_);
lean_dec_ref(v_predVars_2778_);
lean_dec(v___x_2802_);
v___x_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
return v___x_2804_;
}
case 1:
{
lean_object* v_fvarId_2805_; lean_object* v___x_2806_; 
lean_dec_ref(v_predVars_2778_);
v_fvarId_2805_ = lean_ctor_get(v_type_2795_, 0);
lean_inc(v_fvarId_2805_);
lean_dec_ref_known(v_type_2795_, 1);
v___x_2806_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2805_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2816_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2809_ = v___x_2806_;
v_isShared_2810_ = v_isSharedCheck_2816_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2806_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2816_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
uint8_t v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2814_; 
v___x_2811_ = l_Lean_Compiler_LCNF_isPredicateType(v_a_2807_);
v___x_2812_ = lean_box(v___x_2811_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 0, v___x_2812_);
v___x_2814_ = v___x_2809_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2812_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
v_a_2817_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2806_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2806_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
case 3:
{
uint8_t v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
lean_dec_ref_known(v_type_2795_, 1);
lean_dec_ref(v_predVars_2778_);
v___x_2825_ = 0;
v___x_2826_ = lean_box(v___x_2825_);
v___x_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
return v___x_2827_;
}
case 4:
{
uint8_t v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
lean_dec_ref(v_predVars_2778_);
v___x_2828_ = l_Lean_Expr_isErased(v_type_2795_);
lean_dec_ref_known(v_type_2795_, 2);
v___x_2829_ = lean_box(v___x_2828_);
v___x_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
return v___x_2830_;
}
case 5:
{
lean_object* v_fn_2831_; 
v_fn_2831_ = lean_ctor_get(v_type_2795_, 0);
lean_inc_ref(v_fn_2831_);
lean_dec_ref_known(v_type_2795_, 2);
v_type_2777_ = v_fn_2831_;
goto _start;
}
case 6:
{
lean_object* v_binderType_2833_; lean_object* v_body_2834_; 
v_binderType_2833_ = lean_ctor_get(v_type_2795_, 1);
lean_inc_ref(v_binderType_2833_);
v_body_2834_ = lean_ctor_get(v_type_2795_, 2);
lean_inc_ref(v_body_2834_);
lean_dec_ref_known(v_type_2795_, 3);
v_t_2785_ = v_binderType_2833_;
v_b_2786_ = v_body_2834_;
v___y_2787_ = v_a_2779_;
v___y_2788_ = v_a_2780_;
v___y_2789_ = v_a_2781_;
v___y_2790_ = v_a_2782_;
goto v___jp_2784_;
}
case 7:
{
lean_object* v_binderType_2835_; lean_object* v_body_2836_; 
v_binderType_2835_ = lean_ctor_get(v_type_2795_, 1);
lean_inc_ref(v_binderType_2835_);
v_body_2836_ = lean_ctor_get(v_type_2795_, 2);
lean_inc_ref(v_body_2836_);
lean_dec_ref_known(v_type_2795_, 3);
v_t_2785_ = v_binderType_2835_;
v_b_2786_ = v_body_2836_;
v___y_2787_ = v_a_2779_;
v___y_2788_ = v_a_2780_;
v___y_2789_ = v_a_2781_;
v___y_2790_ = v_a_2782_;
goto v___jp_2784_;
}
case 10:
{
lean_object* v_expr_2837_; 
v_expr_2837_ = lean_ctor_get(v_type_2795_, 1);
lean_inc_ref(v_expr_2837_);
lean_dec_ref_known(v_type_2795_, 2);
v_type_2777_ = v_expr_2837_;
goto _start;
}
default: 
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
lean_dec_ref(v_type_2795_);
lean_dec_ref(v_predVars_2778_);
v___x_2839_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1, &l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1);
v___x_2840_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(v___x_2839_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_);
return v___x_2840_;
}
}
v___jp_2784_:
{
uint8_t v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2791_ = l_Lean_Compiler_LCNF_isPredicateType(v_t_2785_);
v___x_2792_ = lean_box(v___x_2791_);
v___x_2793_ = lean_array_push(v_predVars_2778_, v___x_2792_);
v_type_2777_ = v_b_2786_;
v_predVars_2778_ = v___x_2793_;
v_a_2779_ = v___y_2787_;
v_a_2780_ = v___y_2788_;
v_a_2781_ = v___y_2789_;
v_a_2782_ = v___y_2790_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___boxed(lean_object* v_type_2841_, lean_object* v_predVars_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(v_type_2841_, v_predVars_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_);
lean_dec(v_a_2846_);
lean_dec_ref(v_a_2845_);
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2843_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible(lean_object* v_type_2849_, lean_object* v_predVars_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(v_type_2849_, v_predVars_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible___boxed(lean_object* v_type_2857_, lean_object* v_predVars_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lean_Compiler_LCNF_isErasedCompatible(v_type_2857_, v_predVars_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_);
lean_dec(v_a_2862_);
lean_dec_ref(v_a_2861_);
lean_dec(v_a_2860_);
lean_dec_ref(v_a_2859_);
return v_res_2864_;
}
}
LEAN_EXPORT uint8_t l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(lean_object* v_x_2865_, lean_object* v_x_2866_){
_start:
{
if (lean_obj_tag(v_x_2865_) == 0)
{
if (lean_obj_tag(v_x_2866_) == 0)
{
uint8_t v___x_2867_; 
v___x_2867_ = 1;
return v___x_2867_;
}
else
{
uint8_t v___x_2868_; 
v___x_2868_ = 0;
return v___x_2868_;
}
}
else
{
if (lean_obj_tag(v_x_2866_) == 0)
{
uint8_t v___x_2869_; 
v___x_2869_ = 0;
return v___x_2869_;
}
else
{
lean_object* v_head_2870_; lean_object* v_tail_2871_; lean_object* v_head_2872_; lean_object* v_tail_2873_; uint8_t v___x_2874_; 
v_head_2870_ = lean_ctor_get(v_x_2865_, 0);
v_tail_2871_ = lean_ctor_get(v_x_2865_, 1);
v_head_2872_ = lean_ctor_get(v_x_2866_, 0);
v_tail_2873_ = lean_ctor_get(v_x_2866_, 1);
v___x_2874_ = l_Lean_Level_isEquiv(v_head_2870_, v_head_2872_);
if (v___x_2874_ == 0)
{
return v___x_2874_;
}
else
{
v_x_2865_ = v_tail_2871_;
v_x_2866_ = v_tail_2873_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0___boxed(lean_object* v_x_2876_, lean_object* v_x_2877_){
_start:
{
uint8_t v_res_2878_; lean_object* v_r_2879_; 
v_res_2878_ = l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(v_x_2876_, v_x_2877_);
lean_dec(v_x_2877_);
lean_dec(v_x_2876_);
v_r_2879_ = lean_box(v_res_2878_);
return v_r_2879_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_eqvTypes(lean_object* v_a_2880_, lean_object* v_b_2881_){
_start:
{
uint8_t v___x_2882_; lean_object* v_d_u2081_2884_; lean_object* v_b_u2081_2885_; lean_object* v_d_u2082_2886_; lean_object* v_b_u2082_2887_; uint8_t v___x_2890_; uint8_t v___y_2892_; 
v___x_2882_ = lean_expr_eqv(v_a_2880_, v_b_2881_);
v___x_2890_ = 1;
if (v___x_2882_ == 0)
{
uint8_t v___x_2936_; 
v___x_2936_ = l_Lean_Expr_isErased(v_a_2880_);
if (v___x_2936_ == 0)
{
v___y_2892_ = v___x_2882_;
goto v___jp_2891_;
}
else
{
uint8_t v___x_2937_; 
v___x_2937_ = l_Lean_Expr_isErased(v_b_2881_);
v___y_2892_ = v___x_2937_;
goto v___jp_2891_;
}
}
else
{
lean_dec_ref(v_b_2881_);
lean_dec_ref(v_a_2880_);
return v___x_2890_;
}
v___jp_2883_:
{
uint8_t v___x_2888_; 
v___x_2888_ = l_Lean_Compiler_LCNF_eqvTypes(v_d_u2081_2884_, v_d_u2082_2886_);
if (v___x_2888_ == 0)
{
lean_dec_ref(v_b_u2082_2887_);
lean_dec_ref(v_b_u2081_2885_);
return v___x_2882_;
}
else
{
v_a_2880_ = v_b_u2081_2885_;
v_b_2881_ = v_b_u2082_2887_;
goto _start;
}
}
v___jp_2891_:
{
if (v___y_2892_ == 0)
{
lean_object* v_a_x27_2893_; lean_object* v_b_x27_2894_; uint8_t v___x_2895_; 
lean_inc_ref(v_a_2880_);
v_a_x27_2893_ = l_Lean_Expr_headBeta(v_a_2880_);
lean_inc_ref(v_b_2881_);
v_b_x27_2894_ = l_Lean_Expr_headBeta(v_b_2881_);
v___x_2895_ = lean_expr_eqv(v_a_2880_, v_a_x27_2893_);
if (v___x_2895_ == 0)
{
lean_dec_ref(v_b_2881_);
lean_dec_ref(v_a_2880_);
v_a_2880_ = v_a_x27_2893_;
v_b_2881_ = v_b_x27_2894_;
goto _start;
}
else
{
uint8_t v___x_2897_; 
v___x_2897_ = lean_expr_eqv(v_b_2881_, v_b_x27_2894_);
if (v___x_2897_ == 0)
{
lean_dec_ref(v_b_2881_);
lean_dec_ref(v_a_2880_);
v_a_2880_ = v_a_x27_2893_;
v_b_2881_ = v_b_x27_2894_;
goto _start;
}
else
{
lean_dec_ref(v_b_x27_2894_);
lean_dec_ref(v_a_x27_2893_);
switch(lean_obj_tag(v_a_2880_))
{
case 10:
{
lean_object* v_expr_2899_; 
v_expr_2899_ = lean_ctor_get(v_a_2880_, 1);
lean_inc_ref(v_expr_2899_);
lean_dec_ref_known(v_a_2880_, 2);
v_a_2880_ = v_expr_2899_;
goto _start;
}
case 5:
{
switch(lean_obj_tag(v_b_2881_))
{
case 10:
{
lean_object* v_expr_2901_; 
v_expr_2901_ = lean_ctor_get(v_b_2881_, 1);
lean_inc_ref(v_expr_2901_);
lean_dec_ref_known(v_b_2881_, 2);
v_b_2881_ = v_expr_2901_;
goto _start;
}
case 5:
{
lean_object* v_fn_2903_; lean_object* v_arg_2904_; lean_object* v_fn_2905_; lean_object* v_arg_2906_; uint8_t v___x_2907_; 
v_fn_2903_ = lean_ctor_get(v_a_2880_, 0);
lean_inc_ref(v_fn_2903_);
v_arg_2904_ = lean_ctor_get(v_a_2880_, 1);
lean_inc_ref(v_arg_2904_);
lean_dec_ref_known(v_a_2880_, 2);
v_fn_2905_ = lean_ctor_get(v_b_2881_, 0);
lean_inc_ref(v_fn_2905_);
v_arg_2906_ = lean_ctor_get(v_b_2881_, 1);
lean_inc_ref(v_arg_2906_);
lean_dec_ref_known(v_b_2881_, 2);
v___x_2907_ = l_Lean_Compiler_LCNF_eqvTypes(v_fn_2903_, v_fn_2905_);
if (v___x_2907_ == 0)
{
lean_dec_ref(v_arg_2906_);
lean_dec_ref(v_arg_2904_);
return v___x_2882_;
}
else
{
v_a_2880_ = v_arg_2904_;
v_b_2881_ = v_arg_2906_;
goto _start;
}
}
default: 
{
lean_dec_ref_known(v_a_2880_, 2);
lean_dec_ref(v_b_2881_);
return v___y_2892_;
}
}
}
case 7:
{
switch(lean_obj_tag(v_b_2881_))
{
case 10:
{
lean_object* v_expr_2909_; 
v_expr_2909_ = lean_ctor_get(v_b_2881_, 1);
lean_inc_ref(v_expr_2909_);
lean_dec_ref_known(v_b_2881_, 2);
v_b_2881_ = v_expr_2909_;
goto _start;
}
case 7:
{
lean_object* v_binderType_2911_; lean_object* v_body_2912_; lean_object* v_binderType_2913_; lean_object* v_body_2914_; 
v_binderType_2911_ = lean_ctor_get(v_a_2880_, 1);
lean_inc_ref(v_binderType_2911_);
v_body_2912_ = lean_ctor_get(v_a_2880_, 2);
lean_inc_ref(v_body_2912_);
lean_dec_ref_known(v_a_2880_, 3);
v_binderType_2913_ = lean_ctor_get(v_b_2881_, 1);
lean_inc_ref(v_binderType_2913_);
v_body_2914_ = lean_ctor_get(v_b_2881_, 2);
lean_inc_ref(v_body_2914_);
lean_dec_ref_known(v_b_2881_, 3);
v_d_u2081_2884_ = v_binderType_2911_;
v_b_u2081_2885_ = v_body_2912_;
v_d_u2082_2886_ = v_binderType_2913_;
v_b_u2082_2887_ = v_body_2914_;
goto v___jp_2883_;
}
default: 
{
lean_dec_ref_known(v_a_2880_, 3);
lean_dec_ref(v_b_2881_);
return v___y_2892_;
}
}
}
case 6:
{
switch(lean_obj_tag(v_b_2881_))
{
case 10:
{
lean_object* v_expr_2915_; 
v_expr_2915_ = lean_ctor_get(v_b_2881_, 1);
lean_inc_ref(v_expr_2915_);
lean_dec_ref_known(v_b_2881_, 2);
v_b_2881_ = v_expr_2915_;
goto _start;
}
case 6:
{
lean_object* v_binderType_2917_; lean_object* v_body_2918_; lean_object* v_binderType_2919_; lean_object* v_body_2920_; 
v_binderType_2917_ = lean_ctor_get(v_a_2880_, 1);
lean_inc_ref(v_binderType_2917_);
v_body_2918_ = lean_ctor_get(v_a_2880_, 2);
lean_inc_ref(v_body_2918_);
lean_dec_ref_known(v_a_2880_, 3);
v_binderType_2919_ = lean_ctor_get(v_b_2881_, 1);
lean_inc_ref(v_binderType_2919_);
v_body_2920_ = lean_ctor_get(v_b_2881_, 2);
lean_inc_ref(v_body_2920_);
lean_dec_ref_known(v_b_2881_, 3);
v_d_u2081_2884_ = v_binderType_2917_;
v_b_u2081_2885_ = v_body_2918_;
v_d_u2082_2886_ = v_binderType_2919_;
v_b_u2082_2887_ = v_body_2920_;
goto v___jp_2883_;
}
default: 
{
lean_dec_ref_known(v_a_2880_, 3);
lean_dec_ref(v_b_2881_);
return v___y_2892_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_b_2881_))
{
case 10:
{
lean_object* v_expr_2921_; 
v_expr_2921_ = lean_ctor_get(v_b_2881_, 1);
lean_inc_ref(v_expr_2921_);
lean_dec_ref_known(v_b_2881_, 2);
v_b_2881_ = v_expr_2921_;
goto _start;
}
case 3:
{
lean_object* v_u_2923_; lean_object* v_u_2924_; uint8_t v___x_2925_; 
v_u_2923_ = lean_ctor_get(v_a_2880_, 0);
lean_inc(v_u_2923_);
lean_dec_ref_known(v_a_2880_, 1);
v_u_2924_ = lean_ctor_get(v_b_2881_, 0);
lean_inc(v_u_2924_);
lean_dec_ref_known(v_b_2881_, 1);
v___x_2925_ = l_Lean_Level_isEquiv(v_u_2923_, v_u_2924_);
lean_dec(v_u_2924_);
lean_dec(v_u_2923_);
return v___x_2925_;
}
default: 
{
lean_dec_ref_known(v_a_2880_, 1);
lean_dec_ref(v_b_2881_);
return v___y_2892_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_b_2881_))
{
case 10:
{
lean_object* v_expr_2926_; 
v_expr_2926_ = lean_ctor_get(v_b_2881_, 1);
lean_inc_ref(v_expr_2926_);
lean_dec_ref_known(v_b_2881_, 2);
v_b_2881_ = v_expr_2926_;
goto _start;
}
case 4:
{
lean_object* v_declName_2928_; lean_object* v_us_2929_; lean_object* v_declName_2930_; lean_object* v_us_2931_; uint8_t v___x_2932_; 
v_declName_2928_ = lean_ctor_get(v_a_2880_, 0);
lean_inc(v_declName_2928_);
v_us_2929_ = lean_ctor_get(v_a_2880_, 1);
lean_inc(v_us_2929_);
lean_dec_ref_known(v_a_2880_, 2);
v_declName_2930_ = lean_ctor_get(v_b_2881_, 0);
lean_inc(v_declName_2930_);
v_us_2931_ = lean_ctor_get(v_b_2881_, 1);
lean_inc(v_us_2931_);
lean_dec_ref_known(v_b_2881_, 2);
v___x_2932_ = lean_name_eq(v_declName_2928_, v_declName_2930_);
lean_dec(v_declName_2930_);
lean_dec(v_declName_2928_);
if (v___x_2932_ == 0)
{
lean_dec(v_us_2931_);
lean_dec(v_us_2929_);
return v___x_2882_;
}
else
{
uint8_t v___x_2933_; 
v___x_2933_ = l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(v_us_2929_, v_us_2931_);
lean_dec(v_us_2931_);
lean_dec(v_us_2929_);
return v___x_2933_;
}
}
default: 
{
lean_dec_ref_known(v_a_2880_, 2);
lean_dec_ref(v_b_2881_);
return v___y_2892_;
}
}
}
default: 
{
if (lean_obj_tag(v_b_2881_) == 10)
{
lean_object* v_expr_2934_; 
v_expr_2934_ = lean_ctor_get(v_b_2881_, 1);
lean_inc_ref(v_expr_2934_);
lean_dec_ref_known(v_b_2881_, 2);
v_b_2881_ = v_expr_2934_;
goto _start;
}
else
{
lean_dec_ref(v_b_2881_);
lean_dec_ref(v_a_2880_);
return v___y_2892_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_b_2881_);
lean_dec_ref(v_a_2880_);
return v___x_2890_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eqvTypes___boxed(lean_object* v_a_2938_, lean_object* v_b_2939_){
_start:
{
uint8_t v_res_2940_; lean_object* v_r_2941_; 
v_res_2940_ = l_Lean_Compiler_LCNF_eqvTypes(v_a_2938_, v_b_2939_);
v_r_2941_ = lean_box(v_res_2940_);
return v_r_2941_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_OtherDecl(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_OtherDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_OtherDecl(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_OtherDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_InferType(builtin);
}
#ifdef __cplusplus
}
#endif
