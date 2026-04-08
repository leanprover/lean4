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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_dec_ref(v___x_69_);
v___x_71_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v___x_68_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; 
v_a_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_a_72_);
lean_dec_ref(v___x_71_);
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
lean_dec_ref(v___x_71_);
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
lean_dec_ref(v___x_285_);
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
lean_dec_ref(v___x_371_);
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
lean_dec_ref(v___x_416_);
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
lean_dec_ref(v_a_420_);
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
v___x_537_ = lean_st_ref_set(v___y_509_, v___x_536_);
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
lean_object* v___x_576_; lean_object* v_toApplicative_577_; lean_object* v_toFunctor_578_; lean_object* v_toSeq_579_; lean_object* v_toSeqLeft_580_; lean_object* v_toSeqRight_581_; lean_object* v___f_582_; lean_object* v___f_583_; lean_object* v___f_584_; lean_object* v___f_585_; lean_object* v___x_586_; lean_object* v___f_587_; lean_object* v___f_588_; lean_object* v___f_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___x_6849__overap_597_; lean_object* v___x_598_; 
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
v___x_6849__overap_597_ = lean_panic_fn_borrowed(v___f_596_, v_msg_569_);
lean_dec_ref(v___f_596_);
lean_inc(v___y_574_);
lean_inc_ref(v___y_573_);
lean_inc(v___y_572_);
lean_inc_ref(v___y_571_);
lean_inc_ref(v___y_570_);
v___x_598_ = lean_apply_6(v___x_6849__overap_597_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, lean_box(0));
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
lean_dec_ref(v___x_631_);
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
lean_dec_ref(v___x_640_);
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
lean_dec_ref(v___x_677_);
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
lean_dec_ref(v_fst_695_);
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
lean_dec_ref(v_e_717_);
v___x_730_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc_n(v_a_731_, 2);
lean_dec_ref(v___x_730_);
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
lean_dec_ref(v_e_717_);
v___x_750_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_752_; uint8_t v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc_n(v_a_751_, 2);
lean_dec_ref(v___x_750_);
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
lean_dec_ref(v___x_768_);
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
lean_dec_ref(v_e_789_);
v___x_797_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_fvarId_796_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
return v___x_797_;
}
case 3:
{
lean_object* v_u_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_u_798_ = lean_ctor_get(v_e_789_, 0);
lean_inc(v_u_798_);
lean_dec_ref(v_e_789_);
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
lean_dec_ref(v_e_789_);
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
lean_dec_ref(v_a_818_);
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
lean_dec_ref(v___x_855_);
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
lean_dec_ref(v_a_858_);
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
lean_dec_ref(v_e_907_);
v___x_919_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc_n(v_a_920_, 2);
lean_dec_ref(v___x_919_);
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
lean_dec_ref(v_a_937_);
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
lean_dec_ref(v_fst_952_);
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
lean_dec_ref(v_arg_1108_);
v___x_1118_ = l_Lean_Compiler_LCNF_getType(v_fvarId_1117_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
return v___x_1118_;
}
default: 
{
lean_object* v_expr_1119_; lean_object* v___x_1120_; 
v_expr_1119_ = lean_ctor_get(v_arg_1108_, 0);
lean_inc_ref(v_expr_1119_);
lean_dec_ref(v_arg_1108_);
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
lean_dec_ref(v___x_1151_);
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
lean_dec_ref(v___x_1160_);
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
lean_dec_ref(v_fst_1203_);
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
v___x_1267_ = lean_alloc_ctor(0, 10, 0);
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
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(lean_object* v_msg_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_options_1274_; lean_object* v_ref_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v_options_1274_ = lean_ctor_get(v___y_1271_, 2);
v_ref_1275_ = lean_ctor_get(v___y_1271_, 5);
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
lean_dec_ref(v_snd_1357_);
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
lean_dec_ref(v___x_1378_);
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
lean_dec_ref(v_snd_1429_);
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
lean_dec_ref(v___x_1450_);
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
lean_object* v_fileName_1490_; lean_object* v_fileMap_1491_; lean_object* v_options_1492_; lean_object* v_currRecDepth_1493_; lean_object* v_maxRecDepth_1494_; lean_object* v_ref_1495_; lean_object* v_currNamespace_1496_; lean_object* v_openDecls_1497_; lean_object* v_initHeartbeats_1498_; lean_object* v_maxHeartbeats_1499_; lean_object* v_quotContext_1500_; lean_object* v_currMacroScope_1501_; uint8_t v_diag_1502_; lean_object* v_cancelTk_x3f_1503_; uint8_t v_suppressElabErrors_1504_; lean_object* v_inheritedTraceOptions_1505_; lean_object* v_ref_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v_fileName_1490_ = lean_ctor_get(v___y_1487_, 0);
v_fileMap_1491_ = lean_ctor_get(v___y_1487_, 1);
v_options_1492_ = lean_ctor_get(v___y_1487_, 2);
v_currRecDepth_1493_ = lean_ctor_get(v___y_1487_, 3);
v_maxRecDepth_1494_ = lean_ctor_get(v___y_1487_, 4);
v_ref_1495_ = lean_ctor_get(v___y_1487_, 5);
v_currNamespace_1496_ = lean_ctor_get(v___y_1487_, 6);
v_openDecls_1497_ = lean_ctor_get(v___y_1487_, 7);
v_initHeartbeats_1498_ = lean_ctor_get(v___y_1487_, 8);
v_maxHeartbeats_1499_ = lean_ctor_get(v___y_1487_, 9);
v_quotContext_1500_ = lean_ctor_get(v___y_1487_, 10);
v_currMacroScope_1501_ = lean_ctor_get(v___y_1487_, 11);
v_diag_1502_ = lean_ctor_get_uint8(v___y_1487_, sizeof(void*)*14);
v_cancelTk_x3f_1503_ = lean_ctor_get(v___y_1487_, 12);
v_suppressElabErrors_1504_ = lean_ctor_get_uint8(v___y_1487_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1505_ = lean_ctor_get(v___y_1487_, 13);
v_ref_1506_ = l_Lean_replaceRef(v_ref_1482_, v_ref_1495_);
lean_inc_ref(v_inheritedTraceOptions_1505_);
lean_inc(v_cancelTk_x3f_1503_);
lean_inc(v_currMacroScope_1501_);
lean_inc(v_quotContext_1500_);
lean_inc(v_maxHeartbeats_1499_);
lean_inc(v_initHeartbeats_1498_);
lean_inc(v_openDecls_1497_);
lean_inc(v_currNamespace_1496_);
lean_inc(v_maxRecDepth_1494_);
lean_inc(v_currRecDepth_1493_);
lean_inc_ref(v_options_1492_);
lean_inc_ref(v_fileMap_1491_);
lean_inc_ref(v_fileName_1490_);
v___x_1507_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1507_, 0, v_fileName_1490_);
lean_ctor_set(v___x_1507_, 1, v_fileMap_1491_);
lean_ctor_set(v___x_1507_, 2, v_options_1492_);
lean_ctor_set(v___x_1507_, 3, v_currRecDepth_1493_);
lean_ctor_set(v___x_1507_, 4, v_maxRecDepth_1494_);
lean_ctor_set(v___x_1507_, 5, v_ref_1506_);
lean_ctor_set(v___x_1507_, 6, v_currNamespace_1496_);
lean_ctor_set(v___x_1507_, 7, v_openDecls_1497_);
lean_ctor_set(v___x_1507_, 8, v_initHeartbeats_1498_);
lean_ctor_set(v___x_1507_, 9, v_maxHeartbeats_1499_);
lean_ctor_set(v___x_1507_, 10, v_quotContext_1500_);
lean_ctor_set(v___x_1507_, 11, v_currMacroScope_1501_);
lean_ctor_set(v___x_1507_, 12, v_cancelTk_x3f_1503_);
lean_ctor_set(v___x_1507_, 13, v_inheritedTraceOptions_1505_);
lean_ctor_set_uint8(v___x_1507_, sizeof(void*)*14, v_diag_1502_);
lean_ctor_set_uint8(v___x_1507_, sizeof(void*)*14 + 1, v_suppressElabErrors_1504_);
v___x_1508_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v_msg_1483_, v___y_1485_, v___y_1486_, v___x_1507_, v___y_1488_);
lean_dec_ref(v___x_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_ref_1509_, lean_object* v_msg_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_1509_, v_msg_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v_ref_1509_);
return v_res_1517_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1518_ = lean_box(1);
v___x_1519_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3);
v___x_1520_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1);
v___x_1521_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
lean_ctor_set(v___x_1521_, 1, v___x_1519_);
lean_ctor_set(v___x_1521_, 2, v___x_1518_);
return v___x_1521_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__1));
v___x_1524_ = l_Lean_stringToMessageData(v___x_1523_);
return v___x_1524_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__3));
v___x_1527_ = l_Lean_stringToMessageData(v___x_1526_);
return v___x_1527_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__5));
v___x_1530_ = l_Lean_stringToMessageData(v___x_1529_);
return v___x_1530_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__7));
v___x_1533_ = l_Lean_stringToMessageData(v___x_1532_);
return v___x_1533_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__9));
v___x_1536_ = l_Lean_stringToMessageData(v___x_1535_);
return v___x_1536_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__11));
v___x_1539_ = l_Lean_stringToMessageData(v___x_1538_);
return v___x_1539_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__13));
v___x_1542_ = l_Lean_stringToMessageData(v___x_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(lean_object* v_msg_1543_, lean_object* v_declHint_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; lean_object* v_env_1548_; uint8_t v___x_1549_; 
v___x_1547_ = lean_st_ref_get(v___y_1545_);
v_env_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc_ref(v_env_1548_);
lean_dec(v___x_1547_);
v___x_1549_ = l_Lean_Name_isAnonymous(v_declHint_1544_);
if (v___x_1549_ == 0)
{
uint8_t v_isExporting_1550_; 
v_isExporting_1550_ = lean_ctor_get_uint8(v_env_1548_, sizeof(void*)*8);
if (v_isExporting_1550_ == 0)
{
lean_object* v___x_1551_; 
lean_dec_ref(v_env_1548_);
lean_dec(v_declHint_1544_);
v___x_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1551_, 0, v_msg_1543_);
return v___x_1551_;
}
else
{
lean_object* v___x_1552_; uint8_t v___x_1553_; 
lean_inc_ref(v_env_1548_);
v___x_1552_ = l_Lean_Environment_setExporting(v_env_1548_, v___x_1549_);
lean_inc(v_declHint_1544_);
lean_inc_ref(v___x_1552_);
v___x_1553_ = l_Lean_Environment_contains(v___x_1552_, v_declHint_1544_, v_isExporting_1550_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; 
lean_dec_ref(v___x_1552_);
lean_dec_ref(v_env_1548_);
lean_dec(v_declHint_1544_);
v___x_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1554_, 0, v_msg_1543_);
return v___x_1554_;
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v_c_1560_; lean_object* v___x_1561_; 
v___x_1555_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2);
v___x_1556_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0);
v___x_1557_ = l_Lean_Options_empty;
v___x_1558_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1552_);
lean_ctor_set(v___x_1558_, 1, v___x_1555_);
lean_ctor_set(v___x_1558_, 2, v___x_1556_);
lean_ctor_set(v___x_1558_, 3, v___x_1557_);
lean_inc(v_declHint_1544_);
v___x_1559_ = l_Lean_MessageData_ofConstName(v_declHint_1544_, v___x_1549_);
v_c_1560_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1560_, 0, v___x_1558_);
lean_ctor_set(v_c_1560_, 1, v___x_1559_);
v___x_1561_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1548_, v_declHint_1544_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_dec_ref(v_env_1548_);
lean_dec(v_declHint_1544_);
v___x_1562_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2);
v___x_1563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
lean_ctor_set(v___x_1563_, 1, v_c_1560_);
v___x_1564_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4);
v___x_1565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1563_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = l_Lean_MessageData_note(v___x_1565_);
v___x_1567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1567_, 0, v_msg_1543_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
return v___x_1568_;
}
else
{
lean_object* v_val_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1604_; 
v_val_1569_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1571_ = v___x_1561_;
v_isShared_1572_ = v_isSharedCheck_1604_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_val_1569_);
lean_dec(v___x_1561_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1604_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v_mod_1576_; uint8_t v___x_1577_; 
v___x_1573_ = lean_box(0);
v___x_1574_ = l_Lean_Environment_header(v_env_1548_);
lean_dec_ref(v_env_1548_);
v___x_1575_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1574_);
v_mod_1576_ = lean_array_get(v___x_1573_, v___x_1575_, v_val_1569_);
lean_dec(v_val_1569_);
lean_dec_ref(v___x_1575_);
v___x_1577_ = l_Lean_isPrivateName(v_declHint_1544_);
lean_dec(v_declHint_1544_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1589_; 
v___x_1578_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6);
v___x_1579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
lean_ctor_set(v___x_1579_, 1, v_c_1560_);
v___x_1580_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8);
v___x_1581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = l_Lean_MessageData_ofName(v_mod_1576_);
v___x_1583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1581_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10);
v___x_1585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1583_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = l_Lean_MessageData_note(v___x_1585_);
v___x_1587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1587_, 0, v_msg_1543_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set_tag(v___x_1571_, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1587_);
v___x_1589_ = v___x_1571_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1591_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2);
v___x_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
lean_ctor_set(v___x_1592_, 1, v_c_1560_);
v___x_1593_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12);
v___x_1594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1592_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = l_Lean_MessageData_ofName(v_mod_1576_);
v___x_1596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1594_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
v___x_1597_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14);
v___x_1598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1596_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = l_Lean_MessageData_note(v___x_1598_);
v___x_1600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1600_, 0, v_msg_1543_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set_tag(v___x_1571_, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1600_);
v___x_1602_ = v___x_1571_;
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
else
{
lean_object* v___x_1605_; 
lean_dec_ref(v_env_1548_);
lean_dec(v_declHint_1544_);
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v_msg_1543_);
return v___x_1605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_msg_1606_, lean_object* v_declHint_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_1606_, v_declHint_1607_, v___y_1608_);
lean_dec(v___y_1608_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(lean_object* v_msg_1611_, lean_object* v_declHint_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1629_; 
v___x_1619_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_1611_, v_declHint_1612_, v___y_1617_);
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1622_ = v___x_1619_;
v_isShared_1623_ = v_isSharedCheck_1629_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1619_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1629_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1627_; 
v___x_1624_ = l_Lean_unknownIdentifierMessageTag;
v___x_1625_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
lean_ctor_set(v___x_1625_, 1, v_a_1620_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v___x_1625_);
v___x_1627_ = v___x_1622_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_msg_1630_, lean_object* v_declHint_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(v_msg_1630_, v_declHint_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec_ref(v___y_1632_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1639_, lean_object* v_msg_1640_, lean_object* v_declHint_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v___x_1648_; lean_object* v_a_1649_; lean_object* v___x_1650_; 
v___x_1648_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(v_msg_1640_, v_declHint_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref(v___x_1648_);
v___x_1650_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_1639_, v_a_1649_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1651_, lean_object* v_msg_1652_, lean_object* v_declHint_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1651_, v_msg_1652_, v_declHint_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v_ref_1651_);
return v_res_1660_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__0));
v___x_1663_ = l_Lean_stringToMessageData(v___x_1662_);
return v___x_1663_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__2));
v___x_1666_ = l_Lean_stringToMessageData(v___x_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(lean_object* v_ref_1667_, lean_object* v_constName_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v___x_1675_; uint8_t v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1675_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_1676_ = 0;
lean_inc(v_constName_1668_);
v___x_1677_ = l_Lean_MessageData_ofConstName(v_constName_1668_, v___x_1676_);
v___x_1678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1675_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
v___x_1679_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3);
v___x_1680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1678_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1667_, v___x_1680_, v_constName_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1682_, lean_object* v_constName_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1682_, v_constName_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v_ref_1682_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(lean_object* v_constName_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v_ref_1698_; lean_object* v___x_1699_; 
v_ref_1698_ = lean_ctor_get(v___y_1695_, 5);
v___x_1699_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1698_, v_constName_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_constName_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec_ref(v___y_1701_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(lean_object* v_constName_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___x_1715_; lean_object* v_env_1716_; uint8_t v___x_1717_; lean_object* v___x_1718_; 
v___x_1715_ = lean_st_ref_get(v___y_1713_);
v_env_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc_ref(v_env_1716_);
lean_dec(v___x_1715_);
v___x_1717_ = 0;
lean_inc(v_constName_1708_);
v___x_1718_ = l_Lean_Environment_find_x3f(v_env_1716_, v_constName_1708_, v___x_1717_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
return v___x_1719_;
}
else
{
lean_object* v_val_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
lean_dec(v_constName_1708_);
v_val_1720_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1718_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_val_1720_);
lean_dec(v___x_1718_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
lean_ctor_set_tag(v___x_1722_, 0);
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_val_1720_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1___boxed(lean_object* v_constName_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(v_constName_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v___y_1729_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(lean_object* v_structName_1736_, lean_object* v_idx_1737_, lean_object* v_s_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___x_1757_; 
lean_inc(v_s_1738_);
v___x_1757_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_s_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1853_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1853_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1853_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1762_ = l_Lean_Expr_headBeta(v_a_1758_);
v___x_1763_ = l_Lean_Expr_isErased(v___x_1762_);
if (v___x_1763_ == 0)
{
uint8_t v___x_1764_; 
v___x_1764_ = l_Lean_Expr_isAny(v___x_1762_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; 
lean_del_object(v___x_1760_);
v___x_1765_ = l_Lean_Expr_getAppFn(v___x_1762_);
if (lean_obj_tag(v___x_1765_) == 4)
{
lean_object* v_declName_1766_; lean_object* v_us_1767_; lean_object* v___x_1768_; lean_object* v_env_1769_; lean_object* v___x_1770_; 
v_declName_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_declName_1766_);
v_us_1767_ = lean_ctor_get(v___x_1765_, 1);
lean_inc(v_us_1767_);
lean_dec_ref(v___x_1765_);
v___x_1768_ = lean_st_ref_get(v_a_1743_);
v_env_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc_ref(v_env_1769_);
lean_dec(v___x_1768_);
v___x_1770_ = l_Lean_Environment_find_x3f(v_env_1769_, v_declName_1766_, v___x_1764_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_dec(v_us_1767_);
lean_dec_ref(v___x_1762_);
v___y_1746_ = v_a_1739_;
v___y_1747_ = v_a_1740_;
v___y_1748_ = v_a_1741_;
v___y_1749_ = v_a_1742_;
v___y_1750_ = v_a_1743_;
goto v___jp_1745_;
}
else
{
lean_object* v_val_1771_; 
v_val_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_val_1771_);
lean_dec_ref(v___x_1770_);
if (lean_obj_tag(v_val_1771_) == 5)
{
lean_object* v_val_1772_; lean_object* v_ctors_1773_; 
v_val_1772_ = lean_ctor_get(v_val_1771_, 0);
lean_inc_ref(v_val_1772_);
lean_dec_ref(v_val_1771_);
v_ctors_1773_ = lean_ctor_get(v_val_1772_, 4);
lean_inc(v_ctors_1773_);
if (lean_obj_tag(v_ctors_1773_) == 1)
{
lean_object* v_tail_1774_; 
v_tail_1774_ = lean_ctor_get(v_ctors_1773_, 1);
if (lean_obj_tag(v_tail_1774_) == 0)
{
lean_object* v_numParams_1775_; lean_object* v_numIndices_1776_; lean_object* v_head_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1843_; 
v_numParams_1775_ = lean_ctor_get(v_val_1772_, 1);
lean_inc(v_numParams_1775_);
v_numIndices_1776_ = lean_ctor_get(v_val_1772_, 2);
lean_inc(v_numIndices_1776_);
lean_dec_ref(v_val_1772_);
v_head_1777_ = lean_ctor_get(v_ctors_1773_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v_ctors_1773_);
if (v_isSharedCheck_1843_ == 0)
{
lean_object* v_unused_1844_; 
v_unused_1844_ = lean_ctor_get(v_ctors_1773_, 1);
lean_dec(v_unused_1844_);
v___x_1779_ = v_ctors_1773_;
v_isShared_1780_ = v_isSharedCheck_1843_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_head_1777_);
lean_dec(v_ctors_1773_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1843_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(v_head_1777_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_a_1782_);
lean_dec_ref(v___x_1781_);
if (lean_obj_tag(v_a_1782_) == 6)
{
lean_object* v_val_1783_; lean_object* v_dummy_1784_; lean_object* v_nargs_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v_val_1783_ = lean_ctor_get(v_a_1782_, 0);
lean_inc_ref(v_val_1783_);
lean_dec_ref(v_a_1782_);
v_dummy_1784_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0);
v_nargs_1785_ = l_Lean_Expr_getAppNumArgs(v___x_1762_);
lean_inc(v_nargs_1785_);
v___x_1786_ = lean_mk_array(v_nargs_1785_, v_dummy_1784_);
v___x_1787_ = lean_unsigned_to_nat(1u);
v___x_1788_ = lean_nat_sub(v_nargs_1785_, v___x_1787_);
lean_dec(v_nargs_1785_);
v___x_1789_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1762_, v___x_1786_, v___x_1788_);
v___x_1790_ = lean_nat_add(v_numParams_1775_, v_numIndices_1776_);
lean_dec(v_numIndices_1776_);
v___x_1791_ = lean_array_get_size(v___x_1789_);
v___x_1792_ = lean_nat_dec_eq(v___x_1790_, v___x_1791_);
lean_dec(v___x_1790_);
if (v___x_1792_ == 0)
{
lean_dec_ref(v___x_1789_);
lean_dec_ref(v_val_1783_);
lean_del_object(v___x_1779_);
lean_dec(v_numParams_1775_);
lean_dec(v_us_1767_);
v___y_1746_ = v_a_1739_;
v___y_1747_ = v_a_1740_;
v___y_1748_ = v_a_1741_;
v___y_1749_ = v_a_1742_;
v___y_1750_ = v_a_1743_;
goto v___jp_1745_;
}
else
{
if (v___x_1764_ == 0)
{
lean_object* v_toConstantVal_1793_; lean_object* v_name_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v_toConstantVal_1793_ = lean_ctor_get(v_val_1783_, 0);
lean_inc_ref(v_toConstantVal_1793_);
lean_dec_ref(v_val_1783_);
v_name_1794_ = lean_ctor_get(v_toConstantVal_1793_, 0);
lean_inc(v_name_1794_);
lean_dec_ref(v_toConstantVal_1793_);
v___x_1795_ = l_Lean_mkConst(v_name_1794_, v_us_1767_);
v___x_1796_ = lean_unsigned_to_nat(0u);
v___x_1797_ = l_Array_toSubarray___redArg(v___x_1789_, v___x_1796_, v_numParams_1775_);
v___x_1798_ = l_Subarray_copy___redArg(v___x_1797_);
v___x_1799_ = l_Lean_mkAppN(v___x_1795_, v___x_1798_);
lean_dec_ref(v___x_1798_);
v___x_1800_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(v___x_1799_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1802_; lean_object* v___x_1804_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1801_);
lean_dec_ref(v___x_1800_);
v___x_1802_ = lean_box(0);
if (v_isShared_1780_ == 0)
{
lean_ctor_set_tag(v___x_1779_, 0);
lean_ctor_set(v___x_1779_, 1, v_a_1801_);
lean_ctor_set(v___x_1779_, 0, v___x_1802_);
v___x_1804_ = v___x_1779_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_a_1801_);
v___x_1804_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v___x_1805_; 
lean_inc(v_structName_1736_);
lean_inc(v_s_1738_);
lean_inc(v_idx_1737_);
v___x_1805_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_idx_1737_, v_s_1738_, v_structName_1736_, v_idx_1737_, v___x_1796_, v___x_1804_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1825_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1808_ = v___x_1805_;
v_isShared_1809_ = v_isSharedCheck_1825_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1805_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1825_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v_fst_1810_; 
v_fst_1810_ = lean_ctor_get(v_a_1806_, 0);
if (lean_obj_tag(v_fst_1810_) == 0)
{
lean_object* v_snd_1811_; 
v_snd_1811_ = lean_ctor_get(v_a_1806_, 1);
lean_inc(v_snd_1811_);
lean_dec(v_a_1806_);
if (lean_obj_tag(v_snd_1811_) == 7)
{
lean_object* v_binderType_1812_; lean_object* v___x_1814_; 
lean_dec(v_s_1738_);
lean_dec(v_idx_1737_);
lean_dec(v_structName_1736_);
v_binderType_1812_ = lean_ctor_get(v_snd_1811_, 1);
lean_inc_ref(v_binderType_1812_);
lean_dec_ref(v_snd_1811_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v_binderType_1812_);
v___x_1814_ = v___x_1808_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_binderType_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
else
{
uint8_t v___x_1816_; 
v___x_1816_ = l_Lean_Expr_isErased(v_snd_1811_);
lean_dec(v_snd_1811_);
if (v___x_1816_ == 0)
{
lean_del_object(v___x_1808_);
v___y_1746_ = v_a_1739_;
v___y_1747_ = v_a_1740_;
v___y_1748_ = v_a_1741_;
v___y_1749_ = v_a_1742_;
v___y_1750_ = v_a_1743_;
goto v___jp_1745_;
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1819_; 
lean_dec(v_s_1738_);
lean_dec(v_idx_1737_);
lean_dec(v_structName_1736_);
v___x_1817_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1817_);
v___x_1819_ = v___x_1808_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
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
lean_object* v_val_1821_; lean_object* v___x_1823_; 
lean_inc_ref(v_fst_1810_);
lean_dec(v_a_1806_);
lean_dec(v_s_1738_);
lean_dec(v_idx_1737_);
lean_dec(v_structName_1736_);
v_val_1821_ = lean_ctor_get(v_fst_1810_, 0);
lean_inc(v_val_1821_);
lean_dec_ref(v_fst_1810_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v_val_1821_);
v___x_1823_ = v___x_1808_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_val_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec(v_s_1738_);
lean_dec(v_idx_1737_);
lean_dec(v_structName_1736_);
v_a_1826_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1805_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1805_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
}
else
{
lean_del_object(v___x_1779_);
lean_dec(v_s_1738_);
lean_dec(v_idx_1737_);
lean_dec(v_structName_1736_);
return v___x_1800_;
}
}
else
{
lean_dec_ref(v___x_1789_);
lean_dec_ref(v_val_1783_);
lean_del_object(v___x_1779_);
lean_dec(v_numParams_1775_);
lean_dec(v_us_1767_);
v___y_1746_ = v_a_1739_;
v___y_1747_ = v_a_1740_;
v___y_1748_ = v_a_1741_;
v___y_1749_ = v_a_1742_;
v___y_1750_ = v_a_1743_;
goto v___jp_1745_;
}
}
}
else
{
lean_dec(v_a_1782_);
lean_del_object(v___x_1779_);
lean_dec(v_numIndices_1776_);
lean_dec(v_numParams_1775_);
lean_dec(v_us_1767_);
lean_dec_ref(v___x_1762_);
v___y_1746_ = v_a_1739_;
v___y_1747_ = v_a_1740_;
v___y_1748_ = v_a_1741_;
v___y_1749_ = v_a_1742_;
v___y_1750_ = v_a_1743_;
goto v___jp_1745_;
}
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_del_object(v___x_1779_);
lean_dec(v_numIndices_1776_);
lean_dec(v_numParams_1775_);
lean_dec(v_us_1767_);
lean_dec_ref(v___x_1762_);
lean_dec(v_s_1738_);
lean_dec(v_idx_1737_);
lean_dec(v_structName_1736_);
v_a_1835_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1781_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1781_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctors_1773_);
lean_dec_ref(v_val_1772_);
lean_dec(v_us_1767_);
lean_dec_ref(v___x_1762_);
v___y_1746_ = v_a_1739_;
v___y_1747_ = v_a_1740_;
v___y_1748_ = v_a_1741_;
v___y_1749_ = v_a_1742_;
v___y_1750_ = v_a_1743_;
goto v___jp_1745_;
}
}
else
{
lean_dec(v_ctors_1773_);
lean_dec_ref(v_val_1772_);
lean_dec(v_us_1767_);
lean_dec_ref(v___x_1762_);
v___y_1746_ = v_a_1739_;
v___y_1747_ = v_a_1740_;
v___y_1748_ = v_a_1741_;
v___y_1749_ = v_a_1742_;
v___y_1750_ = v_a_1743_;
goto v___jp_1745_;
}
}
else
{
lean_dec(v_val_1771_);
lean_dec(v_us_1767_);
lean_dec_ref(v___x_1762_);
v___y_1746_ = v_a_1739_;
v___y_1747_ = v_a_1740_;
v___y_1748_ = v_a_1741_;
v___y_1749_ = v_a_1742_;
v___y_1750_ = v_a_1743_;
goto v___jp_1745_;
}
}
}
else
{
lean_dec_ref(v___x_1765_);
lean_dec_ref(v___x_1762_);
v___y_1746_ = v_a_1739_;
v___y_1747_ = v_a_1740_;
v___y_1748_ = v_a_1741_;
v___y_1749_ = v_a_1742_;
v___y_1750_ = v_a_1743_;
goto v___jp_1745_;
}
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1847_; 
lean_dec_ref(v___x_1762_);
lean_dec(v_s_1738_);
lean_dec(v_idx_1737_);
lean_dec(v_structName_1736_);
v___x_1845_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1845_);
v___x_1847_ = v___x_1760_;
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
else
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
lean_dec_ref(v___x_1762_);
lean_dec(v_s_1738_);
lean_dec(v_idx_1737_);
lean_dec(v_structName_1736_);
v___x_1849_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1849_);
v___x_1851_ = v___x_1760_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
else
{
lean_dec(v_s_1738_);
lean_dec(v_idx_1737_);
lean_dec(v_structName_1736_);
return v___x_1757_;
}
v___jp_1745_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1751_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
v___x_1752_ = l_Lean_mkFVar(v_s_1738_);
v___x_1753_ = l_Lean_mkProj(v_structName_1736_, v_idx_1737_, v___x_1752_);
v___x_1754_ = l_Lean_indentExpr(v___x_1753_);
v___x_1755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1751_);
lean_ctor_set(v___x_1755_, 1, v___x_1754_);
v___x_1756_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_1755_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
return v___x_1756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferProjType___boxed(lean_object* v_structName_1854_, lean_object* v_idx_1855_, lean_object* v_s_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(v_structName_1854_, v_idx_1855_, v_s_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec_ref(v_a_1857_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2(lean_object* v_upperBound_1864_, lean_object* v_s_1865_, lean_object* v_structName_1866_, lean_object* v_idx_1867_, lean_object* v_inst_1868_, lean_object* v_R_1869_, lean_object* v_a_1870_, lean_object* v_b_1871_, lean_object* v_c_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_upperBound_1864_, v_s_1865_, v_structName_1866_, v_idx_1867_, v_a_1870_, v_b_1871_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___boxed(lean_object* v_upperBound_1880_, lean_object* v_s_1881_, lean_object* v_structName_1882_, lean_object* v_idx_1883_, lean_object* v_inst_1884_, lean_object* v_R_1885_, lean_object* v_a_1886_, lean_object* v_b_1887_, lean_object* v_c_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2(v_upperBound_1880_, v_s_1881_, v_structName_1882_, v_idx_1883_, v_inst_1884_, v_R_1885_, v_a_1886_, v_b_1887_, v_c_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v_a_1886_);
lean_dec(v_upperBound_1880_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1(lean_object* v_00_u03b1_1896_, lean_object* v_constName_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___boxed(lean_object* v_00_u03b1_1905_, lean_object* v_constName_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1(v_00_u03b1_1905_, v_constName_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec_ref(v___y_1907_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3(lean_object* v_upperBound_1914_, lean_object* v_s_1915_, lean_object* v_structName_1916_, lean_object* v_idx_1917_, lean_object* v_inst_1918_, lean_object* v_R_1919_, lean_object* v_a_1920_, lean_object* v_b_1921_, lean_object* v_c_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_1914_, v_s_1915_, v_structName_1916_, v_idx_1917_, v_a_1920_, v_b_1921_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___boxed(lean_object* v_upperBound_1930_, lean_object* v_s_1931_, lean_object* v_structName_1932_, lean_object* v_idx_1933_, lean_object* v_inst_1934_, lean_object* v_R_1935_, lean_object* v_a_1936_, lean_object* v_b_1937_, lean_object* v_c_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3(v_upperBound_1930_, v_s_1931_, v_structName_1932_, v_idx_1933_, v_inst_1934_, v_R_1935_, v_a_1936_, v_b_1937_, v_c_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v_upperBound_1930_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_1946_, lean_object* v_ref_1947_, lean_object* v_constName_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1947_, v_constName_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1956_, lean_object* v_ref_1957_, lean_object* v_constName_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2(v_00_u03b1_1956_, v_ref_1957_, v_constName_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v_ref_1957_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1966_, lean_object* v_ref_1967_, lean_object* v_msg_1968_, lean_object* v_declHint_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1967_, v_msg_1968_, v_declHint_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1977_, lean_object* v_ref_1978_, lean_object* v_msg_1979_, lean_object* v_declHint_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4(v_00_u03b1_1977_, v_ref_1978_, v_msg_1979_, v_declHint_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v_ref_1978_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msg_1988_, lean_object* v_declHint_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_1988_, v_declHint_1989_, v___y_1994_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_1997_, lean_object* v_declHint_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_1997_, v_declHint_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec_ref(v___y_1999_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b1_2006_, lean_object* v_ref_2007_, lean_object* v_msg_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_2007_, v_msg_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b1_2016_, lean_object* v_ref_2017_, lean_object* v_msg_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7(v_00_u03b1_2016_, v_ref_2017_, v_msg_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v_ref_2017_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(lean_object* v_e_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_){
_start:
{
switch(lean_obj_tag(v_e_2026_))
{
case 0:
{
lean_object* v_value_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2041_; 
v_value_2033_ = lean_ctor_get(v_e_2026_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_e_2026_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2035_ = v_e_2026_;
v_isShared_2036_ = v_isSharedCheck_2041_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_value_2033_);
lean_dec(v_e_2026_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2041_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; lean_object* v___x_2039_; 
v___x_2037_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType(v_value_2033_);
lean_dec_ref(v_value_2033_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2037_);
v___x_2039_ = v___x_2035_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
case 1:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
return v___x_2043_;
}
case 2:
{
lean_object* v_typeName_2044_; lean_object* v_idx_2045_; lean_object* v_struct_2046_; lean_object* v___x_2047_; 
v_typeName_2044_ = lean_ctor_get(v_e_2026_, 0);
lean_inc(v_typeName_2044_);
v_idx_2045_ = lean_ctor_get(v_e_2026_, 1);
lean_inc(v_idx_2045_);
v_struct_2046_ = lean_ctor_get(v_e_2026_, 2);
lean_inc(v_struct_2046_);
lean_dec_ref(v_e_2026_);
v___x_2047_ = l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(v_typeName_2044_, v_idx_2045_, v_struct_2046_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_);
return v___x_2047_;
}
case 3:
{
lean_object* v_declName_2048_; lean_object* v_us_2049_; lean_object* v_args_2050_; lean_object* v___x_2051_; 
v_declName_2048_ = lean_ctor_get(v_e_2026_, 0);
lean_inc(v_declName_2048_);
v_us_2049_ = lean_ctor_get(v_e_2026_, 1);
lean_inc(v_us_2049_);
v_args_2050_ = lean_ctor_get(v_e_2026_, 2);
lean_inc_ref(v_args_2050_);
lean_dec_ref(v_e_2026_);
v___x_2051_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(v_declName_2048_, v_us_2049_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2053_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref(v___x_2051_);
v___x_2053_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2052_, v_args_2050_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_);
return v___x_2053_;
}
else
{
lean_dec_ref(v_args_2050_);
return v___x_2051_;
}
}
default: 
{
lean_object* v_fvarId_2054_; lean_object* v_args_2055_; lean_object* v___x_2056_; 
v_fvarId_2054_ = lean_ctor_get(v_e_2026_, 0);
lean_inc(v_fvarId_2054_);
v_args_2055_ = lean_ctor_get(v_e_2026_, 1);
lean_inc_ref(v_args_2055_);
lean_dec_ref(v_e_2026_);
v___x_2056_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_fvarId_2054_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2058_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref(v___x_2056_);
v___x_2058_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2057_, v_args_2055_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_);
return v___x_2058_;
}
else
{
lean_dec_ref(v_args_2055_);
return v___x_2056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType___boxed(lean_object* v_e_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(v_e_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
lean_dec(v_a_2064_);
lean_dec_ref(v_a_2063_);
lean_dec(v_a_2062_);
lean_dec_ref(v_a_2061_);
lean_dec_ref(v_a_2060_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType(lean_object* v_e_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2073_ = lean_unsigned_to_nat(32u);
v___x_2074_ = lean_mk_empty_array_with_capacity(v___x_2073_);
lean_dec_ref(v___x_2074_);
v___x_2075_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2076_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_e_2067_, v___x_2075_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType___boxed(lean_object* v_e_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lean_Compiler_LCNF_inferType(v_e_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(lean_object* v_msg_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v___x_2090_; lean_object* v_toApplicative_2091_; lean_object* v_toFunctor_2092_; lean_object* v_toSeq_2093_; lean_object* v_toSeqLeft_2094_; lean_object* v_toSeqRight_2095_; lean_object* v___f_2096_; lean_object* v___f_2097_; lean_object* v___f_2098_; lean_object* v___f_2099_; lean_object* v___x_2100_; lean_object* v___f_2101_; lean_object* v___f_2102_; lean_object* v___f_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___f_2109_; lean_object* v___x_208__overap_2110_; lean_object* v___x_2111_; 
v___x_2090_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_2091_ = lean_ctor_get(v___x_2090_, 0);
v_toFunctor_2092_ = lean_ctor_get(v_toApplicative_2091_, 0);
v_toSeq_2093_ = lean_ctor_get(v_toApplicative_2091_, 2);
v_toSeqLeft_2094_ = lean_ctor_get(v_toApplicative_2091_, 3);
v_toSeqRight_2095_ = lean_ctor_get(v_toApplicative_2091_, 4);
v___f_2096_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_2097_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2092_, 2);
v___f_2098_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2098_, 0, v_toFunctor_2092_);
v___f_2099_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2099_, 0, v_toFunctor_2092_);
v___x_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___f_2098_);
lean_ctor_set(v___x_2100_, 1, v___f_2099_);
lean_inc(v_toSeqRight_2095_);
v___f_2101_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2101_, 0, v_toSeqRight_2095_);
lean_inc(v_toSeqLeft_2094_);
v___f_2102_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2102_, 0, v_toSeqLeft_2094_);
lean_inc(v_toSeq_2093_);
v___f_2103_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2103_, 0, v_toSeq_2093_);
v___x_2104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2100_);
lean_ctor_set(v___x_2104_, 1, v___f_2096_);
lean_ctor_set(v___x_2104_, 2, v___f_2103_);
lean_ctor_set(v___x_2104_, 3, v___f_2102_);
lean_ctor_set(v___x_2104_, 4, v___f_2101_);
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
lean_ctor_set(v___x_2105_, 1, v___f_2097_);
v___x_2106_ = l_StateRefT_x27_instMonad___redArg(v___x_2105_);
v___x_2107_ = l_Lean_instInhabitedExpr;
v___x_2108_ = l_instInhabitedOfMonad___redArg(v___x_2106_, v___x_2107_);
v___f_2109_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2109_, 0, v___x_2108_);
v___x_208__overap_2110_ = lean_panic_fn_borrowed(v___f_2109_, v_msg_2084_);
lean_dec_ref(v___f_2109_);
lean_inc(v___y_2088_);
lean_inc_ref(v___y_2087_);
lean_inc(v___y_2086_);
lean_inc_ref(v___y_2085_);
v___x_2111_ = lean_apply_5(v___x_208__overap_2110_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, lean_box(0));
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0___boxed(lean_object* v_msg_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v_msg_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
return v_res_2118_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inferAppType___closed__2(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2121_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2122_ = lean_unsigned_to_nat(15u);
v___x_2123_ = lean_unsigned_to_nat(258u);
v___x_2124_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__0));
v___x_2125_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2126_ = l_mkPanicMessageWithDecl(v___x_2125_, v___x_2124_, v___x_2123_, v___x_2122_, v___x_2121_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType(uint8_t v_pu_2127_, lean_object* v_fnType_2128_, lean_object* v_args_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
if (v_pu_2127_ == 0)
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2136_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_fnType_2128_, v_args_2129_, v___x_2135_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_);
return v___x_2136_;
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
lean_dec_ref(v_args_2129_);
lean_dec_ref(v_fnType_2128_);
v___x_2137_ = lean_obj_once(&l_Lean_Compiler_LCNF_inferAppType___closed__2, &l_Lean_Compiler_LCNF_inferAppType___closed__2_once, _init_l_Lean_Compiler_LCNF_inferAppType___closed__2);
v___x_2138_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2137_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_);
return v___x_2138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType___boxed(lean_object* v_pu_2139_, lean_object* v_fnType_2140_, lean_object* v_args_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_){
_start:
{
uint8_t v_pu_boxed_2147_; lean_object* v_res_2148_; 
v_pu_boxed_2147_ = lean_unbox(v_pu_2139_);
v_res_2148_ = l_Lean_Compiler_LCNF_inferAppType(v_pu_boxed_2147_, v_fnType_2140_, v_args_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_);
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
lean_dec(v_a_2143_);
lean_dec_ref(v_a_2142_);
return v_res_2148_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Arg_inferType___closed__1(void){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2150_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2151_ = lean_unsigned_to_nat(15u);
v___x_2152_ = lean_unsigned_to_nat(263u);
v___x_2153_ = ((lean_object*)(l_Lean_Compiler_LCNF_Arg_inferType___closed__0));
v___x_2154_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2155_ = l_mkPanicMessageWithDecl(v___x_2154_, v___x_2153_, v___x_2152_, v___x_2151_, v___x_2150_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType(uint8_t v_pu_2156_, lean_object* v_arg_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_){
_start:
{
if (v_pu_2156_ == 0)
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2163_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2164_ = l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(v_arg_2157_, v___x_2163_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
return v___x_2164_;
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec(v_arg_2157_);
v___x_2165_ = lean_obj_once(&l_Lean_Compiler_LCNF_Arg_inferType___closed__1, &l_Lean_Compiler_LCNF_Arg_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_Arg_inferType___closed__1);
v___x_2166_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2165_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
return v___x_2166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType___boxed(lean_object* v_pu_2167_, lean_object* v_arg_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_){
_start:
{
uint8_t v_pu_boxed_2174_; lean_object* v_res_2175_; 
v_pu_boxed_2174_ = lean_unbox(v_pu_2167_);
v_res_2175_ = l_Lean_Compiler_LCNF_Arg_inferType(v_pu_boxed_2174_, v_arg_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
lean_dec(v_a_2172_);
lean_dec_ref(v_a_2171_);
lean_dec(v_a_2170_);
lean_dec_ref(v_a_2169_);
return v_res_2175_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LetValue_inferType___closed__1(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2177_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2178_ = lean_unsigned_to_nat(15u);
v___x_2179_ = lean_unsigned_to_nat(268u);
v___x_2180_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_inferType___closed__0));
v___x_2181_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2182_ = l_mkPanicMessageWithDecl(v___x_2181_, v___x_2180_, v___x_2179_, v___x_2178_, v___x_2177_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(uint8_t v_pu_2183_, lean_object* v_e_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
if (v_pu_2183_ == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2191_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(v_e_2184_, v___x_2190_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
return v___x_2191_;
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
lean_dec(v_e_2184_);
v___x_2192_ = lean_obj_once(&l_Lean_Compiler_LCNF_LetValue_inferType___closed__1, &l_Lean_Compiler_LCNF_LetValue_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_LetValue_inferType___closed__1);
v___x_2193_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2192_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
return v___x_2193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType___boxed(lean_object* v_pu_2194_, lean_object* v_e_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_){
_start:
{
uint8_t v_pu_boxed_2201_; lean_object* v_res_2202_; 
v_pu_boxed_2201_ = lean_unbox(v_pu_2194_);
v_res_2202_ = l_Lean_Compiler_LCNF_LetValue_inferType(v_pu_boxed_2201_, v_e_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
lean_dec(v_a_2197_);
lean_dec_ref(v_a_2196_);
return v_res_2202_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_inferType___closed__1(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2204_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2205_ = lean_unsigned_to_nat(15u);
v___x_2206_ = lean_unsigned_to_nat(279u);
v___x_2207_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_inferType___closed__0));
v___x_2208_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2209_ = l_mkPanicMessageWithDecl(v___x_2208_, v___x_2207_, v___x_2206_, v___x_2205_, v___x_2204_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t v_pu_2210_, lean_object* v_code_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
if (v_pu_2210_ == 0)
{
switch(lean_obj_tag(v_code_2211_))
{
case 3:
{
lean_object* v_fvarId_2217_; lean_object* v_args_2218_; lean_object* v___x_2219_; 
v_fvarId_2217_ = lean_ctor_get(v_code_2211_, 0);
lean_inc(v_fvarId_2217_);
v_args_2218_ = lean_ctor_get(v_code_2211_, 1);
lean_inc_ref(v_args_2218_);
lean_dec_ref(v_code_2211_);
v___x_2219_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2217_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2220_);
lean_dec_ref(v___x_2219_);
v___x_2221_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2222_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2220_, v_args_2218_, v___x_2221_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
return v___x_2222_;
}
else
{
lean_dec_ref(v_args_2218_);
return v___x_2219_;
}
}
case 4:
{
lean_object* v_cases_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2231_; 
v_cases_2223_ = lean_ctor_get(v_code_2211_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_code_2211_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2225_ = v_code_2211_;
v_isShared_2226_ = v_isSharedCheck_2231_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_cases_2223_);
lean_dec(v_code_2211_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2231_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v_resultType_2227_; lean_object* v___x_2229_; 
v_resultType_2227_ = lean_ctor_get(v_cases_2223_, 1);
lean_inc_ref(v_resultType_2227_);
lean_dec_ref(v_cases_2223_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set_tag(v___x_2225_, 0);
lean_ctor_set(v___x_2225_, 0, v_resultType_2227_);
v___x_2229_ = v___x_2225_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_resultType_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
case 5:
{
lean_object* v_fvarId_2232_; lean_object* v___x_2233_; 
v_fvarId_2232_ = lean_ctor_get(v_code_2211_, 0);
lean_inc(v_fvarId_2232_);
lean_dec_ref(v_code_2211_);
v___x_2233_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2232_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
return v___x_2233_;
}
case 6:
{
lean_object* v_type_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
v_type_2234_ = lean_ctor_get(v_code_2211_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_code_2211_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v_code_2211_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_type_2234_);
lean_dec(v_code_2211_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
lean_ctor_set_tag(v___x_2236_, 0);
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_type_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
default: 
{
lean_object* v_k_2242_; 
v_k_2242_ = lean_ctor_get(v_code_2211_, 1);
lean_inc_ref(v_k_2242_);
lean_dec_ref(v_code_2211_);
v_code_2211_ = v_k_2242_;
goto _start;
}
}
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
lean_dec_ref(v_code_2211_);
v___x_2244_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_inferType___closed__1, &l_Lean_Compiler_LCNF_Code_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_Code_inferType___closed__1);
v___x_2245_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2244_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
return v___x_2245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType___boxed(lean_object* v_pu_2246_, lean_object* v_code_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_){
_start:
{
uint8_t v_pu_boxed_2253_; lean_object* v_res_2254_; 
v_pu_boxed_2253_ = lean_unbox(v_pu_2246_);
v_res_2254_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_boxed_2253_, v_code_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_);
lean_dec(v_a_2251_);
lean_dec_ref(v_a_2250_);
lean_dec(v_a_2249_);
lean_dec_ref(v_a_2248_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg(uint8_t v_pu_2255_, lean_object* v_code_2256_, lean_object* v_h__1_2257_, lean_object* v_h__2_2258_){
_start:
{
if (v_pu_2255_ == 0)
{
lean_object* v___x_2259_; 
lean_dec(v_h__2_2258_);
v___x_2259_ = lean_apply_1(v_h__1_2257_, v_code_2256_);
return v___x_2259_;
}
else
{
lean_object* v___x_2260_; 
lean_dec(v_h__1_2257_);
v___x_2260_ = lean_apply_1(v_h__2_2258_, v_code_2256_);
return v___x_2260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg___boxed(lean_object* v_pu_2261_, lean_object* v_code_2262_, lean_object* v_h__1_2263_, lean_object* v_h__2_2264_){
_start:
{
uint8_t v_pu_32__boxed_2265_; lean_object* v_res_2266_; 
v_pu_32__boxed_2265_ = lean_unbox(v_pu_2261_);
v_res_2266_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg(v_pu_32__boxed_2265_, v_code_2262_, v_h__1_2263_, v_h__2_2264_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter(lean_object* v_motive_2267_, uint8_t v_pu_2268_, lean_object* v_code_2269_, lean_object* v_h__1_2270_, lean_object* v_h__2_2271_){
_start:
{
if (v_pu_2268_ == 0)
{
lean_object* v___x_2272_; 
lean_dec(v_h__2_2271_);
v___x_2272_ = lean_apply_1(v_h__1_2270_, v_code_2269_);
return v___x_2272_;
}
else
{
lean_object* v___x_2273_; 
lean_dec(v_h__1_2270_);
v___x_2273_ = lean_apply_1(v_h__2_2271_, v_code_2269_);
return v___x_2273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___boxed(lean_object* v_motive_2274_, lean_object* v_pu_2275_, lean_object* v_code_2276_, lean_object* v_h__1_2277_, lean_object* v_h__2_2278_){
_start:
{
uint8_t v_pu_39__boxed_2279_; lean_object* v_res_2280_; 
v_pu_39__boxed_2279_ = lean_unbox(v_pu_2275_);
v_res_2280_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter(v_motive_2274_, v_pu_39__boxed_2279_, v_code_2276_, v_h__1_2277_, v_h__2_2278_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__1_splitter___redArg(lean_object* v_code_2281_, lean_object* v_h__1_2282_, lean_object* v_h__2_2283_, lean_object* v_h__3_2284_, lean_object* v_h__4_2285_, lean_object* v_h__5_2286_, lean_object* v_h__6_2287_, lean_object* v_h__7_2288_){
_start:
{
switch(lean_obj_tag(v_code_2281_))
{
case 0:
{
lean_object* v_decl_2289_; lean_object* v_k_2290_; lean_object* v___x_2291_; 
lean_dec(v_h__7_2288_);
lean_dec(v_h__6_2287_);
lean_dec(v_h__5_2286_);
lean_dec(v_h__4_2285_);
lean_dec(v_h__3_2284_);
lean_dec(v_h__2_2283_);
v_decl_2289_ = lean_ctor_get(v_code_2281_, 0);
lean_inc_ref(v_decl_2289_);
v_k_2290_ = lean_ctor_get(v_code_2281_, 1);
lean_inc_ref(v_k_2290_);
lean_dec_ref(v_code_2281_);
v___x_2291_ = lean_apply_2(v_h__1_2282_, v_decl_2289_, v_k_2290_);
return v___x_2291_;
}
case 1:
{
lean_object* v_decl_2292_; lean_object* v_k_2293_; lean_object* v___x_2294_; 
lean_dec(v_h__7_2288_);
lean_dec(v_h__6_2287_);
lean_dec(v_h__5_2286_);
lean_dec(v_h__4_2285_);
lean_dec(v_h__3_2284_);
lean_dec(v_h__1_2282_);
v_decl_2292_ = lean_ctor_get(v_code_2281_, 0);
lean_inc_ref(v_decl_2292_);
v_k_2293_ = lean_ctor_get(v_code_2281_, 1);
lean_inc_ref(v_k_2293_);
lean_dec_ref(v_code_2281_);
v___x_2294_ = lean_apply_3(v_h__2_2283_, v_decl_2292_, v_k_2293_, lean_box(0));
return v___x_2294_;
}
case 2:
{
lean_object* v_decl_2295_; lean_object* v_k_2296_; lean_object* v___x_2297_; 
lean_dec(v_h__7_2288_);
lean_dec(v_h__6_2287_);
lean_dec(v_h__5_2286_);
lean_dec(v_h__4_2285_);
lean_dec(v_h__2_2283_);
lean_dec(v_h__1_2282_);
v_decl_2295_ = lean_ctor_get(v_code_2281_, 0);
lean_inc_ref(v_decl_2295_);
v_k_2296_ = lean_ctor_get(v_code_2281_, 1);
lean_inc_ref(v_k_2296_);
lean_dec_ref(v_code_2281_);
v___x_2297_ = lean_apply_2(v_h__3_2284_, v_decl_2295_, v_k_2296_);
return v___x_2297_;
}
case 3:
{
lean_object* v_fvarId_2298_; lean_object* v_args_2299_; lean_object* v___x_2300_; 
lean_dec(v_h__7_2288_);
lean_dec(v_h__6_2287_);
lean_dec(v_h__4_2285_);
lean_dec(v_h__3_2284_);
lean_dec(v_h__2_2283_);
lean_dec(v_h__1_2282_);
v_fvarId_2298_ = lean_ctor_get(v_code_2281_, 0);
lean_inc(v_fvarId_2298_);
v_args_2299_ = lean_ctor_get(v_code_2281_, 1);
lean_inc_ref(v_args_2299_);
lean_dec_ref(v_code_2281_);
v___x_2300_ = lean_apply_2(v_h__5_2286_, v_fvarId_2298_, v_args_2299_);
return v___x_2300_;
}
case 4:
{
lean_object* v_cases_2301_; lean_object* v___x_2302_; 
lean_dec(v_h__6_2287_);
lean_dec(v_h__5_2286_);
lean_dec(v_h__4_2285_);
lean_dec(v_h__3_2284_);
lean_dec(v_h__2_2283_);
lean_dec(v_h__1_2282_);
v_cases_2301_ = lean_ctor_get(v_code_2281_, 0);
lean_inc_ref(v_cases_2301_);
lean_dec_ref(v_code_2281_);
v___x_2302_ = lean_apply_1(v_h__7_2288_, v_cases_2301_);
return v___x_2302_;
}
case 5:
{
lean_object* v_fvarId_2303_; lean_object* v___x_2304_; 
lean_dec(v_h__7_2288_);
lean_dec(v_h__6_2287_);
lean_dec(v_h__5_2286_);
lean_dec(v_h__3_2284_);
lean_dec(v_h__2_2283_);
lean_dec(v_h__1_2282_);
v_fvarId_2303_ = lean_ctor_get(v_code_2281_, 0);
lean_inc(v_fvarId_2303_);
lean_dec_ref(v_code_2281_);
v___x_2304_ = lean_apply_1(v_h__4_2285_, v_fvarId_2303_);
return v___x_2304_;
}
default: 
{
lean_object* v_type_2305_; lean_object* v___x_2306_; 
lean_dec(v_h__7_2288_);
lean_dec(v_h__5_2286_);
lean_dec(v_h__4_2285_);
lean_dec(v_h__3_2284_);
lean_dec(v_h__2_2283_);
lean_dec(v_h__1_2282_);
v_type_2305_ = lean_ctor_get(v_code_2281_, 0);
lean_inc_ref(v_type_2305_);
lean_dec_ref(v_code_2281_);
v___x_2306_ = lean_apply_1(v_h__6_2287_, v_type_2305_);
return v___x_2306_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__1_splitter(lean_object* v_motive_2307_, lean_object* v_code_2308_, lean_object* v_h__1_2309_, lean_object* v_h__2_2310_, lean_object* v_h__3_2311_, lean_object* v_h__4_2312_, lean_object* v_h__5_2313_, lean_object* v_h__6_2314_, lean_object* v_h__7_2315_){
_start:
{
switch(lean_obj_tag(v_code_2308_))
{
case 0:
{
lean_object* v_decl_2316_; lean_object* v_k_2317_; lean_object* v___x_2318_; 
lean_dec(v_h__7_2315_);
lean_dec(v_h__6_2314_);
lean_dec(v_h__5_2313_);
lean_dec(v_h__4_2312_);
lean_dec(v_h__3_2311_);
lean_dec(v_h__2_2310_);
v_decl_2316_ = lean_ctor_get(v_code_2308_, 0);
lean_inc_ref(v_decl_2316_);
v_k_2317_ = lean_ctor_get(v_code_2308_, 1);
lean_inc_ref(v_k_2317_);
lean_dec_ref(v_code_2308_);
v___x_2318_ = lean_apply_2(v_h__1_2309_, v_decl_2316_, v_k_2317_);
return v___x_2318_;
}
case 1:
{
lean_object* v_decl_2319_; lean_object* v_k_2320_; lean_object* v___x_2321_; 
lean_dec(v_h__7_2315_);
lean_dec(v_h__6_2314_);
lean_dec(v_h__5_2313_);
lean_dec(v_h__4_2312_);
lean_dec(v_h__3_2311_);
lean_dec(v_h__1_2309_);
v_decl_2319_ = lean_ctor_get(v_code_2308_, 0);
lean_inc_ref(v_decl_2319_);
v_k_2320_ = lean_ctor_get(v_code_2308_, 1);
lean_inc_ref(v_k_2320_);
lean_dec_ref(v_code_2308_);
v___x_2321_ = lean_apply_3(v_h__2_2310_, v_decl_2319_, v_k_2320_, lean_box(0));
return v___x_2321_;
}
case 2:
{
lean_object* v_decl_2322_; lean_object* v_k_2323_; lean_object* v___x_2324_; 
lean_dec(v_h__7_2315_);
lean_dec(v_h__6_2314_);
lean_dec(v_h__5_2313_);
lean_dec(v_h__4_2312_);
lean_dec(v_h__2_2310_);
lean_dec(v_h__1_2309_);
v_decl_2322_ = lean_ctor_get(v_code_2308_, 0);
lean_inc_ref(v_decl_2322_);
v_k_2323_ = lean_ctor_get(v_code_2308_, 1);
lean_inc_ref(v_k_2323_);
lean_dec_ref(v_code_2308_);
v___x_2324_ = lean_apply_2(v_h__3_2311_, v_decl_2322_, v_k_2323_);
return v___x_2324_;
}
case 3:
{
lean_object* v_fvarId_2325_; lean_object* v_args_2326_; lean_object* v___x_2327_; 
lean_dec(v_h__7_2315_);
lean_dec(v_h__6_2314_);
lean_dec(v_h__4_2312_);
lean_dec(v_h__3_2311_);
lean_dec(v_h__2_2310_);
lean_dec(v_h__1_2309_);
v_fvarId_2325_ = lean_ctor_get(v_code_2308_, 0);
lean_inc(v_fvarId_2325_);
v_args_2326_ = lean_ctor_get(v_code_2308_, 1);
lean_inc_ref(v_args_2326_);
lean_dec_ref(v_code_2308_);
v___x_2327_ = lean_apply_2(v_h__5_2313_, v_fvarId_2325_, v_args_2326_);
return v___x_2327_;
}
case 4:
{
lean_object* v_cases_2328_; lean_object* v___x_2329_; 
lean_dec(v_h__6_2314_);
lean_dec(v_h__5_2313_);
lean_dec(v_h__4_2312_);
lean_dec(v_h__3_2311_);
lean_dec(v_h__2_2310_);
lean_dec(v_h__1_2309_);
v_cases_2328_ = lean_ctor_get(v_code_2308_, 0);
lean_inc_ref(v_cases_2328_);
lean_dec_ref(v_code_2308_);
v___x_2329_ = lean_apply_1(v_h__7_2315_, v_cases_2328_);
return v___x_2329_;
}
case 5:
{
lean_object* v_fvarId_2330_; lean_object* v___x_2331_; 
lean_dec(v_h__7_2315_);
lean_dec(v_h__6_2314_);
lean_dec(v_h__5_2313_);
lean_dec(v_h__3_2311_);
lean_dec(v_h__2_2310_);
lean_dec(v_h__1_2309_);
v_fvarId_2330_ = lean_ctor_get(v_code_2308_, 0);
lean_inc(v_fvarId_2330_);
lean_dec_ref(v_code_2308_);
v___x_2331_ = lean_apply_1(v_h__4_2312_, v_fvarId_2330_);
return v___x_2331_;
}
default: 
{
lean_object* v_type_2332_; lean_object* v___x_2333_; 
lean_dec(v_h__7_2315_);
lean_dec(v_h__5_2313_);
lean_dec(v_h__4_2312_);
lean_dec(v_h__3_2311_);
lean_dec(v_h__2_2310_);
lean_dec(v_h__1_2309_);
v_type_2332_ = lean_ctor_get(v_code_2308_, 0);
lean_inc_ref(v_type_2332_);
lean_dec_ref(v_code_2308_);
v___x_2333_ = lean_apply_1(v_h__6_2314_, v_type_2332_);
return v___x_2333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(uint8_t v_pu_2334_, lean_object* v_params_2335_, lean_object* v_code_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2334_, v_code_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; size_t v_sz_2344_; size_t v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref(v___x_2342_);
v_sz_2344_ = lean_array_size(v_params_2335_);
v___x_2345_ = ((size_t)0ULL);
v___x_2346_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(v_sz_2344_, v___x_2345_, v_params_2335_);
v___x_2347_ = lean_unsigned_to_nat(32u);
v___x_2348_ = lean_mk_empty_array_with_capacity(v___x_2347_);
lean_dec_ref(v___x_2348_);
v___x_2349_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2350_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v___x_2346_, v_a_2343_, v___x_2349_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v_a_2343_);
lean_dec_ref(v___x_2346_);
return v___x_2350_;
}
else
{
lean_dec_ref(v_params_2335_);
return v___x_2342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType___boxed(lean_object* v_pu_2351_, lean_object* v_params_2352_, lean_object* v_code_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_){
_start:
{
uint8_t v_pu_boxed_2359_; lean_object* v_res_2360_; 
v_pu_boxed_2359_ = lean_unbox(v_pu_2351_);
v_res_2360_ = l_Lean_Compiler_LCNF_Code_inferParamType(v_pu_boxed_2359_, v_params_2352_, v_code_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
lean_dec(v_a_2357_);
lean_dec_ref(v_a_2356_);
lean_dec(v_a_2355_);
lean_dec_ref(v_a_2354_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType(uint8_t v_pu_2361_, lean_object* v_alt_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_){
_start:
{
switch(lean_obj_tag(v_alt_2362_))
{
case 0:
{
lean_object* v_code_2368_; lean_object* v___x_2369_; 
v_code_2368_ = lean_ctor_get(v_alt_2362_, 2);
lean_inc_ref(v_code_2368_);
lean_dec_ref(v_alt_2362_);
v___x_2369_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2361_, v_code_2368_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
return v___x_2369_;
}
case 1:
{
lean_object* v_code_2370_; lean_object* v___x_2371_; 
v_code_2370_ = lean_ctor_get(v_alt_2362_, 1);
lean_inc_ref(v_code_2370_);
lean_dec_ref(v_alt_2362_);
v___x_2371_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2361_, v_code_2370_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
return v___x_2371_;
}
default: 
{
lean_object* v_code_2372_; lean_object* v___x_2373_; 
v_code_2372_ = lean_ctor_get(v_alt_2362_, 0);
lean_inc_ref(v_code_2372_);
lean_dec_ref(v_alt_2362_);
v___x_2373_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2361_, v_code_2372_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
return v___x_2373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType___boxed(lean_object* v_pu_2374_, lean_object* v_alt_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
uint8_t v_pu_boxed_2381_; lean_object* v_res_2382_; 
v_pu_boxed_2381_ = lean_unbox(v_pu_2374_);
v_res_2382_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_boxed_2381_, v_alt_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t v_pu_2383_, lean_object* v_e_2384_, lean_object* v_prefixName_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_prefixName_2385_, v_a_2387_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2393_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref(v___x_2391_);
lean_inc(v_e_2384_);
v___x_2393_ = l_Lean_Compiler_LCNF_LetValue_inferType(v_pu_2383_, v_e_2384_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2395_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref(v___x_2393_);
v___x_2395_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2383_, v_a_2392_, v_a_2394_, v_e_2384_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
return v___x_2395_;
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_dec(v_a_2392_);
lean_dec(v_e_2384_);
v_a_2396_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2393_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2393_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec(v_e_2384_);
v_a_2404_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2391_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2391_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl___boxed(lean_object* v_pu_2412_, lean_object* v_e_2413_, lean_object* v_prefixName_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_){
_start:
{
uint8_t v_pu_boxed_2420_; lean_object* v_res_2421_; 
v_pu_boxed_2420_ = lean_unbox(v_pu_2412_);
v_res_2421_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v_pu_boxed_2420_, v_e_2413_, v_prefixName_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
return v_res_2421_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkForallParams___closed__1(void){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2423_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2424_ = lean_unsigned_to_nat(15u);
v___x_2425_ = lean_unsigned_to_nat(295u);
v___x_2426_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkForallParams___closed__0));
v___x_2427_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2428_ = l_mkPanicMessageWithDecl(v___x_2427_, v___x_2426_, v___x_2425_, v___x_2424_, v___x_2423_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams(uint8_t v_pu_2429_, lean_object* v_params_2430_, lean_object* v_type_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
if (v_pu_2429_ == 0)
{
lean_object* v___x_2437_; 
v___x_2437_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(v_params_2430_, v_type_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
return v___x_2437_;
}
else
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
lean_dec_ref(v_params_2430_);
v___x_2438_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkForallParams___closed__1, &l_Lean_Compiler_LCNF_mkForallParams___closed__1_once, _init_l_Lean_Compiler_LCNF_mkForallParams___closed__1);
v___x_2439_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2438_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
return v___x_2439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams___boxed(lean_object* v_pu_2440_, lean_object* v_params_2441_, lean_object* v_type_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_){
_start:
{
uint8_t v_pu_boxed_2448_; lean_object* v_res_2449_; 
v_pu_boxed_2448_ = lean_unbox(v_pu_2440_);
v_res_2449_ = l_Lean_Compiler_LCNF_mkForallParams(v_pu_boxed_2448_, v_params_2441_, v_type_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_);
lean_dec(v_a_2446_);
lean_dec_ref(v_a_2445_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec_ref(v_type_2442_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(uint8_t v_pu_2450_, lean_object* v_params_2451_, lean_object* v_code_2452_, lean_object* v_prefixName_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v___x_2459_; 
lean_inc_ref(v_code_2452_);
v___x_2459_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2450_, v_code_2452_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v___x_2461_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
lean_dec_ref(v___x_2459_);
lean_inc_ref(v_params_2451_);
v___x_2461_ = l_Lean_Compiler_LCNF_mkForallParams(v_pu_2450_, v_params_2451_, v_a_2460_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_);
lean_dec(v_a_2460_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2463_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_a_2462_);
lean_dec_ref(v___x_2461_);
v___x_2463_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_prefixName_2453_, v_a_2455_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2465_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2464_);
lean_dec_ref(v___x_2463_);
v___x_2465_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_2450_, v_a_2464_, v_a_2462_, v_params_2451_, v_code_2452_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_);
return v___x_2465_;
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec(v_a_2462_);
lean_dec_ref(v_code_2452_);
lean_dec_ref(v_params_2451_);
v_a_2466_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2463_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2463_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec(v_prefixName_2453_);
lean_dec_ref(v_code_2452_);
lean_dec_ref(v_params_2451_);
v_a_2474_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2461_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2461_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_dec(v_prefixName_2453_);
lean_dec_ref(v_code_2452_);
lean_dec_ref(v_params_2451_);
v_a_2482_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2459_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2459_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux___boxed(lean_object* v_pu_2490_, lean_object* v_params_2491_, lean_object* v_code_2492_, lean_object* v_prefixName_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_){
_start:
{
uint8_t v_pu_boxed_2499_; lean_object* v_res_2500_; 
v_pu_boxed_2499_ = lean_unbox(v_pu_2490_);
v_res_2500_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_boxed_2499_, v_params_2491_, v_code_2492_, v_prefixName_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object* v_params_2501_, lean_object* v_code_2502_, lean_object* v_prefixName_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_){
_start:
{
uint8_t v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = 0;
v___x_2510_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v___x_2509_, v_params_2501_, v_code_2502_, v_prefixName_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl___boxed(lean_object* v_params_2511_, lean_object* v_code_2512_, lean_object* v_prefixName_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v_params_2511_, v_code_2512_, v_prefixName_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(uint8_t v_pu_2520_, lean_object* v_params_2521_, lean_object* v_code_2522_, lean_object* v_prefixName_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_2520_, v_params_2521_, v_code_2522_, v_prefixName_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl___boxed(lean_object* v_pu_2530_, lean_object* v_params_2531_, lean_object* v_code_2532_, lean_object* v_prefixName_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_){
_start:
{
uint8_t v_pu_boxed_2539_; lean_object* v_res_2540_; 
v_pu_boxed_2539_ = lean_unbox(v_pu_2530_);
v_res_2540_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v_pu_boxed_2539_, v_params_2531_, v_code_2532_, v_prefixName_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_);
lean_dec(v_a_2537_);
lean_dec_ref(v_a_2536_);
lean_dec(v_a_2535_);
lean_dec_ref(v_a_2534_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(uint8_t v_pu_2541_, lean_object* v_param_2542_, lean_object* v_code_2543_, lean_object* v_prefixName_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v_params_2552_; lean_object* v___x_2553_; 
v___x_2550_ = lean_unsigned_to_nat(1u);
v___x_2551_ = lean_mk_empty_array_with_capacity(v___x_2550_);
v_params_2552_ = lean_array_push(v___x_2551_, v_param_2542_);
v___x_2553_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_2541_, v_params_2552_, v_code_2543_, v_prefixName_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___boxed(lean_object* v_pu_2554_, lean_object* v_param_2555_, lean_object* v_code_2556_, lean_object* v_prefixName_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
uint8_t v_pu_boxed_2563_; lean_object* v_res_2564_; 
v_pu_boxed_2563_ = lean_unbox(v_pu_2554_);
v_res_2564_ = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(v_pu_boxed_2563_, v_param_2555_, v_code_2556_, v_prefixName_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(lean_object* v_msg_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v_options_2571_; lean_object* v_ref_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v_options_2571_ = lean_ctor_get(v___y_2568_, 2);
v_ref_2572_ = lean_ctor_get(v___y_2568_, 5);
v___x_2573_ = lean_st_ref_get(v___y_2569_);
v___x_2574_ = lean_st_ref_get(v___y_2567_);
v___x_2575_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_2566_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2598_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2578_ = v___x_2575_;
v_isShared_2579_ = v_isSharedCheck_2598_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2575_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2598_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v_env_2580_; lean_object* v_lctx_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2596_; 
v_env_2580_ = lean_ctor_get(v___x_2573_, 0);
lean_inc_ref(v_env_2580_);
lean_dec(v___x_2573_);
v_lctx_2581_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2596_ == 0)
{
lean_object* v_unused_2597_; 
v_unused_2597_ = lean_ctor_get(v___x_2574_, 1);
lean_dec(v_unused_2597_);
v___x_2583_ = v___x_2574_;
v_isShared_2584_ = v_isSharedCheck_2596_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_lctx_2581_);
lean_dec(v___x_2574_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2596_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
uint8_t v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2590_; 
v___x_2585_ = lean_unbox(v_a_2576_);
lean_dec(v_a_2576_);
v___x_2586_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2581_, v___x_2585_);
lean_dec_ref(v_lctx_2581_);
v___x_2587_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2);
lean_inc_ref(v_options_2571_);
v___x_2588_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2588_, 0, v_env_2580_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
lean_ctor_set(v___x_2588_, 2, v___x_2586_);
lean_ctor_set(v___x_2588_, 3, v_options_2571_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set_tag(v___x_2583_, 3);
lean_ctor_set(v___x_2583_, 1, v_msg_2565_);
lean_ctor_set(v___x_2583_, 0, v___x_2588_);
v___x_2590_ = v___x_2583_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2588_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v_msg_2565_);
v___x_2590_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
lean_object* v___x_2591_; lean_object* v___x_2593_; 
lean_inc(v_ref_2572_);
v___x_2591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2591_, 0, v_ref_2572_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
if (v_isShared_2579_ == 0)
{
lean_ctor_set_tag(v___x_2578_, 1);
lean_ctor_set(v___x_2578_, 0, v___x_2591_);
v___x_2593_ = v___x_2578_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec(v___x_2574_);
lean_dec(v___x_2573_);
lean_dec_ref(v_msg_2565_);
v_a_2599_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2575_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2575_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg___boxed(lean_object* v_msg_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v_msg_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1(lean_object* v_00_u03b1_2614_, lean_object* v_msg_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v_msg_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___boxed(lean_object* v_00_u03b1_2622_, lean_object* v_msg_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1(v_00_u03b1_2622_, v_msg_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(uint8_t v_pu_2630_, lean_object* v_a_2631_, lean_object* v_b_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v_array_2638_; lean_object* v_start_2639_; lean_object* v_stop_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2656_; 
v_array_2638_ = lean_ctor_get(v_a_2631_, 0);
v_start_2639_ = lean_ctor_get(v_a_2631_, 1);
v_stop_2640_ = lean_ctor_get(v_a_2631_, 2);
v_isSharedCheck_2656_ = !lean_is_exclusive(v_a_2631_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2642_ = v_a_2631_;
v_isShared_2643_ = v_isSharedCheck_2656_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_stop_2640_);
lean_inc(v_start_2639_);
lean_inc(v_array_2638_);
lean_dec(v_a_2631_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2656_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
uint8_t v___x_2644_; 
v___x_2644_ = lean_nat_dec_lt(v_start_2639_, v_stop_2640_);
if (v___x_2644_ == 0)
{
lean_object* v___x_2645_; 
lean_del_object(v___x_2642_);
lean_dec(v_stop_2640_);
lean_dec(v_start_2639_);
lean_dec_ref(v_array_2638_);
v___x_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2645_, 0, v_b_2632_);
return v___x_2645_;
}
else
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2646_ = lean_array_fget_borrowed(v_array_2638_, v_start_2639_);
lean_inc(v___x_2646_);
v___x_2647_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_2630_, v___x_2646_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2652_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref(v___x_2647_);
v___x_2649_ = lean_unsigned_to_nat(1u);
v___x_2650_ = lean_nat_add(v_start_2639_, v___x_2649_);
lean_dec(v_start_2639_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 1, v___x_2650_);
v___x_2652_ = v___x_2642_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_array_2638_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v___x_2650_);
lean_ctor_set(v_reuseFailAlloc_2655_, 2, v_stop_2640_);
v___x_2652_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
lean_object* v___x_2653_; 
v___x_2653_ = l_Lean_Compiler_LCNF_joinTypes(v_b_2632_, v_a_2648_);
v_a_2631_ = v___x_2652_;
v_b_2632_ = v___x_2653_;
goto _start;
}
}
else
{
lean_del_object(v___x_2642_);
lean_dec(v_stop_2640_);
lean_dec(v_start_2639_);
lean_dec_ref(v_array_2638_);
lean_dec_ref(v_b_2632_);
return v___x_2647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg___boxed(lean_object* v_pu_2657_, lean_object* v_a_2658_, lean_object* v_b_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
uint8_t v_pu_boxed_2665_; lean_object* v_res_2666_; 
v_pu_boxed_2665_ = lean_unbox(v_pu_2657_);
v_res_2666_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_boxed_2665_, v_a_2658_, v_b_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
return v_res_2666_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__1(void){
_start:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2668_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkCasesResultType___closed__0));
v___x_2669_ = l_Lean_stringToMessageData(v___x_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(uint8_t v_pu_2670_, lean_object* v_alts_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
lean_object* v___x_2677_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___x_2691_; lean_object* v___x_2692_; uint8_t v___x_2693_; 
v___x_2677_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v_pu_2670_);
v___x_2691_ = lean_array_get_size(v_alts_2671_);
v___x_2692_ = lean_unsigned_to_nat(0u);
v___x_2693_ = lean_nat_dec_eq(v___x_2691_, v___x_2692_);
if (v___x_2693_ == 0)
{
v___y_2679_ = v_a_2672_;
v___y_2680_ = v_a_2673_;
v___y_2681_ = v_a_2674_;
v___y_2682_ = v_a_2675_;
goto v___jp_2678_;
}
else
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec_ref(v___x_2677_);
lean_dec_ref(v_alts_2671_);
v___x_2694_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkCasesResultType___closed__1, &l_Lean_Compiler_LCNF_mkCasesResultType___closed__1_once, _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__1);
v___x_2695_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v___x_2694_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2695_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2695_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
v___jp_2678_:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = lean_unsigned_to_nat(0u);
v___x_2684_ = lean_array_get(v___x_2677_, v_alts_2671_, v___x_2683_);
lean_dec_ref(v___x_2677_);
v___x_2685_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_2670_, v___x_2684_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2686_);
lean_dec_ref(v___x_2685_);
v___x_2687_ = lean_unsigned_to_nat(1u);
v___x_2688_ = lean_array_get_size(v_alts_2671_);
v___x_2689_ = l_Array_toSubarray___redArg(v_alts_2671_, v___x_2687_, v___x_2688_);
v___x_2690_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_2670_, v___x_2689_, v_a_2686_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
return v___x_2690_;
}
else
{
lean_dec_ref(v_alts_2671_);
return v___x_2685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___boxed(lean_object* v_pu_2704_, lean_object* v_alts_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_){
_start:
{
uint8_t v_pu_boxed_2711_; lean_object* v_res_2712_; 
v_pu_boxed_2711_ = lean_unbox(v_pu_2704_);
v_res_2712_ = l_Lean_Compiler_LCNF_mkCasesResultType(v_pu_boxed_2711_, v_alts_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
lean_dec(v_a_2707_);
lean_dec_ref(v_a_2706_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0(uint8_t v_pu_2713_, lean_object* v_inst_2714_, lean_object* v_R_2715_, lean_object* v_a_2716_, lean_object* v_b_2717_, lean_object* v_c_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_2713_, v_a_2716_, v_b_2717_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___boxed(lean_object* v_pu_2725_, lean_object* v_inst_2726_, lean_object* v_R_2727_, lean_object* v_a_2728_, lean_object* v_b_2729_, lean_object* v_c_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
uint8_t v_pu_boxed_2736_; lean_object* v_res_2737_; 
v_pu_boxed_2736_ = lean_unbox(v_pu_2725_);
v_res_2737_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0(v_pu_boxed_2736_, v_inst_2726_, v_R_2727_, v_a_2728_, v_b_2729_, v_c_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(lean_object* v_msg_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v___x_2744_; lean_object* v_toApplicative_2745_; lean_object* v_toFunctor_2746_; lean_object* v_toSeq_2747_; lean_object* v_toSeqLeft_2748_; lean_object* v_toSeqRight_2749_; lean_object* v___f_2750_; lean_object* v___f_2751_; lean_object* v___f_2752_; lean_object* v___f_2753_; lean_object* v___x_2754_; lean_object* v___f_2755_; lean_object* v___f_2756_; lean_object* v___f_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; uint8_t v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___f_2764_; lean_object* v___x_969__overap_2765_; lean_object* v___x_2766_; 
v___x_2744_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_2745_ = lean_ctor_get(v___x_2744_, 0);
v_toFunctor_2746_ = lean_ctor_get(v_toApplicative_2745_, 0);
v_toSeq_2747_ = lean_ctor_get(v_toApplicative_2745_, 2);
v_toSeqLeft_2748_ = lean_ctor_get(v_toApplicative_2745_, 3);
v_toSeqRight_2749_ = lean_ctor_get(v_toApplicative_2745_, 4);
v___f_2750_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_2751_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2746_, 2);
v___f_2752_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2752_, 0, v_toFunctor_2746_);
v___f_2753_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2753_, 0, v_toFunctor_2746_);
v___x_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___f_2752_);
lean_ctor_set(v___x_2754_, 1, v___f_2753_);
lean_inc(v_toSeqRight_2749_);
v___f_2755_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2755_, 0, v_toSeqRight_2749_);
lean_inc(v_toSeqLeft_2748_);
v___f_2756_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2756_, 0, v_toSeqLeft_2748_);
lean_inc(v_toSeq_2747_);
v___f_2757_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2757_, 0, v_toSeq_2747_);
v___x_2758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2754_);
lean_ctor_set(v___x_2758_, 1, v___f_2750_);
lean_ctor_set(v___x_2758_, 2, v___f_2757_);
lean_ctor_set(v___x_2758_, 3, v___f_2756_);
lean_ctor_set(v___x_2758_, 4, v___f_2755_);
v___x_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
lean_ctor_set(v___x_2759_, 1, v___f_2751_);
v___x_2760_ = l_StateRefT_x27_instMonad___redArg(v___x_2759_);
v___x_2761_ = 0;
v___x_2762_ = lean_box(v___x_2761_);
v___x_2763_ = l_instInhabitedOfMonad___redArg(v___x_2760_, v___x_2762_);
v___f_2764_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2764_, 0, v___x_2763_);
v___x_969__overap_2765_ = lean_panic_fn_borrowed(v___f_2764_, v_msg_2738_);
lean_dec_ref(v___f_2764_);
lean_inc(v___y_2742_);
lean_inc_ref(v___y_2741_);
lean_inc(v___y_2740_);
lean_inc_ref(v___y_2739_);
v___x_2766_ = lean_apply_5(v___x_969__overap_2765_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, lean_box(0));
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0___boxed(lean_object* v_msg_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(v_msg_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
return v_res_2773_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1(void){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2775_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2));
v___x_2776_ = lean_unsigned_to_nat(50u);
v___x_2777_ = lean_unsigned_to_nat(345u);
v___x_2778_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__0));
v___x_2779_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2780_ = l_mkPanicMessageWithDecl(v___x_2779_, v___x_2778_, v___x_2777_, v___x_2776_, v___x_2775_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(lean_object* v_type_2781_, lean_object* v_predVars_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v_t_2789_; lean_object* v_b_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v_type_2799_; 
v_type_2799_ = l_Lean_Expr_headBeta(v_type_2781_);
switch(lean_obj_tag(v_type_2799_))
{
case 0:
{
lean_object* v_deBruijnIndex_2800_; uint8_t v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v_deBruijnIndex_2800_ = lean_ctor_get(v_type_2799_, 0);
lean_inc(v_deBruijnIndex_2800_);
lean_dec_ref(v_type_2799_);
v___x_2801_ = 0;
v___x_2802_ = lean_array_get_size(v_predVars_2782_);
v___x_2803_ = lean_nat_sub(v___x_2802_, v_deBruijnIndex_2800_);
lean_dec(v_deBruijnIndex_2800_);
v___x_2804_ = lean_unsigned_to_nat(1u);
v___x_2805_ = lean_nat_sub(v___x_2803_, v___x_2804_);
lean_dec(v___x_2803_);
v___x_2806_ = lean_box(v___x_2801_);
v___x_2807_ = lean_array_get(v___x_2806_, v_predVars_2782_, v___x_2805_);
lean_dec(v___x_2805_);
lean_dec_ref(v_predVars_2782_);
lean_dec(v___x_2806_);
v___x_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
return v___x_2808_;
}
case 1:
{
lean_object* v_fvarId_2809_; lean_object* v___x_2810_; 
lean_dec_ref(v_predVars_2782_);
v_fvarId_2809_ = lean_ctor_get(v_type_2799_, 0);
lean_inc(v_fvarId_2809_);
lean_dec_ref(v_type_2799_);
v___x_2810_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2809_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2820_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2813_ = v___x_2810_;
v_isShared_2814_ = v_isSharedCheck_2820_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2810_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2820_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
uint8_t v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2818_; 
v___x_2815_ = l_Lean_Compiler_LCNF_isPredicateType(v_a_2811_);
v___x_2816_ = lean_box(v___x_2815_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 0, v___x_2816_);
v___x_2818_ = v___x_2813_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2816_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
else
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2828_; 
v_a_2821_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2823_ = v___x_2810_;
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2810_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2824_ == 0)
{
v___x_2826_ = v___x_2823_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2821_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
case 3:
{
uint8_t v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
lean_dec_ref(v_type_2799_);
lean_dec_ref(v_predVars_2782_);
v___x_2829_ = 0;
v___x_2830_ = lean_box(v___x_2829_);
v___x_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
return v___x_2831_;
}
case 4:
{
uint8_t v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
lean_dec_ref(v_predVars_2782_);
v___x_2832_ = l_Lean_Expr_isErased(v_type_2799_);
lean_dec_ref(v_type_2799_);
v___x_2833_ = lean_box(v___x_2832_);
v___x_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2833_);
return v___x_2834_;
}
case 5:
{
lean_object* v_fn_2835_; 
v_fn_2835_ = lean_ctor_get(v_type_2799_, 0);
lean_inc_ref(v_fn_2835_);
lean_dec_ref(v_type_2799_);
v_type_2781_ = v_fn_2835_;
goto _start;
}
case 6:
{
lean_object* v_binderType_2837_; lean_object* v_body_2838_; 
v_binderType_2837_ = lean_ctor_get(v_type_2799_, 1);
lean_inc_ref(v_binderType_2837_);
v_body_2838_ = lean_ctor_get(v_type_2799_, 2);
lean_inc_ref(v_body_2838_);
lean_dec_ref(v_type_2799_);
v_t_2789_ = v_binderType_2837_;
v_b_2790_ = v_body_2838_;
v___y_2791_ = v_a_2783_;
v___y_2792_ = v_a_2784_;
v___y_2793_ = v_a_2785_;
v___y_2794_ = v_a_2786_;
goto v___jp_2788_;
}
case 7:
{
lean_object* v_binderType_2839_; lean_object* v_body_2840_; 
v_binderType_2839_ = lean_ctor_get(v_type_2799_, 1);
lean_inc_ref(v_binderType_2839_);
v_body_2840_ = lean_ctor_get(v_type_2799_, 2);
lean_inc_ref(v_body_2840_);
lean_dec_ref(v_type_2799_);
v_t_2789_ = v_binderType_2839_;
v_b_2790_ = v_body_2840_;
v___y_2791_ = v_a_2783_;
v___y_2792_ = v_a_2784_;
v___y_2793_ = v_a_2785_;
v___y_2794_ = v_a_2786_;
goto v___jp_2788_;
}
case 10:
{
lean_object* v_expr_2841_; 
v_expr_2841_ = lean_ctor_get(v_type_2799_, 1);
lean_inc_ref(v_expr_2841_);
lean_dec_ref(v_type_2799_);
v_type_2781_ = v_expr_2841_;
goto _start;
}
default: 
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
lean_dec_ref(v_type_2799_);
lean_dec_ref(v_predVars_2782_);
v___x_2843_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1, &l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1);
v___x_2844_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(v___x_2843_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
return v___x_2844_;
}
}
v___jp_2788_:
{
uint8_t v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2795_ = l_Lean_Compiler_LCNF_isPredicateType(v_t_2789_);
v___x_2796_ = lean_box(v___x_2795_);
v___x_2797_ = lean_array_push(v_predVars_2782_, v___x_2796_);
v_type_2781_ = v_b_2790_;
v_predVars_2782_ = v___x_2797_;
v_a_2783_ = v___y_2791_;
v_a_2784_ = v___y_2792_;
v_a_2785_ = v___y_2793_;
v_a_2786_ = v___y_2794_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___boxed(lean_object* v_type_2845_, lean_object* v_predVars_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(v_type_2845_, v_predVars_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible(lean_object* v_type_2853_, lean_object* v_predVars_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v___x_2860_; 
v___x_2860_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(v_type_2853_, v_predVars_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible___boxed(lean_object* v_type_2861_, lean_object* v_predVars_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l_Lean_Compiler_LCNF_isErasedCompatible(v_type_2861_, v_predVars_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_);
lean_dec(v_a_2866_);
lean_dec_ref(v_a_2865_);
lean_dec(v_a_2864_);
lean_dec_ref(v_a_2863_);
return v_res_2868_;
}
}
LEAN_EXPORT uint8_t l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(lean_object* v_x_2869_, lean_object* v_x_2870_){
_start:
{
if (lean_obj_tag(v_x_2869_) == 0)
{
if (lean_obj_tag(v_x_2870_) == 0)
{
uint8_t v___x_2871_; 
v___x_2871_ = 1;
return v___x_2871_;
}
else
{
uint8_t v___x_2872_; 
v___x_2872_ = 0;
return v___x_2872_;
}
}
else
{
if (lean_obj_tag(v_x_2870_) == 0)
{
uint8_t v___x_2873_; 
v___x_2873_ = 0;
return v___x_2873_;
}
else
{
lean_object* v_head_2874_; lean_object* v_tail_2875_; lean_object* v_head_2876_; lean_object* v_tail_2877_; uint8_t v___x_2878_; 
v_head_2874_ = lean_ctor_get(v_x_2869_, 0);
v_tail_2875_ = lean_ctor_get(v_x_2869_, 1);
v_head_2876_ = lean_ctor_get(v_x_2870_, 0);
v_tail_2877_ = lean_ctor_get(v_x_2870_, 1);
v___x_2878_ = l_Lean_Level_isEquiv(v_head_2874_, v_head_2876_);
if (v___x_2878_ == 0)
{
return v___x_2878_;
}
else
{
v_x_2869_ = v_tail_2875_;
v_x_2870_ = v_tail_2877_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0___boxed(lean_object* v_x_2880_, lean_object* v_x_2881_){
_start:
{
uint8_t v_res_2882_; lean_object* v_r_2883_; 
v_res_2882_ = l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(v_x_2880_, v_x_2881_);
lean_dec(v_x_2881_);
lean_dec(v_x_2880_);
v_r_2883_ = lean_box(v_res_2882_);
return v_r_2883_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_eqvTypes(lean_object* v_a_2884_, lean_object* v_b_2885_){
_start:
{
lean_object* v_d_u2081_2887_; lean_object* v_b_u2081_2888_; lean_object* v_d_u2082_2889_; lean_object* v_b_u2082_2890_; uint8_t v___x_2893_; uint8_t v___x_2894_; uint8_t v___y_2896_; 
v___x_2893_ = lean_expr_eqv(v_a_2884_, v_b_2885_);
v___x_2894_ = 1;
if (v___x_2893_ == 0)
{
uint8_t v___x_2940_; 
v___x_2940_ = l_Lean_Expr_isErased(v_a_2884_);
if (v___x_2940_ == 0)
{
v___y_2896_ = v___x_2940_;
goto v___jp_2895_;
}
else
{
uint8_t v___x_2941_; 
v___x_2941_ = l_Lean_Expr_isErased(v_b_2885_);
v___y_2896_ = v___x_2941_;
goto v___jp_2895_;
}
}
else
{
lean_dec_ref(v_b_2885_);
lean_dec_ref(v_a_2884_);
return v___x_2894_;
}
v___jp_2886_:
{
uint8_t v___x_2891_; 
v___x_2891_ = l_Lean_Compiler_LCNF_eqvTypes(v_d_u2081_2887_, v_d_u2082_2889_);
if (v___x_2891_ == 0)
{
lean_dec_ref(v_b_u2082_2890_);
lean_dec_ref(v_b_u2081_2888_);
return v___x_2891_;
}
else
{
v_a_2884_ = v_b_u2081_2888_;
v_b_2885_ = v_b_u2082_2890_;
goto _start;
}
}
v___jp_2895_:
{
if (v___y_2896_ == 0)
{
lean_object* v_a_x27_2897_; lean_object* v_b_x27_2898_; uint8_t v___x_2899_; 
lean_inc_ref(v_a_2884_);
v_a_x27_2897_ = l_Lean_Expr_headBeta(v_a_2884_);
lean_inc_ref(v_b_2885_);
v_b_x27_2898_ = l_Lean_Expr_headBeta(v_b_2885_);
v___x_2899_ = lean_expr_eqv(v_a_2884_, v_a_x27_2897_);
if (v___x_2899_ == 0)
{
lean_dec_ref(v_b_2885_);
lean_dec_ref(v_a_2884_);
v_a_2884_ = v_a_x27_2897_;
v_b_2885_ = v_b_x27_2898_;
goto _start;
}
else
{
uint8_t v___x_2901_; 
v___x_2901_ = lean_expr_eqv(v_b_2885_, v_b_x27_2898_);
if (v___x_2901_ == 0)
{
lean_dec_ref(v_b_2885_);
lean_dec_ref(v_a_2884_);
v_a_2884_ = v_a_x27_2897_;
v_b_2885_ = v_b_x27_2898_;
goto _start;
}
else
{
lean_dec_ref(v_b_x27_2898_);
lean_dec_ref(v_a_x27_2897_);
switch(lean_obj_tag(v_a_2884_))
{
case 10:
{
lean_object* v_expr_2903_; 
v_expr_2903_ = lean_ctor_get(v_a_2884_, 1);
lean_inc_ref(v_expr_2903_);
lean_dec_ref(v_a_2884_);
v_a_2884_ = v_expr_2903_;
goto _start;
}
case 5:
{
switch(lean_obj_tag(v_b_2885_))
{
case 10:
{
lean_object* v_expr_2905_; 
v_expr_2905_ = lean_ctor_get(v_b_2885_, 1);
lean_inc_ref(v_expr_2905_);
lean_dec_ref(v_b_2885_);
v_b_2885_ = v_expr_2905_;
goto _start;
}
case 5:
{
lean_object* v_fn_2907_; lean_object* v_arg_2908_; lean_object* v_fn_2909_; lean_object* v_arg_2910_; uint8_t v___x_2911_; 
v_fn_2907_ = lean_ctor_get(v_a_2884_, 0);
lean_inc_ref(v_fn_2907_);
v_arg_2908_ = lean_ctor_get(v_a_2884_, 1);
lean_inc_ref(v_arg_2908_);
lean_dec_ref(v_a_2884_);
v_fn_2909_ = lean_ctor_get(v_b_2885_, 0);
lean_inc_ref(v_fn_2909_);
v_arg_2910_ = lean_ctor_get(v_b_2885_, 1);
lean_inc_ref(v_arg_2910_);
lean_dec_ref(v_b_2885_);
v___x_2911_ = l_Lean_Compiler_LCNF_eqvTypes(v_fn_2907_, v_fn_2909_);
if (v___x_2911_ == 0)
{
lean_dec_ref(v_arg_2910_);
lean_dec_ref(v_arg_2908_);
return v___x_2911_;
}
else
{
v_a_2884_ = v_arg_2908_;
v_b_2885_ = v_arg_2910_;
goto _start;
}
}
default: 
{
lean_dec_ref(v_a_2884_);
lean_dec_ref(v_b_2885_);
return v___y_2896_;
}
}
}
case 7:
{
switch(lean_obj_tag(v_b_2885_))
{
case 10:
{
lean_object* v_expr_2913_; 
v_expr_2913_ = lean_ctor_get(v_b_2885_, 1);
lean_inc_ref(v_expr_2913_);
lean_dec_ref(v_b_2885_);
v_b_2885_ = v_expr_2913_;
goto _start;
}
case 7:
{
lean_object* v_binderType_2915_; lean_object* v_body_2916_; lean_object* v_binderType_2917_; lean_object* v_body_2918_; 
v_binderType_2915_ = lean_ctor_get(v_a_2884_, 1);
lean_inc_ref(v_binderType_2915_);
v_body_2916_ = lean_ctor_get(v_a_2884_, 2);
lean_inc_ref(v_body_2916_);
lean_dec_ref(v_a_2884_);
v_binderType_2917_ = lean_ctor_get(v_b_2885_, 1);
lean_inc_ref(v_binderType_2917_);
v_body_2918_ = lean_ctor_get(v_b_2885_, 2);
lean_inc_ref(v_body_2918_);
lean_dec_ref(v_b_2885_);
v_d_u2081_2887_ = v_binderType_2915_;
v_b_u2081_2888_ = v_body_2916_;
v_d_u2082_2889_ = v_binderType_2917_;
v_b_u2082_2890_ = v_body_2918_;
goto v___jp_2886_;
}
default: 
{
lean_dec_ref(v_a_2884_);
lean_dec_ref(v_b_2885_);
return v___y_2896_;
}
}
}
case 6:
{
switch(lean_obj_tag(v_b_2885_))
{
case 10:
{
lean_object* v_expr_2919_; 
v_expr_2919_ = lean_ctor_get(v_b_2885_, 1);
lean_inc_ref(v_expr_2919_);
lean_dec_ref(v_b_2885_);
v_b_2885_ = v_expr_2919_;
goto _start;
}
case 6:
{
lean_object* v_binderType_2921_; lean_object* v_body_2922_; lean_object* v_binderType_2923_; lean_object* v_body_2924_; 
v_binderType_2921_ = lean_ctor_get(v_a_2884_, 1);
lean_inc_ref(v_binderType_2921_);
v_body_2922_ = lean_ctor_get(v_a_2884_, 2);
lean_inc_ref(v_body_2922_);
lean_dec_ref(v_a_2884_);
v_binderType_2923_ = lean_ctor_get(v_b_2885_, 1);
lean_inc_ref(v_binderType_2923_);
v_body_2924_ = lean_ctor_get(v_b_2885_, 2);
lean_inc_ref(v_body_2924_);
lean_dec_ref(v_b_2885_);
v_d_u2081_2887_ = v_binderType_2921_;
v_b_u2081_2888_ = v_body_2922_;
v_d_u2082_2889_ = v_binderType_2923_;
v_b_u2082_2890_ = v_body_2924_;
goto v___jp_2886_;
}
default: 
{
lean_dec_ref(v_a_2884_);
lean_dec_ref(v_b_2885_);
return v___y_2896_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_b_2885_))
{
case 10:
{
lean_object* v_expr_2925_; 
v_expr_2925_ = lean_ctor_get(v_b_2885_, 1);
lean_inc_ref(v_expr_2925_);
lean_dec_ref(v_b_2885_);
v_b_2885_ = v_expr_2925_;
goto _start;
}
case 3:
{
lean_object* v_u_2927_; lean_object* v_u_2928_; uint8_t v___x_2929_; 
v_u_2927_ = lean_ctor_get(v_a_2884_, 0);
lean_inc(v_u_2927_);
lean_dec_ref(v_a_2884_);
v_u_2928_ = lean_ctor_get(v_b_2885_, 0);
lean_inc(v_u_2928_);
lean_dec_ref(v_b_2885_);
v___x_2929_ = l_Lean_Level_isEquiv(v_u_2927_, v_u_2928_);
lean_dec(v_u_2928_);
lean_dec(v_u_2927_);
return v___x_2929_;
}
default: 
{
lean_dec_ref(v_a_2884_);
lean_dec_ref(v_b_2885_);
return v___y_2896_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_b_2885_))
{
case 10:
{
lean_object* v_expr_2930_; 
v_expr_2930_ = lean_ctor_get(v_b_2885_, 1);
lean_inc_ref(v_expr_2930_);
lean_dec_ref(v_b_2885_);
v_b_2885_ = v_expr_2930_;
goto _start;
}
case 4:
{
lean_object* v_declName_2932_; lean_object* v_us_2933_; lean_object* v_declName_2934_; lean_object* v_us_2935_; uint8_t v___x_2936_; 
v_declName_2932_ = lean_ctor_get(v_a_2884_, 0);
lean_inc(v_declName_2932_);
v_us_2933_ = lean_ctor_get(v_a_2884_, 1);
lean_inc(v_us_2933_);
lean_dec_ref(v_a_2884_);
v_declName_2934_ = lean_ctor_get(v_b_2885_, 0);
lean_inc(v_declName_2934_);
v_us_2935_ = lean_ctor_get(v_b_2885_, 1);
lean_inc(v_us_2935_);
lean_dec_ref(v_b_2885_);
v___x_2936_ = lean_name_eq(v_declName_2932_, v_declName_2934_);
lean_dec(v_declName_2934_);
lean_dec(v_declName_2932_);
if (v___x_2936_ == 0)
{
lean_dec(v_us_2935_);
lean_dec(v_us_2933_);
return v___x_2936_;
}
else
{
uint8_t v___x_2937_; 
v___x_2937_ = l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(v_us_2933_, v_us_2935_);
lean_dec(v_us_2935_);
lean_dec(v_us_2933_);
return v___x_2937_;
}
}
default: 
{
lean_dec_ref(v_a_2884_);
lean_dec_ref(v_b_2885_);
return v___y_2896_;
}
}
}
default: 
{
if (lean_obj_tag(v_b_2885_) == 10)
{
lean_object* v_expr_2938_; 
v_expr_2938_ = lean_ctor_get(v_b_2885_, 1);
lean_inc_ref(v_expr_2938_);
lean_dec_ref(v_b_2885_);
v_b_2885_ = v_expr_2938_;
goto _start;
}
else
{
lean_dec_ref(v_b_2885_);
lean_dec_ref(v_a_2884_);
return v___y_2896_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_b_2885_);
lean_dec_ref(v_a_2884_);
return v___x_2894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eqvTypes___boxed(lean_object* v_a_2942_, lean_object* v_b_2943_){
_start:
{
uint8_t v_res_2944_; lean_object* v_r_2945_; 
v_res_2944_ = l_Lean_Compiler_LCNF_eqvTypes(v_a_2942_, v_b_2943_);
v_r_2945_ = lean_box(v_res_2944_);
return v_r_2945_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_OtherDecl(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
