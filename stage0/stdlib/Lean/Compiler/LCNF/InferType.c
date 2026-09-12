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
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshFVarId___redArg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
static lean_once_cell_t l_Lean_Compiler_LCNF_mkCasesResultType___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__0;
static const lean_string_object l_Lean_Compiler_LCNF_mkCasesResultType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`Code.bind` failed, empty `cases` found"};
static const lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_mkCasesResultType___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkCasesResultType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__2;
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
v___x_160_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
v___x_214_ = l_instMonadEIO___redArg();
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
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_198__overap_284_; lean_object* v___x_285_; 
v___x_282_ = l_ReaderT_instMonad___redArg(v___x_281_);
v___x_283_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10);
v___x_198__overap_284_ = l_Lean_mkFreshFVarId___redArg(v___x_282_, v___x_283_);
lean_inc(v_a_240_);
lean_inc_ref(v_a_239_);
lean_inc(v_a_238_);
lean_inc_ref(v_a_237_);
lean_inc_ref(v_a_236_);
v___x_285_ = lean_apply_6(v___x_198__overap_284_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, lean_box(0));
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
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_232__overap_370_; lean_object* v___x_371_; 
v___x_368_ = l_ReaderT_instMonad___redArg(v___x_367_);
v___x_369_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10);
v___x_232__overap_370_ = l_Lean_mkFreshFVarId___redArg(v___x_368_, v___x_369_);
lean_inc(v_a_326_);
lean_inc_ref(v_a_325_);
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
lean_inc_ref(v_a_322_);
v___x_371_ = lean_apply_6(v___x_232__overap_370_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, lean_box(0));
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
lean_object* v_r_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
lean_inc(v_idx_514_);
lean_inc(v_namePrefix_513_);
v_r_518_ = l_Lean_Name_num___override(v_namePrefix_513_, v_idx_514_);
v___x_519_ = lean_unsigned_to_nat(1u);
v___x_520_ = lean_nat_add(v_idx_514_, v___x_519_);
lean_dec(v_idx_514_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v___x_520_);
v___x_522_ = v___x_516_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_namePrefix_513_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v___x_520_);
v___x_522_ = v_reuseFailAlloc_542_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v_env_524_; lean_object* v_nextMacroScope_525_; lean_object* v_auxDeclNGen_526_; lean_object* v_traceState_527_; lean_object* v_cache_528_; lean_object* v_messages_529_; lean_object* v_infoState_530_; lean_object* v_snapshotTasks_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_540_; 
v___x_523_ = lean_st_ref_take(v___y_509_);
v_env_524_ = lean_ctor_get(v___x_523_, 0);
v_nextMacroScope_525_ = lean_ctor_get(v___x_523_, 1);
v_auxDeclNGen_526_ = lean_ctor_get(v___x_523_, 3);
v_traceState_527_ = lean_ctor_get(v___x_523_, 4);
v_cache_528_ = lean_ctor_get(v___x_523_, 5);
v_messages_529_ = lean_ctor_get(v___x_523_, 6);
v_infoState_530_ = lean_ctor_get(v___x_523_, 7);
v_snapshotTasks_531_ = lean_ctor_get(v___x_523_, 8);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_540_ == 0)
{
lean_object* v_unused_541_; 
v_unused_541_ = lean_ctor_get(v___x_523_, 2);
lean_dec(v_unused_541_);
v___x_533_ = v___x_523_;
v_isShared_534_ = v_isSharedCheck_540_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_snapshotTasks_531_);
lean_inc(v_infoState_530_);
lean_inc(v_messages_529_);
lean_inc(v_cache_528_);
lean_inc(v_traceState_527_);
lean_inc(v_auxDeclNGen_526_);
lean_inc(v_nextMacroScope_525_);
lean_inc(v_env_524_);
lean_dec(v___x_523_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_540_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 2, v___x_522_);
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_env_524_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_nextMacroScope_525_);
lean_ctor_set(v_reuseFailAlloc_539_, 2, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_539_, 3, v_auxDeclNGen_526_);
lean_ctor_set(v_reuseFailAlloc_539_, 4, v_traceState_527_);
lean_ctor_set(v_reuseFailAlloc_539_, 5, v_cache_528_);
lean_ctor_set(v_reuseFailAlloc_539_, 6, v_messages_529_);
lean_ctor_set(v_reuseFailAlloc_539_, 7, v_infoState_530_);
lean_ctor_set(v_reuseFailAlloc_539_, 8, v_snapshotTasks_531_);
v___x_536_ = v_reuseFailAlloc_539_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_st_ref_put(v___y_509_, v___x_536_);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v_r_518_);
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
lean_object* v_j_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v_j_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = l_Lean_Expr_getAppFn(v_e_669_);
v___x_678_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v___x_677_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v_dummy_680_; lean_object* v_nargs_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_a_679_);
lean_dec_ref_known(v___x_678_, 1);
v_dummy_680_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0);
v_nargs_681_ = l_Lean_Expr_getAppNumArgs(v_e_669_);
lean_inc(v_nargs_681_);
v___x_682_ = lean_mk_array(v_nargs_681_, v_dummy_680_);
v___x_683_ = lean_unsigned_to_nat(1u);
v___x_684_ = lean_nat_sub(v_nargs_681_, v___x_683_);
lean_dec(v_nargs_681_);
v___x_685_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_669_, v___x_682_, v___x_684_);
v___x_686_ = lean_array_get_size(v___x_685_);
v___x_687_ = lean_box(0);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v_j_676_);
lean_ctor_set(v___x_688_, 1, v_a_679_);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v___x_686_, v___x_685_, v_j_676_, v___x_689_);
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
v___x_699_ = lean_expr_instantiate_rev_range(v_snd_698_, v_fst_697_, v___x_686_, v___x_685_);
lean_dec_ref(v___x_685_);
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
lean_dec_ref(v___x_685_);
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
lean_dec_ref(v___x_685_);
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
return v___x_678_;
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
lean_object* v_binderName_726_; lean_object* v_binderType_727_; lean_object* v_body_728_; uint8_t v_binderInfo_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_binderName_726_ = lean_ctor_get(v_e_717_, 0);
lean_inc(v_binderName_726_);
v_binderType_727_ = lean_ctor_get(v_e_717_, 1);
lean_inc_ref(v_binderType_727_);
v_body_728_ = lean_ctor_get(v_e_717_, 2);
lean_inc_ref(v_body_728_);
v_binderInfo_729_ = lean_ctor_get_uint8(v_e_717_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_717_, 3);
v___x_730_ = lean_expr_instantiate_rev(v_binderType_727_, v_all_719_);
lean_dec_ref(v_binderType_727_);
v___x_731_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_733_; uint8_t v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc_n(v_a_732_, 2);
lean_dec_ref_known(v___x_731_, 1);
v___x_733_ = l_Lean_Expr_fvar___override(v_a_732_);
v___x_734_ = 0;
v___x_735_ = l_Lean_LocalContext_mkLocalDecl(v_a_720_, v_a_732_, v_binderName_726_, v___x_730_, v_binderInfo_729_, v___x_734_);
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
lean_dec_ref(v___x_730_);
lean_dec_ref(v_body_728_);
lean_dec(v_binderName_726_);
lean_dec_ref(v_a_720_);
lean_dec_ref(v_all_719_);
lean_dec_ref(v_fvars_718_);
v_a_739_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_731_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_731_);
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
lean_object* v_declName_747_; lean_object* v_type_748_; lean_object* v_body_749_; lean_object* v___x_750_; uint8_t v___x_751_; lean_object* v___x_752_; 
v_declName_747_ = lean_ctor_get(v_e_717_, 0);
lean_inc(v_declName_747_);
v_type_748_ = lean_ctor_get(v_e_717_, 1);
lean_inc_ref(v_type_748_);
v_body_749_ = lean_ctor_get(v_e_717_, 3);
lean_inc_ref(v_body_749_);
lean_dec_ref_known(v_e_717_, 4);
v___x_750_ = lean_expr_instantiate_rev(v_type_748_, v_all_719_);
lean_dec_ref(v_type_748_);
v___x_751_ = 0;
v___x_752_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_754_; uint8_t v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc_n(v_a_753_, 2);
lean_dec_ref_known(v___x_752_, 1);
v___x_754_ = l_Lean_Expr_fvar___override(v_a_753_);
v___x_755_ = 0;
v___x_756_ = l_Lean_LocalContext_mkLocalDecl(v_a_720_, v_a_753_, v_declName_747_, v___x_750_, v___x_751_, v___x_755_);
v___x_757_ = lean_array_push(v_all_719_, v___x_754_);
v_e_717_ = v_body_749_;
v_all_719_ = v___x_757_;
v_a_720_ = v___x_756_;
goto _start;
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec_ref(v___x_750_);
lean_dec_ref(v_body_749_);
lean_dec(v_declName_747_);
lean_dec_ref(v_a_720_);
lean_dec_ref(v_all_719_);
lean_dec_ref(v_fvars_718_);
v_a_759_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_752_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_752_);
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
lean_object* v_snd_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_899_; 
v_snd_854_ = lean_ctor_get(v_b_845_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_b_845_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; 
v_unused_900_ = lean_ctor_get(v_b_845_, 0);
lean_dec(v_unused_900_);
v___x_856_ = v_b_845_;
v_isShared_857_ = v_isSharedCheck_899_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_snd_854_);
lean_dec(v_b_845_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_899_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v_a_859_; lean_object* v___x_860_; 
v___x_858_ = lean_box(0);
v_a_859_ = lean_array_uget_borrowed(v_as_842_, v_i_844_);
lean_inc(v_a_859_);
v___x_860_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_a_859_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_862_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 1);
v___x_862_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(v_a_861_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_882_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_882_ == 0)
{
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_882_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_882_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
if (lean_obj_tag(v_a_863_) == 1)
{
lean_object* v_val_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
lean_del_object(v___x_865_);
v_val_867_ = lean_ctor_get(v_a_863_, 0);
lean_inc(v_val_867_);
lean_dec_ref_known(v_a_863_, 1);
v___x_868_ = l_Lean_mkLevelIMax_x27(v_val_867_, v_snd_854_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 1, v___x_868_);
lean_ctor_set(v___x_856_, 0, v___x_858_);
v___x_870_ = v___x_856_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_858_);
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
else
{
lean_object* v___x_875_; lean_object* v___x_877_; 
lean_dec(v_a_863_);
v___x_875_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_875_);
v___x_877_ = v___x_856_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_snd_854_);
v___x_877_ = v_reuseFailAlloc_881_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_879_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_877_);
v___x_879_ = v___x_865_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_del_object(v___x_856_);
lean_dec(v_snd_854_);
v_a_883_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_862_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_862_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_del_object(v___x_856_);
lean_dec(v_snd_854_);
v_a_891_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_860_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_860_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(lean_object* v_e_901_, lean_object* v_fvars_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
if (lean_obj_tag(v_e_901_) == 7)
{
lean_object* v_binderName_909_; lean_object* v_binderType_910_; lean_object* v_body_911_; uint8_t v_binderInfo_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_binderName_909_ = lean_ctor_get(v_e_901_, 0);
lean_inc(v_binderName_909_);
v_binderType_910_ = lean_ctor_get(v_e_901_, 1);
lean_inc_ref(v_binderType_910_);
v_body_911_ = lean_ctor_get(v_e_901_, 2);
lean_inc_ref(v_body_911_);
v_binderInfo_912_ = lean_ctor_get_uint8(v_e_901_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_901_, 3);
v___x_913_ = lean_expr_instantiate_rev(v_binderType_910_, v_fvars_902_);
lean_dec_ref(v_binderType_910_);
v___x_914_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_916_; uint8_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc_n(v_a_915_, 2);
lean_dec_ref_known(v___x_914_, 1);
v___x_916_ = l_Lean_Expr_fvar___override(v_a_915_);
v___x_917_ = 0;
v___x_918_ = l_Lean_LocalContext_mkLocalDecl(v_a_903_, v_a_915_, v_binderName_909_, v___x_913_, v_binderInfo_912_, v___x_917_);
v___x_919_ = lean_array_push(v_fvars_902_, v___x_916_);
v_e_901_ = v_body_911_;
v_fvars_902_ = v___x_919_;
v_a_903_ = v___x_918_;
goto _start;
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec_ref(v___x_913_);
lean_dec_ref(v_body_911_);
lean_dec(v_binderName_909_);
lean_dec_ref(v_a_903_);
lean_dec_ref(v_fvars_902_);
v_a_921_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_914_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_914_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
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
else
{
lean_object* v_e_929_; lean_object* v___x_930_; 
v_e_929_ = lean_expr_instantiate_rev(v_e_901_, v_fvars_902_);
lean_dec_ref(v_e_901_);
v___x_930_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(v_e_929_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_970_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_970_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_970_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_970_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
if (lean_obj_tag(v_a_931_) == 1)
{
lean_object* v_val_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; size_t v_sz_939_; size_t v___x_940_; lean_object* v___x_941_; 
lean_del_object(v___x_933_);
v_val_935_ = lean_ctor_get(v_a_931_, 0);
lean_inc(v_val_935_);
lean_dec_ref_known(v_a_931_, 1);
v___x_936_ = l_Array_reverse___redArg(v_fvars_902_);
v___x_937_ = lean_box(0);
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v_val_935_);
v_sz_939_ = lean_array_size(v___x_936_);
v___x_940_ = ((size_t)0ULL);
v___x_941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(v___x_936_, v_sz_939_, v___x_940_, v___x_938_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
lean_dec_ref(v_a_903_);
lean_dec_ref(v___x_936_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_957_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_957_ == 0)
{
v___x_944_ = v___x_941_;
v_isShared_945_ = v_isSharedCheck_957_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_941_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_957_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v_fst_946_; 
v_fst_946_ = lean_ctor_get(v_a_942_, 0);
if (lean_obj_tag(v_fst_946_) == 0)
{
lean_object* v_snd_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
v_snd_947_ = lean_ctor_get(v_a_942_, 1);
lean_inc(v_snd_947_);
lean_dec(v_a_942_);
v___x_948_ = l_Lean_Level_normalize(v_snd_947_);
lean_dec(v_snd_947_);
v___x_949_ = l_Lean_Expr_sort___override(v___x_948_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v___x_949_);
v___x_951_ = v___x_944_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
else
{
lean_object* v_val_953_; lean_object* v___x_955_; 
lean_inc_ref(v_fst_946_);
lean_dec(v_a_942_);
v_val_953_ = lean_ctor_get(v_fst_946_, 0);
lean_inc(v_val_953_);
lean_dec_ref_known(v_fst_946_, 1);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v_val_953_);
v___x_955_ = v___x_944_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_val_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
v_a_958_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_941_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_941_);
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
lean_dec(v_a_931_);
lean_dec_ref(v_a_903_);
lean_dec_ref(v_fvars_902_);
v___x_966_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_966_);
v___x_968_ = v___x_933_;
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
lean_dec_ref(v_a_903_);
lean_dec_ref(v_fvars_902_);
v_a_971_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_930_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_930_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(lean_object* v_e_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0));
lean_inc_ref(v_a_980_);
v___x_987_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(v_e_979_, v___x_986_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___boxed(lean_object* v_e_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(v_e_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
lean_dec_ref(v_a_989_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType___boxed(lean_object* v_e_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(v_e_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec_ref(v_a_997_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f___boxed(lean_object* v_type_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(v_type_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec_ref(v_a_1005_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType___boxed(lean_object* v_e_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_e_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec_ref(v_a_1013_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___boxed(lean_object* v_as_1020_, lean_object* v_sz_1021_, lean_object* v_i_1022_, lean_object* v_b_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
size_t v_sz_boxed_1030_; size_t v_i_boxed_1031_; lean_object* v_res_1032_; 
v_sz_boxed_1030_ = lean_unbox_usize(v_sz_1021_);
lean_dec(v_sz_1021_);
v_i_boxed_1031_ = lean_unbox_usize(v_i_1022_);
lean_dec(v_i_1022_);
v_res_1032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(v_as_1020_, v_sz_boxed_1030_, v_i_boxed_1031_, v_b_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec_ref(v_as_1020_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___boxed(lean_object* v_e_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(v_e_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec_ref(v_a_1034_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go___boxed(lean_object* v_e_1041_, lean_object* v_fvars_1042_, lean_object* v_all_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(v_e_1041_, v_fvars_1042_, v_all_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go___boxed(lean_object* v_e_1051_, lean_object* v_fvars_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(v_e_1051_, v_fvars_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3(lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(v___y_1064_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___boxed(lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3(v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec_ref(v___y_1067_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9(lean_object* v_upperBound_1074_, lean_object* v___x_1075_, lean_object* v_inst_1076_, lean_object* v_R_1077_, lean_object* v_a_1078_, lean_object* v_b_1079_, lean_object* v_c_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v_upperBound_1074_, v___x_1075_, v_a_1078_, v_b_1079_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___boxed(lean_object* v_upperBound_1088_, lean_object* v___x_1089_, lean_object* v_inst_1090_, lean_object* v_R_1091_, lean_object* v_a_1092_, lean_object* v_b_1093_, lean_object* v_c_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9(v_upperBound_1088_, v___x_1089_, v_inst_1090_, v_R_1091_, v_a_1092_, v_b_1093_, v_c_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec_ref(v___x_1089_);
lean_dec(v_upperBound_1088_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(lean_object* v_arg_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
switch(lean_obj_tag(v_arg_1102_))
{
case 0:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
return v___x_1110_;
}
case 1:
{
lean_object* v_fvarId_1111_; lean_object* v___x_1112_; 
v_fvarId_1111_ = lean_ctor_get(v_arg_1102_, 0);
lean_inc(v_fvarId_1111_);
lean_dec_ref_known(v_arg_1102_, 1);
v___x_1112_ = l_Lean_Compiler_LCNF_getType(v_fvarId_1111_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
return v___x_1112_;
}
default: 
{
lean_object* v_expr_1113_; lean_object* v___x_1114_; 
v_expr_1113_ = lean_ctor_get(v_arg_1102_, 0);
lean_inc_ref(v_expr_1113_);
lean_dec_ref_known(v_arg_1102_, 1);
v___x_1114_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_expr_1113_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
return v___x_1114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferArgType___boxed(lean_object* v_arg_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(v_arg_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec_ref(v_a_1116_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(lean_object* v_upperBound_1123_, lean_object* v_args_1124_, lean_object* v_a_1125_, lean_object* v_b_1126_){
_start:
{
lean_object* v_a_1129_; uint8_t v___x_1133_; 
v___x_1133_ = lean_nat_dec_lt(v_a_1125_, v_upperBound_1123_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec(v_a_1125_);
lean_dec_ref(v_args_1124_);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v_b_1126_);
return v___x_1134_;
}
else
{
lean_object* v_snd_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1171_; 
v_snd_1135_ = lean_ctor_get(v_b_1126_, 1);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_b_1126_);
if (v_isSharedCheck_1171_ == 0)
{
lean_object* v_unused_1172_; 
v_unused_1172_ = lean_ctor_get(v_b_1126_, 0);
lean_dec(v_unused_1172_);
v___x_1137_ = v_b_1126_;
v_isShared_1138_ = v_isSharedCheck_1171_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_snd_1135_);
lean_dec(v_b_1126_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1171_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v_fst_1139_; lean_object* v_snd_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1170_; 
v_fst_1139_ = lean_ctor_get(v_snd_1135_, 0);
v_snd_1140_ = lean_ctor_get(v_snd_1135_, 1);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_snd_1135_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1142_ = v_snd_1135_;
v_isShared_1143_ = v_isSharedCheck_1170_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_snd_1140_);
lean_inc(v_fst_1139_);
lean_dec(v_snd_1135_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1170_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_box(0);
v___x_1145_ = l_Lean_Expr_headBeta(v_snd_1140_);
if (lean_obj_tag(v___x_1145_) == 7)
{
lean_object* v_body_1146_; lean_object* v___x_1148_; 
v_body_1146_ = lean_ctor_get(v___x_1145_, 2);
lean_inc_ref(v_body_1146_);
lean_dec_ref_known(v___x_1145_, 3);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v_body_1146_);
v___x_1148_ = v___x_1142_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_fst_1139_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_body_1146_);
v___x_1148_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1150_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 1, v___x_1148_);
lean_ctor_set(v___x_1137_, 0, v___x_1144_);
v___x_1150_ = v___x_1137_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
v_a_1129_ = v___x_1150_;
goto v___jp_1128_;
}
}
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_inc_ref(v_args_1124_);
v___x_1153_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(v___x_1145_, v_fst_1139_, v_a_1125_, v_args_1124_);
lean_dec_ref(v___x_1145_);
v___x_1154_ = l_Lean_Expr_headBeta(v___x_1153_);
if (lean_obj_tag(v___x_1154_) == 7)
{
lean_object* v_body_1155_; lean_object* v___x_1157_; 
lean_dec(v_fst_1139_);
v_body_1155_ = lean_ctor_get(v___x_1154_, 2);
lean_inc_ref(v_body_1155_);
lean_dec_ref_known(v___x_1154_, 3);
lean_inc(v_a_1125_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v_body_1155_);
lean_ctor_set(v___x_1142_, 0, v_a_1125_);
v___x_1157_ = v___x_1142_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1125_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_body_1155_);
v___x_1157_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1159_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 1, v___x_1157_);
lean_ctor_set(v___x_1137_, 0, v___x_1144_);
v___x_1159_ = v___x_1137_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
v_a_1129_ = v___x_1159_;
goto v___jp_1128_;
}
}
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
lean_dec(v_a_1125_);
lean_dec_ref(v_args_1124_);
v___x_1162_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v___x_1154_);
v___x_1164_ = v___x_1142_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_fst_1139_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v___x_1154_);
v___x_1164_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1166_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 1, v___x_1164_);
lean_ctor_set(v___x_1137_, 0, v___x_1162_);
v___x_1166_ = v___x_1137_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
return v___x_1167_;
}
}
}
}
}
}
}
v___jp_1128_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_unsigned_to_nat(1u);
v___x_1131_ = lean_nat_add(v_a_1125_, v___x_1130_);
lean_dec(v_a_1125_);
v_a_1125_ = v___x_1131_;
v_b_1126_ = v_a_1129_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg___boxed(lean_object* v_upperBound_1173_, lean_object* v_args_1174_, lean_object* v_a_1175_, lean_object* v_b_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v_upperBound_1173_, v_args_1174_, v_a_1175_, v_b_1176_);
lean_dec(v_upperBound_1173_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(lean_object* v_fType_1179_, lean_object* v_args_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1187_ = lean_array_get_size(v_args_1180_);
v___x_1188_ = lean_unsigned_to_nat(0u);
v___x_1189_ = lean_box(0);
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1188_);
lean_ctor_set(v___x_1190_, 1, v_fType_1179_);
v___x_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
lean_inc_ref(v_args_1180_);
v___x_1192_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v___x_1187_, v_args_1180_, v___x_1188_, v___x_1191_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1210_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1210_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1210_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_fst_1197_; 
v_fst_1197_ = lean_ctor_get(v_a_1193_, 0);
if (lean_obj_tag(v_fst_1197_) == 0)
{
lean_object* v_snd_1198_; lean_object* v_fst_1199_; lean_object* v_snd_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
v_snd_1198_ = lean_ctor_get(v_a_1193_, 1);
lean_inc(v_snd_1198_);
lean_dec(v_a_1193_);
v_fst_1199_ = lean_ctor_get(v_snd_1198_, 0);
lean_inc(v_fst_1199_);
v_snd_1200_ = lean_ctor_get(v_snd_1198_, 1);
lean_inc(v_snd_1200_);
lean_dec(v_snd_1198_);
v___x_1201_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(v_snd_1200_, v_fst_1199_, v___x_1187_, v_args_1180_);
lean_dec(v_fst_1199_);
lean_dec(v_snd_1200_);
v___x_1202_ = l_Lean_Expr_headBeta(v___x_1201_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1202_);
v___x_1204_ = v___x_1195_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
else
{
lean_object* v_val_1206_; lean_object* v___x_1208_; 
lean_inc_ref(v_fst_1197_);
lean_dec(v_a_1193_);
lean_dec_ref(v_args_1180_);
v_val_1206_ = lean_ctor_get(v_fst_1197_, 0);
lean_inc(v_val_1206_);
lean_dec_ref_known(v_fst_1197_, 1);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v_val_1206_);
v___x_1208_ = v___x_1195_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_val_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec_ref(v_args_1180_);
v_a_1211_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1192_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1192_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore___boxed(lean_object* v_fType_1219_, lean_object* v_args_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_fType_1219_, v_args_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec_ref(v_a_1221_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0(lean_object* v_upperBound_1228_, lean_object* v_args_1229_, lean_object* v_inst_1230_, lean_object* v_R_1231_, lean_object* v_a_1232_, lean_object* v_b_1233_, lean_object* v_c_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v_upperBound_1228_, v_args_1229_, v_a_1232_, v_b_1233_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___boxed(lean_object* v_upperBound_1242_, lean_object* v_args_1243_, lean_object* v_inst_1244_, lean_object* v_R_1245_, lean_object* v_a_1246_, lean_object* v_b_1247_, lean_object* v_c_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0(v_upperBound_1242_, v_args_1243_, v_inst_1244_, v_R_1245_, v_a_1246_, v_b_1247_, v_c_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v_upperBound_1242_);
return v_res_1255_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0);
v___x_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
return v___x_1257_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0);
v___x_1259_ = lean_unsigned_to_nat(0u);
v___x_1260_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
lean_ctor_set(v___x_1260_, 2, v___x_1259_);
lean_ctor_set(v___x_1260_, 3, v___x_1259_);
lean_ctor_set(v___x_1260_, 4, v___x_1258_);
lean_ctor_set(v___x_1260_, 5, v___x_1258_);
lean_ctor_set(v___x_1260_, 6, v___x_1258_);
lean_ctor_set(v___x_1260_, 7, v___x_1258_);
lean_ctor_set(v___x_1260_, 8, v___x_1258_);
lean_ctor_set(v___x_1260_, 9, v___x_1258_);
lean_ctor_set(v___x_1260_, 10, v___x_1258_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(lean_object* v_msg_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_toCold_1267_; lean_object* v_ref_1268_; lean_object* v___x_1269_; lean_object* v_env_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v_toCold_1267_ = lean_ctor_get(v___y_1264_, 0);
v_ref_1268_ = lean_ctor_get(v___y_1264_, 2);
v___x_1269_ = lean_st_ref_get(v___y_1265_);
v_env_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc_ref(v_env_1270_);
lean_dec(v___x_1269_);
v___x_1271_ = lean_st_ref_get(v___y_1263_);
v___x_1272_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1262_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1295_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1295_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1295_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v_lctx_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1293_; 
v_lctx_1277_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1293_ == 0)
{
lean_object* v_unused_1294_; 
v_unused_1294_ = lean_ctor_get(v___x_1271_, 1);
lean_dec(v_unused_1294_);
v___x_1279_ = v___x_1271_;
v_isShared_1280_ = v_isSharedCheck_1293_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_lctx_1277_);
lean_dec(v___x_1271_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1293_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v_options_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1287_; 
v_options_1281_ = lean_ctor_get(v_toCold_1267_, 2);
v___x_1282_ = lean_unbox(v_a_1273_);
lean_dec(v_a_1273_);
v___x_1283_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1277_, v___x_1282_);
lean_dec_ref(v_lctx_1277_);
v___x_1284_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1);
lean_inc_ref(v_options_1281_);
v___x_1285_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1285_, 0, v_env_1270_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
lean_ctor_set(v___x_1285_, 2, v___x_1283_);
lean_ctor_set(v___x_1285_, 3, v_options_1281_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set_tag(v___x_1279_, 3);
lean_ctor_set(v___x_1279_, 1, v_msg_1261_);
lean_ctor_set(v___x_1279_, 0, v___x_1285_);
v___x_1287_ = v___x_1279_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1285_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_msg_1261_);
v___x_1287_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1288_; lean_object* v___x_1290_; 
lean_inc(v_ref_1268_);
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v_ref_1268_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set_tag(v___x_1275_, 1);
lean_ctor_set(v___x_1275_, 0, v___x_1288_);
v___x_1290_ = v___x_1275_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec(v___x_1271_);
lean_dec_ref(v_env_1270_);
lean_dec_ref(v_msg_1261_);
v_a_1296_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1272_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1272_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___boxed(lean_object* v_msg_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v_msg_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0(lean_object* v_00_u03b1_1311_, lean_object* v_msg_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v_msg_1312_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___boxed(lean_object* v_00_u03b1_1320_, lean_object* v_msg_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0(v_00_u03b1_1320_, v_msg_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec_ref(v___y_1322_);
return v_res_1328_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__0));
v___x_1331_ = l_Lean_stringToMessageData(v___x_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(lean_object* v_upperBound_1332_, lean_object* v_s_1333_, lean_object* v_structName_1334_, lean_object* v_idx_1335_, lean_object* v_a_1336_, lean_object* v_b_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_a_1345_; uint8_t v___x_1349_; 
v___x_1349_ = lean_nat_dec_lt(v_a_1336_, v_upperBound_1332_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
lean_dec(v_a_1336_);
lean_dec(v_idx_1335_);
lean_dec(v_structName_1334_);
lean_dec(v_s_1333_);
v___x_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1350_, 0, v_b_1337_);
return v___x_1350_;
}
else
{
lean_object* v_snd_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1389_; 
v_snd_1351_ = lean_ctor_get(v_b_1337_, 1);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_b_1337_);
if (v_isSharedCheck_1389_ == 0)
{
lean_object* v_unused_1390_; 
v_unused_1390_ = lean_ctor_get(v_b_1337_, 0);
lean_dec(v_unused_1390_);
v___x_1353_ = v_b_1337_;
v_isShared_1354_ = v_isSharedCheck_1389_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_snd_1351_);
lean_dec(v_b_1337_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1389_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_box(0);
if (lean_obj_tag(v_snd_1351_) == 7)
{
lean_object* v_body_1356_; uint8_t v___x_1357_; 
v_body_1356_ = lean_ctor_get(v_snd_1351_, 2);
lean_inc_ref(v_body_1356_);
lean_dec_ref_known(v_snd_1351_, 3);
v___x_1357_ = l_Lean_Expr_hasLooseBVars(v_body_1356_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1359_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 1, v_body_1356_);
lean_ctor_set(v___x_1353_, 0, v___x_1355_);
v___x_1359_ = v___x_1353_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_body_1356_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
v_a_1345_ = v___x_1359_;
goto v___jp_1344_;
}
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1361_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_1362_ = lean_expr_instantiate1(v_body_1356_, v___x_1361_);
lean_dec_ref(v_body_1356_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 1, v___x_1362_);
lean_ctor_set(v___x_1353_, 0, v___x_1355_);
v___x_1364_ = v___x_1353_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
v_a_1345_ = v___x_1364_;
goto v___jp_1344_;
}
}
}
else
{
uint8_t v___x_1366_; 
v___x_1366_ = l_Lean_Expr_isErased(v_snd_1351_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1367_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
lean_inc(v_s_1333_);
v___x_1368_ = l_Lean_mkFVar(v_s_1333_);
lean_inc(v_idx_1335_);
lean_inc(v_structName_1334_);
v___x_1369_ = l_Lean_mkProj(v_structName_1334_, v_idx_1335_, v___x_1368_);
v___x_1370_ = l_Lean_indentExpr(v___x_1369_);
v___x_1371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1367_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
v___x_1372_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_1371_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v___x_1374_; 
lean_dec_ref_known(v___x_1372_, 1);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v___x_1355_);
v___x_1374_ = v___x_1353_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_snd_1351_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
v_a_1345_ = v___x_1374_;
goto v___jp_1344_;
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_del_object(v___x_1353_);
lean_dec(v_snd_1351_);
lean_dec(v_a_1336_);
lean_dec(v_idx_1335_);
lean_dec(v_structName_1334_);
lean_dec(v_s_1333_);
v_a_1376_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1372_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1372_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1386_; 
lean_dec(v_a_1336_);
lean_dec(v_idx_1335_);
lean_dec(v_structName_1334_);
lean_dec(v_s_1333_);
v___x_1384_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v___x_1384_);
v___x_1386_ = v___x_1353_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_snd_1351_);
v___x_1386_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1387_; 
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
}
}
}
}
v___jp_1344_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_unsigned_to_nat(1u);
v___x_1347_ = lean_nat_add(v_a_1336_, v___x_1346_);
lean_dec(v_a_1336_);
v_a_1336_ = v___x_1347_;
v_b_1337_ = v_a_1345_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___boxed(lean_object* v_upperBound_1391_, lean_object* v_s_1392_, lean_object* v_structName_1393_, lean_object* v_idx_1394_, lean_object* v_a_1395_, lean_object* v_b_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_1391_, v_s_1392_, v_structName_1393_, v_idx_1394_, v_a_1395_, v_b_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v_upperBound_1391_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(lean_object* v_upperBound_1404_, lean_object* v_s_1405_, lean_object* v_structName_1406_, lean_object* v_idx_1407_, lean_object* v_a_1408_, lean_object* v_b_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_a_1417_; uint8_t v___x_1421_; 
v___x_1421_ = lean_nat_dec_lt(v_a_1408_, v_upperBound_1404_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; 
lean_dec(v_idx_1407_);
lean_dec(v_structName_1406_);
lean_dec(v_s_1405_);
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v_b_1409_);
return v___x_1422_;
}
else
{
lean_object* v_snd_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1461_; 
v_snd_1423_ = lean_ctor_get(v_b_1409_, 1);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_b_1409_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v_b_1409_, 0);
lean_dec(v_unused_1462_);
v___x_1425_ = v_b_1409_;
v_isShared_1426_ = v_isSharedCheck_1461_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_snd_1423_);
lean_dec(v_b_1409_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1461_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_box(0);
if (lean_obj_tag(v_snd_1423_) == 7)
{
lean_object* v_body_1428_; uint8_t v___x_1429_; 
v_body_1428_ = lean_ctor_get(v_snd_1423_, 2);
lean_inc_ref(v_body_1428_);
lean_dec_ref_known(v_snd_1423_, 3);
v___x_1429_ = l_Lean_Expr_hasLooseBVars(v_body_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1431_; 
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 1, v_body_1428_);
lean_ctor_set(v___x_1425_, 0, v___x_1427_);
v___x_1431_ = v___x_1425_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_body_1428_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
v_a_1417_ = v___x_1431_;
goto v___jp_1416_;
}
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1433_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_1434_ = lean_expr_instantiate1(v_body_1428_, v___x_1433_);
lean_dec_ref(v_body_1428_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 1, v___x_1434_);
lean_ctor_set(v___x_1425_, 0, v___x_1427_);
v___x_1436_ = v___x_1425_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
v_a_1417_ = v___x_1436_;
goto v___jp_1416_;
}
}
}
else
{
uint8_t v___x_1438_; 
v___x_1438_ = l_Lean_Expr_isErased(v_snd_1423_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1439_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
lean_inc(v_s_1405_);
v___x_1440_ = l_Lean_mkFVar(v_s_1405_);
lean_inc(v_idx_1407_);
lean_inc(v_structName_1406_);
v___x_1441_ = l_Lean_mkProj(v_structName_1406_, v_idx_1407_, v___x_1440_);
v___x_1442_ = l_Lean_indentExpr(v___x_1441_);
v___x_1443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1439_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
v___x_1444_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_1443_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v___x_1446_; 
lean_dec_ref_known(v___x_1444_, 1);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1427_);
v___x_1446_ = v___x_1425_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_snd_1423_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
v_a_1417_ = v___x_1446_;
goto v___jp_1416_;
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_del_object(v___x_1425_);
lean_dec(v_snd_1423_);
lean_dec(v_idx_1407_);
lean_dec(v_structName_1406_);
lean_dec(v_s_1405_);
v_a_1448_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1444_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1444_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1458_; 
lean_dec(v_idx_1407_);
lean_dec(v_structName_1406_);
lean_dec(v_s_1405_);
v___x_1456_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1456_);
v___x_1458_ = v___x_1425_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_snd_1423_);
v___x_1458_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
return v___x_1459_;
}
}
}
}
}
v___jp_1416_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = lean_unsigned_to_nat(1u);
v___x_1419_ = lean_nat_add(v_a_1408_, v___x_1418_);
v___x_1420_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_1404_, v_s_1405_, v_structName_1406_, v_idx_1407_, v___x_1419_, v_a_1417_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
return v___x_1420_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg___boxed(lean_object* v_upperBound_1463_, lean_object* v_s_1464_, lean_object* v_structName_1465_, lean_object* v_idx_1466_, lean_object* v_a_1467_, lean_object* v_b_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_upperBound_1463_, v_s_1464_, v_structName_1465_, v_idx_1466_, v_a_1467_, v_b_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v_a_1467_);
lean_dec(v_upperBound_1463_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_ref_1476_, lean_object* v_msg_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_toCold_1484_; lean_object* v_currRecDepth_1485_; lean_object* v_ref_1486_; uint8_t v_diag_1487_; uint8_t v_suppressElabErrors_1488_; lean_object* v_ref_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_toCold_1484_ = lean_ctor_get(v___y_1481_, 0);
v_currRecDepth_1485_ = lean_ctor_get(v___y_1481_, 1);
v_ref_1486_ = lean_ctor_get(v___y_1481_, 2);
v_diag_1487_ = lean_ctor_get_uint8(v___y_1481_, sizeof(void*)*3);
v_suppressElabErrors_1488_ = lean_ctor_get_uint8(v___y_1481_, sizeof(void*)*3 + 1);
v_ref_1489_ = l_Lean_replaceRef(v_ref_1476_, v_ref_1486_);
lean_inc(v_currRecDepth_1485_);
lean_inc_ref(v_toCold_1484_);
v___x_1490_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1490_, 0, v_toCold_1484_);
lean_ctor_set(v___x_1490_, 1, v_currRecDepth_1485_);
lean_ctor_set(v___x_1490_, 2, v_ref_1489_);
lean_ctor_set_uint8(v___x_1490_, sizeof(void*)*3, v_diag_1487_);
lean_ctor_set_uint8(v___x_1490_, sizeof(void*)*3 + 1, v_suppressElabErrors_1488_);
v___x_1491_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v_msg_1477_, v___y_1479_, v___y_1480_, v___x_1490_, v___y_1482_);
lean_dec_ref_known(v___x_1490_, 3);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_ref_1492_, lean_object* v_msg_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_1492_, v_msg_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v_ref_1492_);
return v_res_1500_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1501_ = lean_box(1);
v___x_1502_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3);
v___x_1503_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0);
v___x_1504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
lean_ctor_set(v___x_1504_, 1, v___x_1502_);
lean_ctor_set(v___x_1504_, 2, v___x_1501_);
return v___x_1504_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__1));
v___x_1507_ = l_Lean_stringToMessageData(v___x_1506_);
return v___x_1507_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__3));
v___x_1510_ = l_Lean_stringToMessageData(v___x_1509_);
return v___x_1510_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__5));
v___x_1513_ = l_Lean_stringToMessageData(v___x_1512_);
return v___x_1513_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__7));
v___x_1516_ = l_Lean_stringToMessageData(v___x_1515_);
return v___x_1516_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__9));
v___x_1519_ = l_Lean_stringToMessageData(v___x_1518_);
return v___x_1519_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__11));
v___x_1522_ = l_Lean_stringToMessageData(v___x_1521_);
return v___x_1522_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__13));
v___x_1525_ = l_Lean_stringToMessageData(v___x_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(lean_object* v_msg_1526_, lean_object* v_declHint_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v_env_1532_; uint8_t v___x_1533_; 
v___x_1530_ = lean_box(0);
v___x_1531_ = lean_st_ref_get(v___y_1528_);
v_env_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc_ref(v_env_1532_);
lean_dec(v___x_1531_);
v___x_1533_ = l_Lean_Name_isAnonymous(v_declHint_1527_);
if (v___x_1533_ == 0)
{
uint8_t v_isExporting_1534_; 
v_isExporting_1534_ = lean_ctor_get_uint8(v_env_1532_, sizeof(void*)*8);
if (v_isExporting_1534_ == 0)
{
lean_object* v___x_1535_; 
lean_dec_ref(v_env_1532_);
lean_dec(v_declHint_1527_);
v___x_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1535_, 0, v_msg_1526_);
return v___x_1535_;
}
else
{
lean_object* v___x_1536_; uint8_t v___x_1537_; 
lean_inc_ref(v_env_1532_);
v___x_1536_ = l_Lean_Environment_setExporting(v_env_1532_, v___x_1533_);
lean_inc(v_declHint_1527_);
lean_inc_ref(v___x_1536_);
v___x_1537_ = l_Lean_Environment_contains(v___x_1536_, v_declHint_1527_, v_isExporting_1534_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; 
lean_dec_ref(v___x_1536_);
lean_dec_ref(v_env_1532_);
lean_dec(v_declHint_1527_);
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v_msg_1526_);
return v___x_1538_;
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v_c_1544_; lean_object* v___x_1545_; 
v___x_1539_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1);
v___x_1540_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0);
v___x_1541_ = l_Lean_Options_empty;
v___x_1542_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1536_);
lean_ctor_set(v___x_1542_, 1, v___x_1539_);
lean_ctor_set(v___x_1542_, 2, v___x_1540_);
lean_ctor_set(v___x_1542_, 3, v___x_1541_);
lean_inc(v_declHint_1527_);
v___x_1543_ = l_Lean_MessageData_ofConstName(v_declHint_1527_, v___x_1533_);
v_c_1544_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1544_, 0, v___x_1542_);
lean_ctor_set(v_c_1544_, 1, v___x_1543_);
v___x_1545_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1532_, v_declHint_1527_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
lean_dec_ref(v_env_1532_);
lean_dec(v_declHint_1527_);
v___x_1546_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2);
v___x_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v_c_1544_);
v___x_1548_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = l_Lean_MessageData_note(v___x_1549_);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v_msg_1526_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
return v___x_1552_;
}
else
{
lean_object* v_val_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1587_; 
v_val_1553_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1555_ = v___x_1545_;
v_isShared_1556_ = v_isSharedCheck_1587_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_val_1553_);
lean_dec(v___x_1545_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1587_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v_mod_1559_; uint8_t v___x_1560_; 
v___x_1557_ = l_Lean_Environment_header(v_env_1532_);
lean_dec_ref(v_env_1532_);
v___x_1558_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1557_);
v_mod_1559_ = lean_array_get(v___x_1530_, v___x_1558_, v_val_1553_);
lean_dec(v_val_1553_);
lean_dec_ref(v___x_1558_);
v___x_1560_ = l_Lean_isPrivateName(v_declHint_1527_);
lean_dec(v_declHint_1527_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1572_; 
v___x_1561_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6);
v___x_1562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
lean_ctor_set(v___x_1562_, 1, v_c_1544_);
v___x_1563_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8);
v___x_1564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1562_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = l_Lean_MessageData_ofName(v_mod_1559_);
v___x_1566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1564_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10);
v___x_1568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = l_Lean_MessageData_note(v___x_1568_);
v___x_1570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1570_, 0, v_msg_1526_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set_tag(v___x_1555_, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1570_);
v___x_1572_ = v___x_1555_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
else
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1574_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2);
v___x_1575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
lean_ctor_set(v___x_1575_, 1, v_c_1544_);
v___x_1576_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12);
v___x_1577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = l_Lean_MessageData_ofName(v_mod_1559_);
v___x_1579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1577_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14);
v___x_1581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = l_Lean_MessageData_note(v___x_1581_);
v___x_1583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1583_, 0, v_msg_1526_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set_tag(v___x_1555_, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1583_);
v___x_1585_ = v___x_1555_;
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
}
}
}
}
}
else
{
lean_object* v___x_1588_; 
lean_dec_ref(v_env_1532_);
lean_dec(v_declHint_1527_);
v___x_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1588_, 0, v_msg_1526_);
return v___x_1588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_msg_1589_, lean_object* v_declHint_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_1589_, v_declHint_1590_, v___y_1591_);
lean_dec(v___y_1591_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(lean_object* v_msg_1594_, lean_object* v_declHint_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___x_1602_; lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1612_; 
v___x_1602_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_1594_, v_declHint_1595_, v___y_1600_);
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1612_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1612_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1610_; 
v___x_1607_ = l_Lean_unknownIdentifierMessageTag;
v___x_1608_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
lean_ctor_set(v___x_1608_, 1, v_a_1603_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v___x_1608_);
v___x_1610_ = v___x_1605_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1608_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_msg_1613_, lean_object* v_declHint_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(v_msg_1613_, v_declHint_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec_ref(v___y_1615_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1622_, lean_object* v_msg_1623_, lean_object* v_declHint_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; lean_object* v_a_1632_; lean_object* v___x_1633_; 
v___x_1631_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(v_msg_1623_, v_declHint_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1632_);
lean_dec_ref(v___x_1631_);
v___x_1633_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_1622_, v_a_1632_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1634_, lean_object* v_msg_1635_, lean_object* v_declHint_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1634_, v_msg_1635_, v_declHint_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v_ref_1634_);
return v_res_1643_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__0));
v___x_1646_ = l_Lean_stringToMessageData(v___x_1645_);
return v___x_1646_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__2));
v___x_1649_ = l_Lean_stringToMessageData(v___x_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(lean_object* v_ref_1650_, lean_object* v_constName_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v___x_1658_; uint8_t v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1658_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_1659_ = 0;
lean_inc(v_constName_1651_);
v___x_1660_ = l_Lean_MessageData_ofConstName(v_constName_1651_, v___x_1659_);
v___x_1661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1658_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
v___x_1662_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3);
v___x_1663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1661_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1650_, v___x_1663_, v_constName_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1665_, lean_object* v_constName_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1665_, v_constName_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v_ref_1665_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(lean_object* v_constName_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_ref_1681_; lean_object* v___x_1682_; 
v_ref_1681_ = lean_ctor_get(v___y_1678_, 2);
v___x_1682_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1681_, v_constName_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_constName_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec_ref(v___y_1684_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(lean_object* v_constName_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v___x_1698_; lean_object* v_env_1699_; uint8_t v___x_1700_; lean_object* v___x_1701_; 
v___x_1698_ = lean_st_ref_get(v___y_1696_);
v_env_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc_ref(v_env_1699_);
lean_dec(v___x_1698_);
v___x_1700_ = 0;
lean_inc(v_constName_1691_);
v___x_1701_ = l_Lean_Environment_find_x3f(v_env_1699_, v_constName_1691_, v___x_1700_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
return v___x_1702_;
}
else
{
lean_object* v_val_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec(v_constName_1691_);
v_val_1703_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1701_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_val_1703_);
lean_dec(v___x_1701_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
lean_ctor_set_tag(v___x_1705_, 0);
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_val_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1___boxed(lean_object* v_constName_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(v_constName_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec_ref(v___y_1712_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(lean_object* v_structName_1719_, lean_object* v_idx_1720_, lean_object* v_s_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___x_1740_; 
lean_inc(v_s_1721_);
v___x_1740_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_s_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1836_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1743_ = v___x_1740_;
v_isShared_1744_ = v_isSharedCheck_1836_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1740_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1836_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1745_ = l_Lean_Expr_headBeta(v_a_1741_);
v___x_1746_ = l_Lean_Expr_isErased(v___x_1745_);
if (v___x_1746_ == 0)
{
uint8_t v___x_1747_; 
v___x_1747_ = l_Lean_Expr_isAny(v___x_1745_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; 
lean_del_object(v___x_1743_);
v___x_1748_ = l_Lean_Expr_getAppFn(v___x_1745_);
if (lean_obj_tag(v___x_1748_) == 4)
{
lean_object* v_declName_1749_; lean_object* v_us_1750_; lean_object* v___x_1751_; lean_object* v_env_1752_; lean_object* v___x_1753_; 
v_declName_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_declName_1749_);
v_us_1750_ = lean_ctor_get(v___x_1748_, 1);
lean_inc(v_us_1750_);
lean_dec_ref_known(v___x_1748_, 2);
v___x_1751_ = lean_st_ref_get(v_a_1726_);
v_env_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc_ref(v_env_1752_);
lean_dec(v___x_1751_);
v___x_1753_ = l_Lean_Environment_find_x3f(v_env_1752_, v_declName_1749_, v___x_1747_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_dec(v_us_1750_);
lean_dec_ref(v___x_1745_);
v___y_1729_ = v_a_1722_;
v___y_1730_ = v_a_1723_;
v___y_1731_ = v_a_1724_;
v___y_1732_ = v_a_1725_;
v___y_1733_ = v_a_1726_;
goto v___jp_1728_;
}
else
{
lean_object* v_val_1754_; 
v_val_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_val_1754_);
lean_dec_ref_known(v___x_1753_, 1);
if (lean_obj_tag(v_val_1754_) == 5)
{
lean_object* v_val_1755_; lean_object* v_ctors_1756_; 
v_val_1755_ = lean_ctor_get(v_val_1754_, 0);
lean_inc_ref(v_val_1755_);
lean_dec_ref_known(v_val_1754_, 1);
v_ctors_1756_ = lean_ctor_get(v_val_1755_, 4);
lean_inc(v_ctors_1756_);
if (lean_obj_tag(v_ctors_1756_) == 1)
{
lean_object* v_tail_1757_; 
v_tail_1757_ = lean_ctor_get(v_ctors_1756_, 1);
if (lean_obj_tag(v_tail_1757_) == 0)
{
lean_object* v_numParams_1758_; lean_object* v_numIndices_1759_; lean_object* v_head_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1826_; 
v_numParams_1758_ = lean_ctor_get(v_val_1755_, 1);
lean_inc(v_numParams_1758_);
v_numIndices_1759_ = lean_ctor_get(v_val_1755_, 2);
lean_inc(v_numIndices_1759_);
lean_dec_ref(v_val_1755_);
v_head_1760_ = lean_ctor_get(v_ctors_1756_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v_ctors_1756_);
if (v_isSharedCheck_1826_ == 0)
{
lean_object* v_unused_1827_; 
v_unused_1827_ = lean_ctor_get(v_ctors_1756_, 1);
lean_dec(v_unused_1827_);
v___x_1762_ = v_ctors_1756_;
v_isShared_1763_ = v_isSharedCheck_1826_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_head_1760_);
lean_dec(v_ctors_1756_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1826_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(v_head_1760_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
if (lean_obj_tag(v_a_1765_) == 6)
{
lean_object* v_val_1766_; lean_object* v_dummy_1767_; lean_object* v_nargs_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v_val_1766_ = lean_ctor_get(v_a_1765_, 0);
lean_inc_ref(v_val_1766_);
lean_dec_ref_known(v_a_1765_, 1);
v_dummy_1767_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0);
v_nargs_1768_ = l_Lean_Expr_getAppNumArgs(v___x_1745_);
lean_inc(v_nargs_1768_);
v___x_1769_ = lean_mk_array(v_nargs_1768_, v_dummy_1767_);
v___x_1770_ = lean_unsigned_to_nat(1u);
v___x_1771_ = lean_nat_sub(v_nargs_1768_, v___x_1770_);
lean_dec(v_nargs_1768_);
v___x_1772_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1745_, v___x_1769_, v___x_1771_);
v___x_1773_ = lean_nat_add(v_numParams_1758_, v_numIndices_1759_);
lean_dec(v_numIndices_1759_);
v___x_1774_ = lean_array_get_size(v___x_1772_);
v___x_1775_ = lean_nat_dec_eq(v___x_1773_, v___x_1774_);
lean_dec(v___x_1773_);
if (v___x_1775_ == 0)
{
lean_dec_ref(v___x_1772_);
lean_dec_ref(v_val_1766_);
lean_del_object(v___x_1762_);
lean_dec(v_numParams_1758_);
lean_dec(v_us_1750_);
v___y_1729_ = v_a_1722_;
v___y_1730_ = v_a_1723_;
v___y_1731_ = v_a_1724_;
v___y_1732_ = v_a_1725_;
v___y_1733_ = v_a_1726_;
goto v___jp_1728_;
}
else
{
if (v___x_1747_ == 0)
{
lean_object* v_toConstantVal_1776_; lean_object* v_name_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_toConstantVal_1776_ = lean_ctor_get(v_val_1766_, 0);
lean_inc_ref(v_toConstantVal_1776_);
lean_dec_ref(v_val_1766_);
v_name_1777_ = lean_ctor_get(v_toConstantVal_1776_, 0);
lean_inc(v_name_1777_);
lean_dec_ref(v_toConstantVal_1776_);
v___x_1778_ = l_Lean_mkConst(v_name_1777_, v_us_1750_);
v___x_1779_ = lean_unsigned_to_nat(0u);
v___x_1780_ = l_Array_toSubarray___redArg(v___x_1772_, v___x_1779_, v_numParams_1758_);
v___x_1781_ = l_Subarray_copy___redArg(v___x_1780_);
v___x_1782_ = l_Lean_mkAppN(v___x_1778_, v___x_1781_);
lean_dec_ref(v___x_1781_);
v___x_1783_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(v___x_1782_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1783_, 1);
v___x_1785_ = lean_box(0);
if (v_isShared_1763_ == 0)
{
lean_ctor_set_tag(v___x_1762_, 0);
lean_ctor_set(v___x_1762_, 1, v_a_1784_);
lean_ctor_set(v___x_1762_, 0, v___x_1785_);
v___x_1787_ = v___x_1762_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1785_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_a_1784_);
v___x_1787_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1788_; 
lean_inc(v_structName_1719_);
lean_inc(v_s_1721_);
lean_inc(v_idx_1720_);
v___x_1788_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_idx_1720_, v_s_1721_, v_structName_1719_, v_idx_1720_, v___x_1779_, v___x_1787_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1808_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1808_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1808_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v_fst_1793_; 
v_fst_1793_ = lean_ctor_get(v_a_1789_, 0);
if (lean_obj_tag(v_fst_1793_) == 0)
{
lean_object* v_snd_1794_; 
v_snd_1794_ = lean_ctor_get(v_a_1789_, 1);
lean_inc(v_snd_1794_);
lean_dec(v_a_1789_);
if (lean_obj_tag(v_snd_1794_) == 7)
{
lean_object* v_binderType_1795_; lean_object* v___x_1797_; 
lean_dec(v_s_1721_);
lean_dec(v_idx_1720_);
lean_dec(v_structName_1719_);
v_binderType_1795_ = lean_ctor_get(v_snd_1794_, 1);
lean_inc_ref(v_binderType_1795_);
lean_dec_ref_known(v_snd_1794_, 3);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v_binderType_1795_);
v___x_1797_ = v___x_1791_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_binderType_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
else
{
uint8_t v___x_1799_; 
v___x_1799_ = l_Lean_Expr_isErased(v_snd_1794_);
lean_dec(v_snd_1794_);
if (v___x_1799_ == 0)
{
lean_del_object(v___x_1791_);
v___y_1729_ = v_a_1722_;
v___y_1730_ = v_a_1723_;
v___y_1731_ = v_a_1724_;
v___y_1732_ = v_a_1725_;
v___y_1733_ = v_a_1726_;
goto v___jp_1728_;
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1802_; 
lean_dec(v_s_1721_);
lean_dec(v_idx_1720_);
lean_dec(v_structName_1719_);
v___x_1800_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v___x_1800_);
v___x_1802_ = v___x_1791_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
else
{
lean_object* v_val_1804_; lean_object* v___x_1806_; 
lean_inc_ref(v_fst_1793_);
lean_dec(v_a_1789_);
lean_dec(v_s_1721_);
lean_dec(v_idx_1720_);
lean_dec(v_structName_1719_);
v_val_1804_ = lean_ctor_get(v_fst_1793_, 0);
lean_inc(v_val_1804_);
lean_dec_ref_known(v_fst_1793_, 1);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v_val_1804_);
v___x_1806_ = v___x_1791_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_val_1804_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec(v_s_1721_);
lean_dec(v_idx_1720_);
lean_dec(v_structName_1719_);
v_a_1809_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1788_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1788_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
else
{
lean_del_object(v___x_1762_);
lean_dec(v_s_1721_);
lean_dec(v_idx_1720_);
lean_dec(v_structName_1719_);
return v___x_1783_;
}
}
else
{
lean_dec_ref(v___x_1772_);
lean_dec_ref(v_val_1766_);
lean_del_object(v___x_1762_);
lean_dec(v_numParams_1758_);
lean_dec(v_us_1750_);
v___y_1729_ = v_a_1722_;
v___y_1730_ = v_a_1723_;
v___y_1731_ = v_a_1724_;
v___y_1732_ = v_a_1725_;
v___y_1733_ = v_a_1726_;
goto v___jp_1728_;
}
}
}
else
{
lean_dec(v_a_1765_);
lean_del_object(v___x_1762_);
lean_dec(v_numIndices_1759_);
lean_dec(v_numParams_1758_);
lean_dec(v_us_1750_);
lean_dec_ref(v___x_1745_);
v___y_1729_ = v_a_1722_;
v___y_1730_ = v_a_1723_;
v___y_1731_ = v_a_1724_;
v___y_1732_ = v_a_1725_;
v___y_1733_ = v_a_1726_;
goto v___jp_1728_;
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_del_object(v___x_1762_);
lean_dec(v_numIndices_1759_);
lean_dec(v_numParams_1758_);
lean_dec(v_us_1750_);
lean_dec_ref(v___x_1745_);
lean_dec(v_s_1721_);
lean_dec(v_idx_1720_);
lean_dec(v_structName_1719_);
v_a_1818_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1764_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1764_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
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
}
else
{
lean_dec_ref_known(v_ctors_1756_, 2);
lean_dec_ref(v_val_1755_);
lean_dec(v_us_1750_);
lean_dec_ref(v___x_1745_);
v___y_1729_ = v_a_1722_;
v___y_1730_ = v_a_1723_;
v___y_1731_ = v_a_1724_;
v___y_1732_ = v_a_1725_;
v___y_1733_ = v_a_1726_;
goto v___jp_1728_;
}
}
else
{
lean_dec(v_ctors_1756_);
lean_dec_ref(v_val_1755_);
lean_dec(v_us_1750_);
lean_dec_ref(v___x_1745_);
v___y_1729_ = v_a_1722_;
v___y_1730_ = v_a_1723_;
v___y_1731_ = v_a_1724_;
v___y_1732_ = v_a_1725_;
v___y_1733_ = v_a_1726_;
goto v___jp_1728_;
}
}
else
{
lean_dec(v_val_1754_);
lean_dec(v_us_1750_);
lean_dec_ref(v___x_1745_);
v___y_1729_ = v_a_1722_;
v___y_1730_ = v_a_1723_;
v___y_1731_ = v_a_1724_;
v___y_1732_ = v_a_1725_;
v___y_1733_ = v_a_1726_;
goto v___jp_1728_;
}
}
}
else
{
lean_dec_ref(v___x_1748_);
lean_dec_ref(v___x_1745_);
v___y_1729_ = v_a_1722_;
v___y_1730_ = v_a_1723_;
v___y_1731_ = v_a_1724_;
v___y_1732_ = v_a_1725_;
v___y_1733_ = v_a_1726_;
goto v___jp_1728_;
}
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1830_; 
lean_dec_ref(v___x_1745_);
lean_dec(v_s_1721_);
lean_dec(v_idx_1720_);
lean_dec(v_structName_1719_);
v___x_1828_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1828_);
v___x_1830_ = v___x_1743_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1834_; 
lean_dec_ref(v___x_1745_);
lean_dec(v_s_1721_);
lean_dec(v_idx_1720_);
lean_dec(v_structName_1719_);
v___x_1832_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1832_);
v___x_1834_ = v___x_1743_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
else
{
lean_dec(v_s_1721_);
lean_dec(v_idx_1720_);
lean_dec(v_structName_1719_);
return v___x_1740_;
}
v___jp_1728_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1734_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
v___x_1735_ = l_Lean_mkFVar(v_s_1721_);
v___x_1736_ = l_Lean_mkProj(v_structName_1719_, v_idx_1720_, v___x_1735_);
v___x_1737_ = l_Lean_indentExpr(v___x_1736_);
v___x_1738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1734_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_1738_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
return v___x_1739_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferProjType___boxed(lean_object* v_structName_1837_, lean_object* v_idx_1838_, lean_object* v_s_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(v_structName_1837_, v_idx_1838_, v_s_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec_ref(v_a_1840_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2(lean_object* v_upperBound_1847_, lean_object* v_s_1848_, lean_object* v_structName_1849_, lean_object* v_idx_1850_, lean_object* v_inst_1851_, lean_object* v_R_1852_, lean_object* v_a_1853_, lean_object* v_b_1854_, lean_object* v_c_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_upperBound_1847_, v_s_1848_, v_structName_1849_, v_idx_1850_, v_a_1853_, v_b_1854_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___boxed(lean_object* v_upperBound_1863_, lean_object* v_s_1864_, lean_object* v_structName_1865_, lean_object* v_idx_1866_, lean_object* v_inst_1867_, lean_object* v_R_1868_, lean_object* v_a_1869_, lean_object* v_b_1870_, lean_object* v_c_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2(v_upperBound_1863_, v_s_1864_, v_structName_1865_, v_idx_1866_, v_inst_1867_, v_R_1868_, v_a_1869_, v_b_1870_, v_c_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v_a_1869_);
lean_dec(v_upperBound_1863_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1(lean_object* v_00_u03b1_1879_, lean_object* v_constName_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___boxed(lean_object* v_00_u03b1_1888_, lean_object* v_constName_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1(v_00_u03b1_1888_, v_constName_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec_ref(v___y_1890_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3(lean_object* v_upperBound_1897_, lean_object* v_s_1898_, lean_object* v_structName_1899_, lean_object* v_idx_1900_, lean_object* v_inst_1901_, lean_object* v_R_1902_, lean_object* v_a_1903_, lean_object* v_b_1904_, lean_object* v_c_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_1897_, v_s_1898_, v_structName_1899_, v_idx_1900_, v_a_1903_, v_b_1904_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___boxed(lean_object* v_upperBound_1913_, lean_object* v_s_1914_, lean_object* v_structName_1915_, lean_object* v_idx_1916_, lean_object* v_inst_1917_, lean_object* v_R_1918_, lean_object* v_a_1919_, lean_object* v_b_1920_, lean_object* v_c_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3(v_upperBound_1913_, v_s_1914_, v_structName_1915_, v_idx_1916_, v_inst_1917_, v_R_1918_, v_a_1919_, v_b_1920_, v_c_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v_upperBound_1913_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_1929_, lean_object* v_ref_1930_, lean_object* v_constName_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v___x_1938_; 
v___x_1938_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1930_, v_constName_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1939_, lean_object* v_ref_1940_, lean_object* v_constName_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2(v_00_u03b1_1939_, v_ref_1940_, v_constName_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v_ref_1940_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1949_, lean_object* v_ref_1950_, lean_object* v_msg_1951_, lean_object* v_declHint_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v___x_1959_; 
v___x_1959_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1950_, v_msg_1951_, v_declHint_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1960_, lean_object* v_ref_1961_, lean_object* v_msg_1962_, lean_object* v_declHint_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4(v_00_u03b1_1960_, v_ref_1961_, v_msg_1962_, v_declHint_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v_ref_1961_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msg_1971_, lean_object* v_declHint_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_1971_, v_declHint_1972_, v___y_1977_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_1980_, lean_object* v_declHint_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_1980_, v_declHint_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec_ref(v___y_1982_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b1_1989_, lean_object* v_ref_1990_, lean_object* v_msg_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_1990_, v_msg_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b1_1999_, lean_object* v_ref_2000_, lean_object* v_msg_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7(v_00_u03b1_1999_, v_ref_2000_, v_msg_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v_ref_2000_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(lean_object* v_e_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
switch(lean_obj_tag(v_e_2009_))
{
case 0:
{
lean_object* v_value_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2024_; 
v_value_2016_ = lean_ctor_get(v_e_2009_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_e_2009_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2018_ = v_e_2009_;
v_isShared_2019_ = v_isSharedCheck_2024_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_value_2016_);
lean_dec(v_e_2009_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2024_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2020_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType(v_value_2016_);
lean_dec_ref(v_value_2016_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2020_);
v___x_2022_ = v___x_2018_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
case 1:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
return v___x_2026_;
}
case 2:
{
lean_object* v_typeName_2027_; lean_object* v_idx_2028_; lean_object* v_struct_2029_; lean_object* v___x_2030_; 
v_typeName_2027_ = lean_ctor_get(v_e_2009_, 0);
lean_inc(v_typeName_2027_);
v_idx_2028_ = lean_ctor_get(v_e_2009_, 1);
lean_inc(v_idx_2028_);
v_struct_2029_ = lean_ctor_get(v_e_2009_, 2);
lean_inc(v_struct_2029_);
lean_dec_ref_known(v_e_2009_, 3);
v___x_2030_ = l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(v_typeName_2027_, v_idx_2028_, v_struct_2029_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
return v___x_2030_;
}
case 3:
{
lean_object* v_declName_2031_; lean_object* v_us_2032_; lean_object* v_args_2033_; lean_object* v___x_2034_; 
v_declName_2031_ = lean_ctor_get(v_e_2009_, 0);
lean_inc(v_declName_2031_);
v_us_2032_ = lean_ctor_get(v_e_2009_, 1);
lean_inc(v_us_2032_);
v_args_2033_ = lean_ctor_get(v_e_2009_, 2);
lean_inc_ref(v_args_2033_);
lean_dec_ref_known(v_e_2009_, 3);
v___x_2034_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(v_declName_2031_, v_us_2032_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2036_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2034_, 1);
v___x_2036_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2035_, v_args_2033_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
return v___x_2036_;
}
else
{
lean_dec_ref(v_args_2033_);
return v___x_2034_;
}
}
default: 
{
lean_object* v_fvarId_2037_; lean_object* v_args_2038_; lean_object* v___x_2039_; 
v_fvarId_2037_ = lean_ctor_get(v_e_2009_, 0);
lean_inc(v_fvarId_2037_);
v_args_2038_ = lean_ctor_get(v_e_2009_, 1);
lean_inc_ref(v_args_2038_);
lean_dec_ref_known(v_e_2009_, 2);
v___x_2039_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_fvarId_2037_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2041_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2041_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2040_, v_args_2038_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
return v___x_2041_;
}
else
{
lean_dec_ref(v_args_2038_);
return v___x_2039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType___boxed(lean_object* v_e_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(v_e_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
lean_dec(v_a_2045_);
lean_dec_ref(v_a_2044_);
lean_dec_ref(v_a_2043_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType(lean_object* v_e_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2056_ = lean_unsigned_to_nat(32u);
v___x_2057_ = lean_mk_empty_array_with_capacity(v___x_2056_);
lean_dec_ref(v___x_2057_);
v___x_2058_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2059_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_e_2050_, v___x_2058_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType___boxed(lean_object* v_e_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_Compiler_LCNF_inferType(v_e_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
lean_dec(v_a_2064_);
lean_dec_ref(v_a_2063_);
lean_dec(v_a_2062_);
lean_dec_ref(v_a_2061_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(lean_object* v_msg_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v___x_2073_; lean_object* v_toApplicative_2074_; lean_object* v_toFunctor_2075_; lean_object* v_toSeq_2076_; lean_object* v_toSeqLeft_2077_; lean_object* v_toSeqRight_2078_; lean_object* v___f_2079_; lean_object* v___f_2080_; lean_object* v___f_2081_; lean_object* v___f_2082_; lean_object* v___x_2083_; lean_object* v___f_2084_; lean_object* v___f_2085_; lean_object* v___f_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___f_2092_; lean_object* v___x_208__overap_2093_; lean_object* v___x_2094_; 
v___x_2073_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_2074_ = lean_ctor_get(v___x_2073_, 0);
v_toFunctor_2075_ = lean_ctor_get(v_toApplicative_2074_, 0);
v_toSeq_2076_ = lean_ctor_get(v_toApplicative_2074_, 2);
v_toSeqLeft_2077_ = lean_ctor_get(v_toApplicative_2074_, 3);
v_toSeqRight_2078_ = lean_ctor_get(v_toApplicative_2074_, 4);
v___f_2079_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_2080_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2075_, 2);
v___f_2081_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2081_, 0, v_toFunctor_2075_);
v___f_2082_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2082_, 0, v_toFunctor_2075_);
v___x_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___f_2081_);
lean_ctor_set(v___x_2083_, 1, v___f_2082_);
lean_inc(v_toSeqRight_2078_);
v___f_2084_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2084_, 0, v_toSeqRight_2078_);
lean_inc(v_toSeqLeft_2077_);
v___f_2085_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2085_, 0, v_toSeqLeft_2077_);
lean_inc(v_toSeq_2076_);
v___f_2086_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2086_, 0, v_toSeq_2076_);
v___x_2087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2083_);
lean_ctor_set(v___x_2087_, 1, v___f_2079_);
lean_ctor_set(v___x_2087_, 2, v___f_2086_);
lean_ctor_set(v___x_2087_, 3, v___f_2085_);
lean_ctor_set(v___x_2087_, 4, v___f_2084_);
v___x_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
lean_ctor_set(v___x_2088_, 1, v___f_2080_);
v___x_2089_ = l_StateRefT_x27_instMonad___redArg(v___x_2088_);
v___x_2090_ = l_Lean_instInhabitedExpr;
v___x_2091_ = l_instInhabitedOfMonad___redArg(v___x_2089_, v___x_2090_);
v___f_2092_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2092_, 0, v___x_2091_);
v___x_208__overap_2093_ = lean_panic_fn_borrowed(v___f_2092_, v_msg_2067_);
lean_dec_ref(v___f_2092_);
lean_inc(v___y_2071_);
lean_inc_ref(v___y_2070_);
lean_inc(v___y_2069_);
lean_inc_ref(v___y_2068_);
v___x_2094_ = lean_apply_5(v___x_208__overap_2093_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, lean_box(0));
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0___boxed(lean_object* v_msg_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v_msg_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
return v_res_2101_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inferAppType___closed__2(void){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2104_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2105_ = lean_unsigned_to_nat(15u);
v___x_2106_ = lean_unsigned_to_nat(258u);
v___x_2107_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__0));
v___x_2108_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2109_ = l_mkPanicMessageWithDecl(v___x_2108_, v___x_2107_, v___x_2106_, v___x_2105_, v___x_2104_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType(uint8_t v_pu_2110_, lean_object* v_fnType_2111_, lean_object* v_args_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
if (v_pu_2110_ == 0)
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2119_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_fnType_2111_, v_args_2112_, v___x_2118_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
return v___x_2119_;
}
else
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
lean_dec_ref(v_args_2112_);
lean_dec_ref(v_fnType_2111_);
v___x_2120_ = lean_obj_once(&l_Lean_Compiler_LCNF_inferAppType___closed__2, &l_Lean_Compiler_LCNF_inferAppType___closed__2_once, _init_l_Lean_Compiler_LCNF_inferAppType___closed__2);
v___x_2121_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2120_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
return v___x_2121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType___boxed(lean_object* v_pu_2122_, lean_object* v_fnType_2123_, lean_object* v_args_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
uint8_t v_pu_boxed_2130_; lean_object* v_res_2131_; 
v_pu_boxed_2130_ = lean_unbox(v_pu_2122_);
v_res_2131_ = l_Lean_Compiler_LCNF_inferAppType(v_pu_boxed_2130_, v_fnType_2123_, v_args_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
lean_dec(v_a_2128_);
lean_dec_ref(v_a_2127_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
return v_res_2131_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Arg_inferType___closed__1(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2133_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2134_ = lean_unsigned_to_nat(15u);
v___x_2135_ = lean_unsigned_to_nat(263u);
v___x_2136_ = ((lean_object*)(l_Lean_Compiler_LCNF_Arg_inferType___closed__0));
v___x_2137_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2138_ = l_mkPanicMessageWithDecl(v___x_2137_, v___x_2136_, v___x_2135_, v___x_2134_, v___x_2133_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType(uint8_t v_pu_2139_, lean_object* v_arg_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
if (v_pu_2139_ == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2147_ = l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(v_arg_2140_, v___x_2146_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
return v___x_2147_;
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
lean_dec(v_arg_2140_);
v___x_2148_ = lean_obj_once(&l_Lean_Compiler_LCNF_Arg_inferType___closed__1, &l_Lean_Compiler_LCNF_Arg_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_Arg_inferType___closed__1);
v___x_2149_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2148_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
return v___x_2149_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType___boxed(lean_object* v_pu_2150_, lean_object* v_arg_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
uint8_t v_pu_boxed_2157_; lean_object* v_res_2158_; 
v_pu_boxed_2157_ = lean_unbox(v_pu_2150_);
v_res_2158_ = l_Lean_Compiler_LCNF_Arg_inferType(v_pu_boxed_2157_, v_arg_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
lean_dec(v_a_2155_);
lean_dec_ref(v_a_2154_);
lean_dec(v_a_2153_);
lean_dec_ref(v_a_2152_);
return v_res_2158_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LetValue_inferType___closed__1(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2160_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2161_ = lean_unsigned_to_nat(15u);
v___x_2162_ = lean_unsigned_to_nat(268u);
v___x_2163_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_inferType___closed__0));
v___x_2164_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2165_ = l_mkPanicMessageWithDecl(v___x_2164_, v___x_2163_, v___x_2162_, v___x_2161_, v___x_2160_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(uint8_t v_pu_2166_, lean_object* v_e_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
if (v_pu_2166_ == 0)
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2174_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(v_e_2167_, v___x_2173_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
return v___x_2174_;
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_dec(v_e_2167_);
v___x_2175_ = lean_obj_once(&l_Lean_Compiler_LCNF_LetValue_inferType___closed__1, &l_Lean_Compiler_LCNF_LetValue_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_LetValue_inferType___closed__1);
v___x_2176_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2175_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
return v___x_2176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType___boxed(lean_object* v_pu_2177_, lean_object* v_e_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_){
_start:
{
uint8_t v_pu_boxed_2184_; lean_object* v_res_2185_; 
v_pu_boxed_2184_ = lean_unbox(v_pu_2177_);
v_res_2185_ = l_Lean_Compiler_LCNF_LetValue_inferType(v_pu_boxed_2184_, v_e_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
lean_dec(v_a_2182_);
lean_dec_ref(v_a_2181_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
return v_res_2185_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_inferType___closed__1(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2187_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2188_ = lean_unsigned_to_nat(15u);
v___x_2189_ = lean_unsigned_to_nat(279u);
v___x_2190_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_inferType___closed__0));
v___x_2191_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2192_ = l_mkPanicMessageWithDecl(v___x_2191_, v___x_2190_, v___x_2189_, v___x_2188_, v___x_2187_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t v_pu_2193_, lean_object* v_code_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_){
_start:
{
if (v_pu_2193_ == 0)
{
switch(lean_obj_tag(v_code_2194_))
{
case 3:
{
lean_object* v_fvarId_2200_; lean_object* v_args_2201_; lean_object* v___x_2202_; 
v_fvarId_2200_ = lean_ctor_get(v_code_2194_, 0);
lean_inc(v_fvarId_2200_);
v_args_2201_ = lean_ctor_get(v_code_2194_, 1);
lean_inc_ref(v_args_2201_);
lean_dec_ref_known(v_code_2194_, 2);
v___x_2202_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2200_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2202_, 1);
v___x_2204_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2205_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2203_, v_args_2201_, v___x_2204_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
return v___x_2205_;
}
else
{
lean_dec_ref(v_args_2201_);
return v___x_2202_;
}
}
case 4:
{
lean_object* v_cases_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2214_; 
v_cases_2206_ = lean_ctor_get(v_code_2194_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_code_2194_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2208_ = v_code_2194_;
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_cases_2206_);
lean_dec(v_code_2194_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v_resultType_2210_; lean_object* v___x_2212_; 
v_resultType_2210_ = lean_ctor_get(v_cases_2206_, 1);
lean_inc_ref(v_resultType_2210_);
lean_dec_ref(v_cases_2206_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set_tag(v___x_2208_, 0);
lean_ctor_set(v___x_2208_, 0, v_resultType_2210_);
v___x_2212_ = v___x_2208_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_resultType_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
case 5:
{
lean_object* v_fvarId_2215_; lean_object* v___x_2216_; 
v_fvarId_2215_ = lean_ctor_get(v_code_2194_, 0);
lean_inc(v_fvarId_2215_);
lean_dec_ref_known(v_code_2194_, 1);
v___x_2216_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2215_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
return v___x_2216_;
}
case 6:
{
lean_object* v_type_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
v_type_2217_ = lean_ctor_get(v_code_2194_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_code_2194_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v_code_2194_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_type_2217_);
lean_dec(v_code_2194_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
lean_ctor_set_tag(v___x_2219_, 0);
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_type_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
default: 
{
lean_object* v_k_2225_; 
v_k_2225_ = lean_ctor_get(v_code_2194_, 1);
lean_inc_ref(v_k_2225_);
lean_dec_ref(v_code_2194_);
v_code_2194_ = v_k_2225_;
goto _start;
}
}
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
lean_dec_ref(v_code_2194_);
v___x_2227_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_inferType___closed__1, &l_Lean_Compiler_LCNF_Code_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_Code_inferType___closed__1);
v___x_2228_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2227_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
return v___x_2228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType___boxed(lean_object* v_pu_2229_, lean_object* v_code_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
uint8_t v_pu_boxed_2236_; lean_object* v_res_2237_; 
v_pu_boxed_2236_ = lean_unbox(v_pu_2229_);
v_res_2237_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_boxed_2236_, v_code_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg(uint8_t v_pu_2238_, lean_object* v_code_2239_, lean_object* v_h__1_2240_, lean_object* v_h__2_2241_){
_start:
{
if (v_pu_2238_ == 0)
{
lean_object* v___x_2242_; 
lean_dec(v_h__2_2241_);
v___x_2242_ = lean_apply_1(v_h__1_2240_, v_code_2239_);
return v___x_2242_;
}
else
{
lean_object* v___x_2243_; 
lean_dec(v_h__1_2240_);
v___x_2243_ = lean_apply_1(v_h__2_2241_, v_code_2239_);
return v___x_2243_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg___boxed(lean_object* v_pu_2244_, lean_object* v_code_2245_, lean_object* v_h__1_2246_, lean_object* v_h__2_2247_){
_start:
{
uint8_t v_pu_32__boxed_2248_; lean_object* v_res_2249_; 
v_pu_32__boxed_2248_ = lean_unbox(v_pu_2244_);
v_res_2249_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg(v_pu_32__boxed_2248_, v_code_2245_, v_h__1_2246_, v_h__2_2247_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter(lean_object* v_motive_2250_, uint8_t v_pu_2251_, lean_object* v_code_2252_, lean_object* v_h__1_2253_, lean_object* v_h__2_2254_){
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___boxed(lean_object* v_motive_2257_, lean_object* v_pu_2258_, lean_object* v_code_2259_, lean_object* v_h__1_2260_, lean_object* v_h__2_2261_){
_start:
{
uint8_t v_pu_39__boxed_2262_; lean_object* v_res_2263_; 
v_pu_39__boxed_2262_ = lean_unbox(v_pu_2258_);
v_res_2263_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter(v_motive_2257_, v_pu_39__boxed_2262_, v_code_2259_, v_h__1_2260_, v_h__2_2261_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__1_splitter___redArg(lean_object* v_code_2264_, lean_object* v_h__1_2265_, lean_object* v_h__2_2266_, lean_object* v_h__3_2267_, lean_object* v_h__4_2268_, lean_object* v_h__5_2269_, lean_object* v_h__6_2270_, lean_object* v_h__7_2271_){
_start:
{
switch(lean_obj_tag(v_code_2264_))
{
case 0:
{
lean_object* v_decl_2272_; lean_object* v_k_2273_; lean_object* v___x_2274_; 
lean_dec(v_h__7_2271_);
lean_dec(v_h__6_2270_);
lean_dec(v_h__5_2269_);
lean_dec(v_h__4_2268_);
lean_dec(v_h__3_2267_);
lean_dec(v_h__2_2266_);
v_decl_2272_ = lean_ctor_get(v_code_2264_, 0);
lean_inc_ref(v_decl_2272_);
v_k_2273_ = lean_ctor_get(v_code_2264_, 1);
lean_inc_ref(v_k_2273_);
lean_dec_ref_known(v_code_2264_, 2);
v___x_2274_ = lean_apply_2(v_h__1_2265_, v_decl_2272_, v_k_2273_);
return v___x_2274_;
}
case 1:
{
lean_object* v_decl_2275_; lean_object* v_k_2276_; lean_object* v___x_2277_; 
lean_dec(v_h__7_2271_);
lean_dec(v_h__6_2270_);
lean_dec(v_h__5_2269_);
lean_dec(v_h__4_2268_);
lean_dec(v_h__3_2267_);
lean_dec(v_h__1_2265_);
v_decl_2275_ = lean_ctor_get(v_code_2264_, 0);
lean_inc_ref(v_decl_2275_);
v_k_2276_ = lean_ctor_get(v_code_2264_, 1);
lean_inc_ref(v_k_2276_);
lean_dec_ref_known(v_code_2264_, 2);
v___x_2277_ = lean_apply_3(v_h__2_2266_, v_decl_2275_, v_k_2276_, lean_box(0));
return v___x_2277_;
}
case 2:
{
lean_object* v_decl_2278_; lean_object* v_k_2279_; lean_object* v___x_2280_; 
lean_dec(v_h__7_2271_);
lean_dec(v_h__6_2270_);
lean_dec(v_h__5_2269_);
lean_dec(v_h__4_2268_);
lean_dec(v_h__2_2266_);
lean_dec(v_h__1_2265_);
v_decl_2278_ = lean_ctor_get(v_code_2264_, 0);
lean_inc_ref(v_decl_2278_);
v_k_2279_ = lean_ctor_get(v_code_2264_, 1);
lean_inc_ref(v_k_2279_);
lean_dec_ref_known(v_code_2264_, 2);
v___x_2280_ = lean_apply_2(v_h__3_2267_, v_decl_2278_, v_k_2279_);
return v___x_2280_;
}
case 3:
{
lean_object* v_fvarId_2281_; lean_object* v_args_2282_; lean_object* v___x_2283_; 
lean_dec(v_h__7_2271_);
lean_dec(v_h__6_2270_);
lean_dec(v_h__4_2268_);
lean_dec(v_h__3_2267_);
lean_dec(v_h__2_2266_);
lean_dec(v_h__1_2265_);
v_fvarId_2281_ = lean_ctor_get(v_code_2264_, 0);
lean_inc(v_fvarId_2281_);
v_args_2282_ = lean_ctor_get(v_code_2264_, 1);
lean_inc_ref(v_args_2282_);
lean_dec_ref_known(v_code_2264_, 2);
v___x_2283_ = lean_apply_2(v_h__5_2269_, v_fvarId_2281_, v_args_2282_);
return v___x_2283_;
}
case 4:
{
lean_object* v_cases_2284_; lean_object* v___x_2285_; 
lean_dec(v_h__6_2270_);
lean_dec(v_h__5_2269_);
lean_dec(v_h__4_2268_);
lean_dec(v_h__3_2267_);
lean_dec(v_h__2_2266_);
lean_dec(v_h__1_2265_);
v_cases_2284_ = lean_ctor_get(v_code_2264_, 0);
lean_inc_ref(v_cases_2284_);
lean_dec_ref_known(v_code_2264_, 1);
v___x_2285_ = lean_apply_1(v_h__7_2271_, v_cases_2284_);
return v___x_2285_;
}
case 5:
{
lean_object* v_fvarId_2286_; lean_object* v___x_2287_; 
lean_dec(v_h__7_2271_);
lean_dec(v_h__6_2270_);
lean_dec(v_h__5_2269_);
lean_dec(v_h__3_2267_);
lean_dec(v_h__2_2266_);
lean_dec(v_h__1_2265_);
v_fvarId_2286_ = lean_ctor_get(v_code_2264_, 0);
lean_inc(v_fvarId_2286_);
lean_dec_ref_known(v_code_2264_, 1);
v___x_2287_ = lean_apply_1(v_h__4_2268_, v_fvarId_2286_);
return v___x_2287_;
}
default: 
{
lean_object* v_type_2288_; lean_object* v___x_2289_; 
lean_dec(v_h__7_2271_);
lean_dec(v_h__5_2269_);
lean_dec(v_h__4_2268_);
lean_dec(v_h__3_2267_);
lean_dec(v_h__2_2266_);
lean_dec(v_h__1_2265_);
v_type_2288_ = lean_ctor_get(v_code_2264_, 0);
lean_inc_ref(v_type_2288_);
lean_dec_ref_known(v_code_2264_, 1);
v___x_2289_ = lean_apply_1(v_h__6_2270_, v_type_2288_);
return v___x_2289_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__1_splitter(lean_object* v_motive_2290_, lean_object* v_code_2291_, lean_object* v_h__1_2292_, lean_object* v_h__2_2293_, lean_object* v_h__3_2294_, lean_object* v_h__4_2295_, lean_object* v_h__5_2296_, lean_object* v_h__6_2297_, lean_object* v_h__7_2298_){
_start:
{
switch(lean_obj_tag(v_code_2291_))
{
case 0:
{
lean_object* v_decl_2299_; lean_object* v_k_2300_; lean_object* v___x_2301_; 
lean_dec(v_h__7_2298_);
lean_dec(v_h__6_2297_);
lean_dec(v_h__5_2296_);
lean_dec(v_h__4_2295_);
lean_dec(v_h__3_2294_);
lean_dec(v_h__2_2293_);
v_decl_2299_ = lean_ctor_get(v_code_2291_, 0);
lean_inc_ref(v_decl_2299_);
v_k_2300_ = lean_ctor_get(v_code_2291_, 1);
lean_inc_ref(v_k_2300_);
lean_dec_ref_known(v_code_2291_, 2);
v___x_2301_ = lean_apply_2(v_h__1_2292_, v_decl_2299_, v_k_2300_);
return v___x_2301_;
}
case 1:
{
lean_object* v_decl_2302_; lean_object* v_k_2303_; lean_object* v___x_2304_; 
lean_dec(v_h__7_2298_);
lean_dec(v_h__6_2297_);
lean_dec(v_h__5_2296_);
lean_dec(v_h__4_2295_);
lean_dec(v_h__3_2294_);
lean_dec(v_h__1_2292_);
v_decl_2302_ = lean_ctor_get(v_code_2291_, 0);
lean_inc_ref(v_decl_2302_);
v_k_2303_ = lean_ctor_get(v_code_2291_, 1);
lean_inc_ref(v_k_2303_);
lean_dec_ref_known(v_code_2291_, 2);
v___x_2304_ = lean_apply_3(v_h__2_2293_, v_decl_2302_, v_k_2303_, lean_box(0));
return v___x_2304_;
}
case 2:
{
lean_object* v_decl_2305_; lean_object* v_k_2306_; lean_object* v___x_2307_; 
lean_dec(v_h__7_2298_);
lean_dec(v_h__6_2297_);
lean_dec(v_h__5_2296_);
lean_dec(v_h__4_2295_);
lean_dec(v_h__2_2293_);
lean_dec(v_h__1_2292_);
v_decl_2305_ = lean_ctor_get(v_code_2291_, 0);
lean_inc_ref(v_decl_2305_);
v_k_2306_ = lean_ctor_get(v_code_2291_, 1);
lean_inc_ref(v_k_2306_);
lean_dec_ref_known(v_code_2291_, 2);
v___x_2307_ = lean_apply_2(v_h__3_2294_, v_decl_2305_, v_k_2306_);
return v___x_2307_;
}
case 3:
{
lean_object* v_fvarId_2308_; lean_object* v_args_2309_; lean_object* v___x_2310_; 
lean_dec(v_h__7_2298_);
lean_dec(v_h__6_2297_);
lean_dec(v_h__4_2295_);
lean_dec(v_h__3_2294_);
lean_dec(v_h__2_2293_);
lean_dec(v_h__1_2292_);
v_fvarId_2308_ = lean_ctor_get(v_code_2291_, 0);
lean_inc(v_fvarId_2308_);
v_args_2309_ = lean_ctor_get(v_code_2291_, 1);
lean_inc_ref(v_args_2309_);
lean_dec_ref_known(v_code_2291_, 2);
v___x_2310_ = lean_apply_2(v_h__5_2296_, v_fvarId_2308_, v_args_2309_);
return v___x_2310_;
}
case 4:
{
lean_object* v_cases_2311_; lean_object* v___x_2312_; 
lean_dec(v_h__6_2297_);
lean_dec(v_h__5_2296_);
lean_dec(v_h__4_2295_);
lean_dec(v_h__3_2294_);
lean_dec(v_h__2_2293_);
lean_dec(v_h__1_2292_);
v_cases_2311_ = lean_ctor_get(v_code_2291_, 0);
lean_inc_ref(v_cases_2311_);
lean_dec_ref_known(v_code_2291_, 1);
v___x_2312_ = lean_apply_1(v_h__7_2298_, v_cases_2311_);
return v___x_2312_;
}
case 5:
{
lean_object* v_fvarId_2313_; lean_object* v___x_2314_; 
lean_dec(v_h__7_2298_);
lean_dec(v_h__6_2297_);
lean_dec(v_h__5_2296_);
lean_dec(v_h__3_2294_);
lean_dec(v_h__2_2293_);
lean_dec(v_h__1_2292_);
v_fvarId_2313_ = lean_ctor_get(v_code_2291_, 0);
lean_inc(v_fvarId_2313_);
lean_dec_ref_known(v_code_2291_, 1);
v___x_2314_ = lean_apply_1(v_h__4_2295_, v_fvarId_2313_);
return v___x_2314_;
}
default: 
{
lean_object* v_type_2315_; lean_object* v___x_2316_; 
lean_dec(v_h__7_2298_);
lean_dec(v_h__5_2296_);
lean_dec(v_h__4_2295_);
lean_dec(v_h__3_2294_);
lean_dec(v_h__2_2293_);
lean_dec(v_h__1_2292_);
v_type_2315_ = lean_ctor_get(v_code_2291_, 0);
lean_inc_ref(v_type_2315_);
lean_dec_ref_known(v_code_2291_, 1);
v___x_2316_ = lean_apply_1(v_h__6_2297_, v_type_2315_);
return v___x_2316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(uint8_t v_pu_2317_, lean_object* v_params_2318_, lean_object* v_code_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2317_, v_code_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; size_t v_sz_2327_; size_t v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref_known(v___x_2325_, 1);
v_sz_2327_ = lean_array_size(v_params_2318_);
v___x_2328_ = ((size_t)0ULL);
v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(v_sz_2327_, v___x_2328_, v_params_2318_);
v___x_2330_ = lean_unsigned_to_nat(32u);
v___x_2331_ = lean_mk_empty_array_with_capacity(v___x_2330_);
lean_dec_ref(v___x_2331_);
v___x_2332_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2333_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v___x_2329_, v_a_2326_, v___x_2332_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
lean_dec(v_a_2326_);
lean_dec_ref(v___x_2329_);
return v___x_2333_;
}
else
{
lean_dec_ref(v_params_2318_);
return v___x_2325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType___boxed(lean_object* v_pu_2334_, lean_object* v_params_2335_, lean_object* v_code_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
uint8_t v_pu_boxed_2342_; lean_object* v_res_2343_; 
v_pu_boxed_2342_ = lean_unbox(v_pu_2334_);
v_res_2343_ = l_Lean_Compiler_LCNF_Code_inferParamType(v_pu_boxed_2342_, v_params_2335_, v_code_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v_a_2340_);
lean_dec_ref(v_a_2339_);
lean_dec(v_a_2338_);
lean_dec_ref(v_a_2337_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType(uint8_t v_pu_2344_, lean_object* v_alt_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
switch(lean_obj_tag(v_alt_2345_))
{
case 0:
{
lean_object* v_code_2351_; lean_object* v___x_2352_; 
v_code_2351_ = lean_ctor_get(v_alt_2345_, 2);
lean_inc_ref(v_code_2351_);
lean_dec_ref_known(v_alt_2345_, 3);
v___x_2352_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2344_, v_code_2351_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
return v___x_2352_;
}
case 1:
{
lean_object* v_code_2353_; lean_object* v___x_2354_; 
v_code_2353_ = lean_ctor_get(v_alt_2345_, 1);
lean_inc_ref(v_code_2353_);
lean_dec_ref_known(v_alt_2345_, 2);
v___x_2354_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2344_, v_code_2353_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
return v___x_2354_;
}
default: 
{
lean_object* v_code_2355_; lean_object* v___x_2356_; 
v_code_2355_ = lean_ctor_get(v_alt_2345_, 0);
lean_inc_ref(v_code_2355_);
lean_dec_ref_known(v_alt_2345_, 1);
v___x_2356_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2344_, v_code_2355_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
return v___x_2356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType___boxed(lean_object* v_pu_2357_, lean_object* v_alt_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
uint8_t v_pu_boxed_2364_; lean_object* v_res_2365_; 
v_pu_boxed_2364_ = lean_unbox(v_pu_2357_);
v_res_2365_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_boxed_2364_, v_alt_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t v_pu_2366_, lean_object* v_e_2367_, lean_object* v_prefixName_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_prefixName_2368_, v_a_2370_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2376_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___x_2374_, 1);
lean_inc(v_e_2367_);
v___x_2376_ = l_Lean_Compiler_LCNF_LetValue_inferType(v_pu_2366_, v_e_2367_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2378_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
lean_dec_ref_known(v___x_2376_, 1);
v___x_2378_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2366_, v_a_2375_, v_a_2377_, v_e_2367_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
return v___x_2378_;
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_dec(v_a_2375_);
lean_dec(v_e_2367_);
v_a_2379_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2376_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2376_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec(v_e_2367_);
v_a_2387_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2374_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2374_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl___boxed(lean_object* v_pu_2395_, lean_object* v_e_2396_, lean_object* v_prefixName_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_){
_start:
{
uint8_t v_pu_boxed_2403_; lean_object* v_res_2404_; 
v_pu_boxed_2403_ = lean_unbox(v_pu_2395_);
v_res_2404_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v_pu_boxed_2403_, v_e_2396_, v_prefixName_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
lean_dec(v_a_2401_);
lean_dec_ref(v_a_2400_);
lean_dec(v_a_2399_);
lean_dec_ref(v_a_2398_);
return v_res_2404_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkForallParams___closed__1(void){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2406_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2407_ = lean_unsigned_to_nat(15u);
v___x_2408_ = lean_unsigned_to_nat(295u);
v___x_2409_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkForallParams___closed__0));
v___x_2410_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2411_ = l_mkPanicMessageWithDecl(v___x_2410_, v___x_2409_, v___x_2408_, v___x_2407_, v___x_2406_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams(uint8_t v_pu_2412_, lean_object* v_params_2413_, lean_object* v_type_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
if (v_pu_2412_ == 0)
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(v_params_2413_, v_type_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
return v___x_2420_;
}
else
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
lean_dec_ref(v_params_2413_);
v___x_2421_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkForallParams___closed__1, &l_Lean_Compiler_LCNF_mkForallParams___closed__1_once, _init_l_Lean_Compiler_LCNF_mkForallParams___closed__1);
v___x_2422_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2421_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
return v___x_2422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams___boxed(lean_object* v_pu_2423_, lean_object* v_params_2424_, lean_object* v_type_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
uint8_t v_pu_boxed_2431_; lean_object* v_res_2432_; 
v_pu_boxed_2431_ = lean_unbox(v_pu_2423_);
v_res_2432_ = l_Lean_Compiler_LCNF_mkForallParams(v_pu_boxed_2431_, v_params_2424_, v_type_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec(v_a_2427_);
lean_dec_ref(v_a_2426_);
lean_dec_ref(v_type_2425_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(uint8_t v_pu_2433_, lean_object* v_params_2434_, lean_object* v_code_2435_, lean_object* v_prefixName_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v___x_2442_; 
lean_inc_ref(v_code_2435_);
v___x_2442_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2433_, v_code_2435_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2444_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2443_);
lean_dec_ref_known(v___x_2442_, 1);
lean_inc_ref(v_params_2434_);
v___x_2444_ = l_Lean_Compiler_LCNF_mkForallParams(v_pu_2433_, v_params_2434_, v_a_2443_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
lean_dec(v_a_2443_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2446_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
lean_inc(v_a_2445_);
lean_dec_ref_known(v___x_2444_, 1);
v___x_2446_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_prefixName_2436_, v_a_2438_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; lean_object* v___x_2448_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_a_2447_);
lean_dec_ref_known(v___x_2446_, 1);
v___x_2448_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_2433_, v_a_2447_, v_a_2445_, v_params_2434_, v_code_2435_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
return v___x_2448_;
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_dec(v_a_2445_);
lean_dec_ref(v_code_2435_);
lean_dec_ref(v_params_2434_);
v_a_2449_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2446_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2446_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_dec(v_prefixName_2436_);
lean_dec_ref(v_code_2435_);
lean_dec_ref(v_params_2434_);
v_a_2457_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2444_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2444_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec(v_prefixName_2436_);
lean_dec_ref(v_code_2435_);
lean_dec_ref(v_params_2434_);
v_a_2465_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2442_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2442_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux___boxed(lean_object* v_pu_2473_, lean_object* v_params_2474_, lean_object* v_code_2475_, lean_object* v_prefixName_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_){
_start:
{
uint8_t v_pu_boxed_2482_; lean_object* v_res_2483_; 
v_pu_boxed_2482_ = lean_unbox(v_pu_2473_);
v_res_2483_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_boxed_2482_, v_params_2474_, v_code_2475_, v_prefixName_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_);
lean_dec(v_a_2480_);
lean_dec_ref(v_a_2479_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object* v_params_2484_, lean_object* v_code_2485_, lean_object* v_prefixName_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
uint8_t v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = 0;
v___x_2493_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v___x_2492_, v_params_2484_, v_code_2485_, v_prefixName_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl___boxed(lean_object* v_params_2494_, lean_object* v_code_2495_, lean_object* v_prefixName_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v_params_2494_, v_code_2495_, v_prefixName_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_);
lean_dec(v_a_2500_);
lean_dec_ref(v_a_2499_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(uint8_t v_pu_2503_, lean_object* v_params_2504_, lean_object* v_code_2505_, lean_object* v_prefixName_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_2503_, v_params_2504_, v_code_2505_, v_prefixName_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl___boxed(lean_object* v_pu_2513_, lean_object* v_params_2514_, lean_object* v_code_2515_, lean_object* v_prefixName_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_){
_start:
{
uint8_t v_pu_boxed_2522_; lean_object* v_res_2523_; 
v_pu_boxed_2522_ = lean_unbox(v_pu_2513_);
v_res_2523_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v_pu_boxed_2522_, v_params_2514_, v_code_2515_, v_prefixName_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
lean_dec(v_a_2520_);
lean_dec_ref(v_a_2519_);
lean_dec(v_a_2518_);
lean_dec_ref(v_a_2517_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(uint8_t v_pu_2524_, lean_object* v_param_2525_, lean_object* v_code_2526_, lean_object* v_prefixName_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v_params_2535_; lean_object* v___x_2536_; 
v___x_2533_ = lean_unsigned_to_nat(1u);
v___x_2534_ = lean_mk_empty_array_with_capacity(v___x_2533_);
v_params_2535_ = lean_array_push(v___x_2534_, v_param_2525_);
v___x_2536_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_2524_, v_params_2535_, v_code_2526_, v_prefixName_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___boxed(lean_object* v_pu_2537_, lean_object* v_param_2538_, lean_object* v_code_2539_, lean_object* v_prefixName_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_){
_start:
{
uint8_t v_pu_boxed_2546_; lean_object* v_res_2547_; 
v_pu_boxed_2546_ = lean_unbox(v_pu_2537_);
v_res_2547_ = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(v_pu_boxed_2546_, v_param_2538_, v_code_2539_, v_prefixName_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(lean_object* v_msg_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v_toCold_2554_; lean_object* v_ref_2555_; lean_object* v___x_2556_; lean_object* v_env_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v_toCold_2554_ = lean_ctor_get(v___y_2551_, 0);
v_ref_2555_ = lean_ctor_get(v___y_2551_, 2);
v___x_2556_ = lean_st_ref_get(v___y_2552_);
v_env_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc_ref(v_env_2557_);
lean_dec(v___x_2556_);
v___x_2558_ = lean_st_ref_get(v___y_2550_);
v___x_2559_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_2549_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2582_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2582_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2582_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v_lctx_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2580_; 
v_lctx_2564_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2580_ == 0)
{
lean_object* v_unused_2581_; 
v_unused_2581_ = lean_ctor_get(v___x_2558_, 1);
lean_dec(v_unused_2581_);
v___x_2566_ = v___x_2558_;
v_isShared_2567_ = v_isSharedCheck_2580_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_lctx_2564_);
lean_dec(v___x_2558_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2580_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v_options_2568_; uint8_t v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2574_; 
v_options_2568_ = lean_ctor_get(v_toCold_2554_, 2);
v___x_2569_ = lean_unbox(v_a_2560_);
lean_dec(v_a_2560_);
v___x_2570_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2564_, v___x_2569_);
lean_dec_ref(v_lctx_2564_);
v___x_2571_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1);
lean_inc_ref(v_options_2568_);
v___x_2572_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2572_, 0, v_env_2557_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
lean_ctor_set(v___x_2572_, 2, v___x_2570_);
lean_ctor_set(v___x_2572_, 3, v_options_2568_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set_tag(v___x_2566_, 3);
lean_ctor_set(v___x_2566_, 1, v_msg_2548_);
lean_ctor_set(v___x_2566_, 0, v___x_2572_);
v___x_2574_ = v___x_2566_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v_msg_2548_);
v___x_2574_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
lean_inc(v_ref_2555_);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v_ref_2555_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set_tag(v___x_2562_, 1);
lean_ctor_set(v___x_2562_, 0, v___x_2575_);
v___x_2577_ = v___x_2562_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
lean_dec(v___x_2558_);
lean_dec_ref(v_env_2557_);
lean_dec_ref(v_msg_2548_);
v_a_2583_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2559_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2559_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg___boxed(lean_object* v_msg_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v_msg_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1(lean_object* v_00_u03b1_2598_, lean_object* v_msg_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v_msg_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___boxed(lean_object* v_00_u03b1_2606_, lean_object* v_msg_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1(v_00_u03b1_2606_, v_msg_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(uint8_t v_pu_2614_, lean_object* v_a_2615_, lean_object* v_b_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v_array_2622_; lean_object* v_start_2623_; lean_object* v_stop_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2640_; 
v_array_2622_ = lean_ctor_get(v_a_2615_, 0);
v_start_2623_ = lean_ctor_get(v_a_2615_, 1);
v_stop_2624_ = lean_ctor_get(v_a_2615_, 2);
v_isSharedCheck_2640_ = !lean_is_exclusive(v_a_2615_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2626_ = v_a_2615_;
v_isShared_2627_ = v_isSharedCheck_2640_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_stop_2624_);
lean_inc(v_start_2623_);
lean_inc(v_array_2622_);
lean_dec(v_a_2615_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2640_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
uint8_t v___x_2628_; 
v___x_2628_ = lean_nat_dec_lt(v_start_2623_, v_stop_2624_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; 
lean_del_object(v___x_2626_);
lean_dec(v_stop_2624_);
lean_dec(v_start_2623_);
lean_dec_ref(v_array_2622_);
v___x_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2629_, 0, v_b_2616_);
return v___x_2629_;
}
else
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2633_; 
v___x_2630_ = lean_unsigned_to_nat(1u);
v___x_2631_ = lean_nat_add(v_start_2623_, v___x_2630_);
lean_inc_ref(v_array_2622_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 1, v___x_2631_);
v___x_2633_ = v___x_2626_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_array_2622_);
lean_ctor_set(v_reuseFailAlloc_2639_, 1, v___x_2631_);
lean_ctor_set(v_reuseFailAlloc_2639_, 2, v_stop_2624_);
v___x_2633_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = lean_array_fget(v_array_2622_, v_start_2623_);
lean_dec(v_start_2623_);
lean_dec_ref(v_array_2622_);
v___x_2635_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_2614_, v___x_2634_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; lean_object* v___x_2637_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2636_);
lean_dec_ref_known(v___x_2635_, 1);
v___x_2637_ = l_Lean_Compiler_LCNF_joinTypes(v_b_2616_, v_a_2636_);
v_a_2615_ = v___x_2633_;
v_b_2616_ = v___x_2637_;
goto _start;
}
else
{
lean_dec_ref(v___x_2633_);
lean_dec_ref(v_b_2616_);
return v___x_2635_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg___boxed(lean_object* v_pu_2641_, lean_object* v_a_2642_, lean_object* v_b_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
uint8_t v_pu_boxed_2649_; lean_object* v_res_2650_; 
v_pu_boxed_2649_ = lean_unbox(v_pu_2641_);
v_res_2650_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_boxed_2649_, v_a_2642_, v_b_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
return v_res_2650_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__0(void){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
return v___x_2651_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__2(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkCasesResultType___closed__1));
v___x_2654_ = l_Lean_stringToMessageData(v___x_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(uint8_t v_pu_2655_, lean_object* v_alts_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v___x_2662_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___x_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v___x_2662_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkCasesResultType___closed__0, &l_Lean_Compiler_LCNF_mkCasesResultType___closed__0_once, _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__0);
v___x_2676_ = lean_array_get_size(v_alts_2656_);
v___x_2677_ = lean_unsigned_to_nat(0u);
v___x_2678_ = lean_nat_dec_eq(v___x_2676_, v___x_2677_);
if (v___x_2678_ == 0)
{
v___y_2664_ = v_a_2657_;
v___y_2665_ = v_a_2658_;
v___y_2666_ = v_a_2659_;
v___y_2667_ = v_a_2660_;
goto v___jp_2663_;
}
else
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
lean_dec_ref(v_alts_2656_);
v___x_2679_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkCasesResultType___closed__2, &l_Lean_Compiler_LCNF_mkCasesResultType___closed__2_once, _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__2);
v___x_2680_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v___x_2679_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v___x_2680_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2680_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2681_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
v___jp_2663_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2668_ = lean_unsigned_to_nat(0u);
v___x_2669_ = lean_array_get_borrowed(v___x_2662_, v_alts_2656_, v___x_2668_);
lean_inc(v___x_2669_);
v___x_2670_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_2655_, v___x_2669_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v___x_2670_, 1);
v___x_2672_ = lean_unsigned_to_nat(1u);
v___x_2673_ = lean_array_get_size(v_alts_2656_);
v___x_2674_ = l_Array_toSubarray___redArg(v_alts_2656_, v___x_2672_, v___x_2673_);
v___x_2675_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_2655_, v___x_2674_, v_a_2671_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
return v___x_2675_;
}
else
{
lean_dec_ref(v_alts_2656_);
return v___x_2670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___boxed(lean_object* v_pu_2689_, lean_object* v_alts_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
uint8_t v_pu_boxed_2696_; lean_object* v_res_2697_; 
v_pu_boxed_2696_ = lean_unbox(v_pu_2689_);
v_res_2697_ = l_Lean_Compiler_LCNF_mkCasesResultType(v_pu_boxed_2696_, v_alts_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
lean_dec(v_a_2694_);
lean_dec_ref(v_a_2693_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0(uint8_t v_pu_2698_, lean_object* v_inst_2699_, lean_object* v_R_2700_, lean_object* v_a_2701_, lean_object* v_b_2702_, lean_object* v_c_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_2698_, v_a_2701_, v_b_2702_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___boxed(lean_object* v_pu_2710_, lean_object* v_inst_2711_, lean_object* v_R_2712_, lean_object* v_a_2713_, lean_object* v_b_2714_, lean_object* v_c_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
uint8_t v_pu_boxed_2721_; lean_object* v_res_2722_; 
v_pu_boxed_2721_ = lean_unbox(v_pu_2710_);
v_res_2722_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0(v_pu_boxed_2721_, v_inst_2711_, v_R_2712_, v_a_2713_, v_b_2714_, v_c_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(lean_object* v_msg_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; lean_object* v_toApplicative_2730_; lean_object* v_toFunctor_2731_; lean_object* v_toSeq_2732_; lean_object* v_toSeqLeft_2733_; lean_object* v_toSeqRight_2734_; lean_object* v___f_2735_; lean_object* v___f_2736_; lean_object* v___f_2737_; lean_object* v___f_2738_; lean_object* v___x_2739_; lean_object* v___f_2740_; lean_object* v___f_2741_; lean_object* v___f_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; uint8_t v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___f_2749_; lean_object* v___x_970__overap_2750_; lean_object* v___x_2751_; 
v___x_2729_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_2730_ = lean_ctor_get(v___x_2729_, 0);
v_toFunctor_2731_ = lean_ctor_get(v_toApplicative_2730_, 0);
v_toSeq_2732_ = lean_ctor_get(v_toApplicative_2730_, 2);
v_toSeqLeft_2733_ = lean_ctor_get(v_toApplicative_2730_, 3);
v_toSeqRight_2734_ = lean_ctor_get(v_toApplicative_2730_, 4);
v___f_2735_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_2736_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2731_, 2);
v___f_2737_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2737_, 0, v_toFunctor_2731_);
v___f_2738_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2738_, 0, v_toFunctor_2731_);
v___x_2739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___f_2737_);
lean_ctor_set(v___x_2739_, 1, v___f_2738_);
lean_inc(v_toSeqRight_2734_);
v___f_2740_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2740_, 0, v_toSeqRight_2734_);
lean_inc(v_toSeqLeft_2733_);
v___f_2741_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2741_, 0, v_toSeqLeft_2733_);
lean_inc(v_toSeq_2732_);
v___f_2742_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2742_, 0, v_toSeq_2732_);
v___x_2743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2739_);
lean_ctor_set(v___x_2743_, 1, v___f_2735_);
lean_ctor_set(v___x_2743_, 2, v___f_2742_);
lean_ctor_set(v___x_2743_, 3, v___f_2741_);
lean_ctor_set(v___x_2743_, 4, v___f_2740_);
v___x_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
lean_ctor_set(v___x_2744_, 1, v___f_2736_);
v___x_2745_ = l_StateRefT_x27_instMonad___redArg(v___x_2744_);
v___x_2746_ = 0;
v___x_2747_ = lean_box(v___x_2746_);
v___x_2748_ = l_instInhabitedOfMonad___redArg(v___x_2745_, v___x_2747_);
v___f_2749_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2749_, 0, v___x_2748_);
v___x_970__overap_2750_ = lean_panic_fn_borrowed(v___f_2749_, v_msg_2723_);
lean_dec_ref(v___f_2749_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
v___x_2751_ = lean_apply_5(v___x_970__overap_2750_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, lean_box(0));
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0___boxed(lean_object* v_msg_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(v_msg_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
return v_res_2758_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1(void){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2760_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2));
v___x_2761_ = lean_unsigned_to_nat(50u);
v___x_2762_ = lean_unsigned_to_nat(345u);
v___x_2763_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__0));
v___x_2764_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2765_ = l_mkPanicMessageWithDecl(v___x_2764_, v___x_2763_, v___x_2762_, v___x_2761_, v___x_2760_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(lean_object* v_type_2766_, lean_object* v_predVars_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v_t_2774_; lean_object* v_b_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v_type_2784_; 
v_type_2784_ = l_Lean_Expr_headBeta(v_type_2766_);
switch(lean_obj_tag(v_type_2784_))
{
case 0:
{
lean_object* v_deBruijnIndex_2785_; uint8_t v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_deBruijnIndex_2785_ = lean_ctor_get(v_type_2784_, 0);
lean_inc(v_deBruijnIndex_2785_);
lean_dec_ref_known(v_type_2784_, 1);
v___x_2786_ = 0;
v___x_2787_ = lean_array_get_size(v_predVars_2767_);
v___x_2788_ = lean_nat_sub(v___x_2787_, v_deBruijnIndex_2785_);
lean_dec(v_deBruijnIndex_2785_);
v___x_2789_ = lean_unsigned_to_nat(1u);
v___x_2790_ = lean_nat_sub(v___x_2788_, v___x_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(v___x_2786_);
v___x_2792_ = lean_array_get(v___x_2791_, v_predVars_2767_, v___x_2790_);
lean_dec(v___x_2790_);
lean_dec_ref(v_predVars_2767_);
lean_dec(v___x_2791_);
v___x_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
return v___x_2793_;
}
case 1:
{
lean_object* v_fvarId_2794_; lean_object* v___x_2795_; 
lean_dec_ref(v_predVars_2767_);
v_fvarId_2794_ = lean_ctor_get(v_type_2784_, 0);
lean_inc(v_fvarId_2794_);
lean_dec_ref_known(v_type_2784_, 1);
v___x_2795_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2794_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2805_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2798_ = v___x_2795_;
v_isShared_2799_ = v_isSharedCheck_2805_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2795_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2805_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
uint8_t v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2803_; 
v___x_2800_ = l_Lean_Compiler_LCNF_isPredicateType(v_a_2796_);
v___x_2801_ = lean_box(v___x_2800_);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2801_);
v___x_2803_ = v___x_2798_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2801_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
v_a_2806_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2795_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2795_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
case 3:
{
uint8_t v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
lean_dec_ref_known(v_type_2784_, 1);
lean_dec_ref(v_predVars_2767_);
v___x_2814_ = 0;
v___x_2815_ = lean_box(v___x_2814_);
v___x_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2815_);
return v___x_2816_;
}
case 4:
{
uint8_t v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
lean_dec_ref(v_predVars_2767_);
v___x_2817_ = l_Lean_Expr_isErased(v_type_2784_);
lean_dec_ref_known(v_type_2784_, 2);
v___x_2818_ = lean_box(v___x_2817_);
v___x_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2818_);
return v___x_2819_;
}
case 5:
{
lean_object* v_fn_2820_; 
v_fn_2820_ = lean_ctor_get(v_type_2784_, 0);
lean_inc_ref(v_fn_2820_);
lean_dec_ref_known(v_type_2784_, 2);
v_type_2766_ = v_fn_2820_;
goto _start;
}
case 6:
{
lean_object* v_binderType_2822_; lean_object* v_body_2823_; 
v_binderType_2822_ = lean_ctor_get(v_type_2784_, 1);
lean_inc_ref(v_binderType_2822_);
v_body_2823_ = lean_ctor_get(v_type_2784_, 2);
lean_inc_ref(v_body_2823_);
lean_dec_ref_known(v_type_2784_, 3);
v_t_2774_ = v_binderType_2822_;
v_b_2775_ = v_body_2823_;
v___y_2776_ = v_a_2768_;
v___y_2777_ = v_a_2769_;
v___y_2778_ = v_a_2770_;
v___y_2779_ = v_a_2771_;
goto v___jp_2773_;
}
case 7:
{
lean_object* v_binderType_2824_; lean_object* v_body_2825_; 
v_binderType_2824_ = lean_ctor_get(v_type_2784_, 1);
lean_inc_ref(v_binderType_2824_);
v_body_2825_ = lean_ctor_get(v_type_2784_, 2);
lean_inc_ref(v_body_2825_);
lean_dec_ref_known(v_type_2784_, 3);
v_t_2774_ = v_binderType_2824_;
v_b_2775_ = v_body_2825_;
v___y_2776_ = v_a_2768_;
v___y_2777_ = v_a_2769_;
v___y_2778_ = v_a_2770_;
v___y_2779_ = v_a_2771_;
goto v___jp_2773_;
}
case 10:
{
lean_object* v_expr_2826_; 
v_expr_2826_ = lean_ctor_get(v_type_2784_, 1);
lean_inc_ref(v_expr_2826_);
lean_dec_ref_known(v_type_2784_, 2);
v_type_2766_ = v_expr_2826_;
goto _start;
}
default: 
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
lean_dec_ref(v_type_2784_);
lean_dec_ref(v_predVars_2767_);
v___x_2828_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1, &l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1);
v___x_2829_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(v___x_2828_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_);
return v___x_2829_;
}
}
v___jp_2773_:
{
uint8_t v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2780_ = l_Lean_Compiler_LCNF_isPredicateType(v_t_2774_);
v___x_2781_ = lean_box(v___x_2780_);
v___x_2782_ = lean_array_push(v_predVars_2767_, v___x_2781_);
v_type_2766_ = v_b_2775_;
v_predVars_2767_ = v___x_2782_;
v_a_2768_ = v___y_2776_;
v_a_2769_ = v___y_2777_;
v_a_2770_ = v___y_2778_;
v_a_2771_ = v___y_2779_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___boxed(lean_object* v_type_2830_, lean_object* v_predVars_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(v_type_2830_, v_predVars_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible(lean_object* v_type_2838_, lean_object* v_predVars_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_){
_start:
{
lean_object* v___x_2845_; 
v___x_2845_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(v_type_2838_, v_predVars_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible___boxed(lean_object* v_type_2846_, lean_object* v_predVars_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_Compiler_LCNF_isErasedCompatible(v_type_2846_, v_predVars_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
return v_res_2853_;
}
}
LEAN_EXPORT uint8_t l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(lean_object* v_x_2854_, lean_object* v_x_2855_){
_start:
{
if (lean_obj_tag(v_x_2854_) == 0)
{
if (lean_obj_tag(v_x_2855_) == 0)
{
uint8_t v___x_2856_; 
v___x_2856_ = 1;
return v___x_2856_;
}
else
{
uint8_t v___x_2857_; 
v___x_2857_ = 0;
return v___x_2857_;
}
}
else
{
if (lean_obj_tag(v_x_2855_) == 0)
{
uint8_t v___x_2858_; 
v___x_2858_ = 0;
return v___x_2858_;
}
else
{
lean_object* v_head_2859_; lean_object* v_tail_2860_; lean_object* v_head_2861_; lean_object* v_tail_2862_; uint8_t v___x_2863_; 
v_head_2859_ = lean_ctor_get(v_x_2854_, 0);
v_tail_2860_ = lean_ctor_get(v_x_2854_, 1);
v_head_2861_ = lean_ctor_get(v_x_2855_, 0);
v_tail_2862_ = lean_ctor_get(v_x_2855_, 1);
v___x_2863_ = l_Lean_Level_isEquiv(v_head_2859_, v_head_2861_);
if (v___x_2863_ == 0)
{
return v___x_2863_;
}
else
{
v_x_2854_ = v_tail_2860_;
v_x_2855_ = v_tail_2862_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0___boxed(lean_object* v_x_2865_, lean_object* v_x_2866_){
_start:
{
uint8_t v_res_2867_; lean_object* v_r_2868_; 
v_res_2867_ = l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(v_x_2865_, v_x_2866_);
lean_dec(v_x_2866_);
lean_dec(v_x_2865_);
v_r_2868_ = lean_box(v_res_2867_);
return v_r_2868_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_eqvTypes(lean_object* v_a_2869_, lean_object* v_b_2870_){
_start:
{
uint8_t v___x_2871_; lean_object* v_d_u2081_2873_; lean_object* v_b_u2081_2874_; lean_object* v_d_u2082_2875_; lean_object* v_b_u2082_2876_; uint8_t v___x_2879_; uint8_t v___y_2881_; 
v___x_2871_ = lean_expr_eqv(v_a_2869_, v_b_2870_);
v___x_2879_ = 1;
if (v___x_2871_ == 0)
{
uint8_t v___x_2925_; 
v___x_2925_ = l_Lean_Expr_isErased(v_a_2869_);
if (v___x_2925_ == 0)
{
v___y_2881_ = v___x_2871_;
goto v___jp_2880_;
}
else
{
uint8_t v___x_2926_; 
v___x_2926_ = l_Lean_Expr_isErased(v_b_2870_);
v___y_2881_ = v___x_2926_;
goto v___jp_2880_;
}
}
else
{
lean_dec_ref(v_b_2870_);
lean_dec_ref(v_a_2869_);
return v___x_2879_;
}
v___jp_2872_:
{
uint8_t v___x_2877_; 
v___x_2877_ = l_Lean_Compiler_LCNF_eqvTypes(v_d_u2081_2873_, v_d_u2082_2875_);
if (v___x_2877_ == 0)
{
lean_dec_ref(v_b_u2082_2876_);
lean_dec_ref(v_b_u2081_2874_);
return v___x_2871_;
}
else
{
v_a_2869_ = v_b_u2081_2874_;
v_b_2870_ = v_b_u2082_2876_;
goto _start;
}
}
v___jp_2880_:
{
if (v___y_2881_ == 0)
{
lean_object* v_a_x27_2882_; lean_object* v_b_x27_2883_; uint8_t v___x_2884_; 
lean_inc_ref(v_a_2869_);
v_a_x27_2882_ = l_Lean_Expr_headBeta(v_a_2869_);
lean_inc_ref(v_b_2870_);
v_b_x27_2883_ = l_Lean_Expr_headBeta(v_b_2870_);
v___x_2884_ = lean_expr_eqv(v_a_2869_, v_a_x27_2882_);
if (v___x_2884_ == 0)
{
lean_dec_ref(v_b_2870_);
lean_dec_ref(v_a_2869_);
v_a_2869_ = v_a_x27_2882_;
v_b_2870_ = v_b_x27_2883_;
goto _start;
}
else
{
uint8_t v___x_2886_; 
v___x_2886_ = lean_expr_eqv(v_b_2870_, v_b_x27_2883_);
if (v___x_2886_ == 0)
{
lean_dec_ref(v_b_2870_);
lean_dec_ref(v_a_2869_);
v_a_2869_ = v_a_x27_2882_;
v_b_2870_ = v_b_x27_2883_;
goto _start;
}
else
{
lean_dec_ref(v_b_x27_2883_);
lean_dec_ref(v_a_x27_2882_);
switch(lean_obj_tag(v_a_2869_))
{
case 10:
{
lean_object* v_expr_2888_; 
v_expr_2888_ = lean_ctor_get(v_a_2869_, 1);
lean_inc_ref(v_expr_2888_);
lean_dec_ref_known(v_a_2869_, 2);
v_a_2869_ = v_expr_2888_;
goto _start;
}
case 5:
{
switch(lean_obj_tag(v_b_2870_))
{
case 10:
{
lean_object* v_expr_2890_; 
v_expr_2890_ = lean_ctor_get(v_b_2870_, 1);
lean_inc_ref(v_expr_2890_);
lean_dec_ref_known(v_b_2870_, 2);
v_b_2870_ = v_expr_2890_;
goto _start;
}
case 5:
{
lean_object* v_fn_2892_; lean_object* v_arg_2893_; lean_object* v_fn_2894_; lean_object* v_arg_2895_; uint8_t v___x_2896_; 
v_fn_2892_ = lean_ctor_get(v_a_2869_, 0);
lean_inc_ref(v_fn_2892_);
v_arg_2893_ = lean_ctor_get(v_a_2869_, 1);
lean_inc_ref(v_arg_2893_);
lean_dec_ref_known(v_a_2869_, 2);
v_fn_2894_ = lean_ctor_get(v_b_2870_, 0);
lean_inc_ref(v_fn_2894_);
v_arg_2895_ = lean_ctor_get(v_b_2870_, 1);
lean_inc_ref(v_arg_2895_);
lean_dec_ref_known(v_b_2870_, 2);
v___x_2896_ = l_Lean_Compiler_LCNF_eqvTypes(v_fn_2892_, v_fn_2894_);
if (v___x_2896_ == 0)
{
lean_dec_ref(v_arg_2895_);
lean_dec_ref(v_arg_2893_);
return v___x_2871_;
}
else
{
v_a_2869_ = v_arg_2893_;
v_b_2870_ = v_arg_2895_;
goto _start;
}
}
default: 
{
lean_dec_ref_known(v_a_2869_, 2);
lean_dec_ref(v_b_2870_);
return v___y_2881_;
}
}
}
case 7:
{
switch(lean_obj_tag(v_b_2870_))
{
case 10:
{
lean_object* v_expr_2898_; 
v_expr_2898_ = lean_ctor_get(v_b_2870_, 1);
lean_inc_ref(v_expr_2898_);
lean_dec_ref_known(v_b_2870_, 2);
v_b_2870_ = v_expr_2898_;
goto _start;
}
case 7:
{
lean_object* v_binderType_2900_; lean_object* v_body_2901_; lean_object* v_binderType_2902_; lean_object* v_body_2903_; 
v_binderType_2900_ = lean_ctor_get(v_a_2869_, 1);
lean_inc_ref(v_binderType_2900_);
v_body_2901_ = lean_ctor_get(v_a_2869_, 2);
lean_inc_ref(v_body_2901_);
lean_dec_ref_known(v_a_2869_, 3);
v_binderType_2902_ = lean_ctor_get(v_b_2870_, 1);
lean_inc_ref(v_binderType_2902_);
v_body_2903_ = lean_ctor_get(v_b_2870_, 2);
lean_inc_ref(v_body_2903_);
lean_dec_ref_known(v_b_2870_, 3);
v_d_u2081_2873_ = v_binderType_2900_;
v_b_u2081_2874_ = v_body_2901_;
v_d_u2082_2875_ = v_binderType_2902_;
v_b_u2082_2876_ = v_body_2903_;
goto v___jp_2872_;
}
default: 
{
lean_dec_ref_known(v_a_2869_, 3);
lean_dec_ref(v_b_2870_);
return v___y_2881_;
}
}
}
case 6:
{
switch(lean_obj_tag(v_b_2870_))
{
case 10:
{
lean_object* v_expr_2904_; 
v_expr_2904_ = lean_ctor_get(v_b_2870_, 1);
lean_inc_ref(v_expr_2904_);
lean_dec_ref_known(v_b_2870_, 2);
v_b_2870_ = v_expr_2904_;
goto _start;
}
case 6:
{
lean_object* v_binderType_2906_; lean_object* v_body_2907_; lean_object* v_binderType_2908_; lean_object* v_body_2909_; 
v_binderType_2906_ = lean_ctor_get(v_a_2869_, 1);
lean_inc_ref(v_binderType_2906_);
v_body_2907_ = lean_ctor_get(v_a_2869_, 2);
lean_inc_ref(v_body_2907_);
lean_dec_ref_known(v_a_2869_, 3);
v_binderType_2908_ = lean_ctor_get(v_b_2870_, 1);
lean_inc_ref(v_binderType_2908_);
v_body_2909_ = lean_ctor_get(v_b_2870_, 2);
lean_inc_ref(v_body_2909_);
lean_dec_ref_known(v_b_2870_, 3);
v_d_u2081_2873_ = v_binderType_2906_;
v_b_u2081_2874_ = v_body_2907_;
v_d_u2082_2875_ = v_binderType_2908_;
v_b_u2082_2876_ = v_body_2909_;
goto v___jp_2872_;
}
default: 
{
lean_dec_ref_known(v_a_2869_, 3);
lean_dec_ref(v_b_2870_);
return v___y_2881_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_b_2870_))
{
case 10:
{
lean_object* v_expr_2910_; 
v_expr_2910_ = lean_ctor_get(v_b_2870_, 1);
lean_inc_ref(v_expr_2910_);
lean_dec_ref_known(v_b_2870_, 2);
v_b_2870_ = v_expr_2910_;
goto _start;
}
case 3:
{
lean_object* v_u_2912_; lean_object* v_u_2913_; uint8_t v___x_2914_; 
v_u_2912_ = lean_ctor_get(v_a_2869_, 0);
lean_inc(v_u_2912_);
lean_dec_ref_known(v_a_2869_, 1);
v_u_2913_ = lean_ctor_get(v_b_2870_, 0);
lean_inc(v_u_2913_);
lean_dec_ref_known(v_b_2870_, 1);
v___x_2914_ = l_Lean_Level_isEquiv(v_u_2912_, v_u_2913_);
lean_dec(v_u_2913_);
lean_dec(v_u_2912_);
return v___x_2914_;
}
default: 
{
lean_dec_ref_known(v_a_2869_, 1);
lean_dec_ref(v_b_2870_);
return v___y_2881_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_b_2870_))
{
case 10:
{
lean_object* v_expr_2915_; 
v_expr_2915_ = lean_ctor_get(v_b_2870_, 1);
lean_inc_ref(v_expr_2915_);
lean_dec_ref_known(v_b_2870_, 2);
v_b_2870_ = v_expr_2915_;
goto _start;
}
case 4:
{
lean_object* v_declName_2917_; lean_object* v_us_2918_; lean_object* v_declName_2919_; lean_object* v_us_2920_; uint8_t v___x_2921_; 
v_declName_2917_ = lean_ctor_get(v_a_2869_, 0);
lean_inc(v_declName_2917_);
v_us_2918_ = lean_ctor_get(v_a_2869_, 1);
lean_inc(v_us_2918_);
lean_dec_ref_known(v_a_2869_, 2);
v_declName_2919_ = lean_ctor_get(v_b_2870_, 0);
lean_inc(v_declName_2919_);
v_us_2920_ = lean_ctor_get(v_b_2870_, 1);
lean_inc(v_us_2920_);
lean_dec_ref_known(v_b_2870_, 2);
v___x_2921_ = lean_name_eq(v_declName_2917_, v_declName_2919_);
lean_dec(v_declName_2919_);
lean_dec(v_declName_2917_);
if (v___x_2921_ == 0)
{
lean_dec(v_us_2920_);
lean_dec(v_us_2918_);
return v___x_2871_;
}
else
{
uint8_t v___x_2922_; 
v___x_2922_ = l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(v_us_2918_, v_us_2920_);
lean_dec(v_us_2920_);
lean_dec(v_us_2918_);
return v___x_2922_;
}
}
default: 
{
lean_dec_ref_known(v_a_2869_, 2);
lean_dec_ref(v_b_2870_);
return v___y_2881_;
}
}
}
default: 
{
if (lean_obj_tag(v_b_2870_) == 10)
{
lean_object* v_expr_2923_; 
v_expr_2923_ = lean_ctor_get(v_b_2870_, 1);
lean_inc_ref(v_expr_2923_);
lean_dec_ref_known(v_b_2870_, 2);
v_b_2870_ = v_expr_2923_;
goto _start;
}
else
{
lean_dec_ref(v_b_2870_);
lean_dec_ref(v_a_2869_);
return v___y_2881_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_b_2870_);
lean_dec_ref(v_a_2869_);
return v___x_2879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eqvTypes___boxed(lean_object* v_a_2927_, lean_object* v_b_2928_){
_start:
{
uint8_t v_res_2929_; lean_object* v_r_2930_; 
v_res_2929_ = l_Lean_Compiler_LCNF_eqvTypes(v_a_2927_, v_b_2928_);
v_r_2930_ = lean_box(v_res_2929_);
return v_r_2930_;
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
