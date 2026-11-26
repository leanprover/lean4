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
lean_object* l_instInhabitedReaderT___redArg___lam__0___boxed(lean_object*, lean_object*);
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
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__18;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__19 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__19_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__20;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__21 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__21_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__22;
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
lean_dec(v_n_66_);
lean_dec_ref(v_a_55_);
return v___x_71_;
}
}
else
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
lean_dec(v___x_68_);
lean_dec(v_n_66_);
lean_dec_ref(v_a_55_);
v_a_77_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v___x_69_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_69_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg___boxed(lean_object* v_xs_85_, lean_object* v_i_86_, lean_object* v_a_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(v_xs_85_, v_i_86_, v_a_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec_ref(v___y_88_);
lean_dec_ref(v_xs_85_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(lean_object* v_xs_95_, lean_object* v_type_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_b_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v_b_103_ = lean_expr_abstract(v_type_96_, v_xs_95_);
v___x_104_ = lean_array_get_size(v_xs_95_);
v___x_105_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(v_xs_95_, v___x_104_, v_b_103_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars___boxed(lean_object* v_xs_106_, lean_object* v_type_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v_xs_106_, v_type_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec_ref(v_type_107_);
lean_dec_ref(v_xs_106_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0(lean_object* v_xs_115_, lean_object* v_n_116_, lean_object* v_i_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(v_xs_115_, v_i_117_, v_a_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___boxed(lean_object* v_xs_127_, lean_object* v_n_128_, lean_object* v_i_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0(v_xs_127_, v_n_128_, v_i_129_, v_a_130_, v_a_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v_n_128_);
lean_dec_ref(v_xs_127_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(size_t v_sz_139_, size_t v_i_140_, lean_object* v_bs_141_){
_start:
{
uint8_t v___x_142_; 
v___x_142_ = lean_usize_dec_lt(v_i_140_, v_sz_139_);
if (v___x_142_ == 0)
{
return v_bs_141_;
}
else
{
lean_object* v_v_143_; lean_object* v_fvarId_144_; lean_object* v___x_145_; lean_object* v_bs_x27_146_; lean_object* v___x_147_; size_t v___x_148_; size_t v___x_149_; lean_object* v___x_150_; 
v_v_143_ = lean_array_uget_borrowed(v_bs_141_, v_i_140_);
v_fvarId_144_ = lean_ctor_get(v_v_143_, 0);
lean_inc(v_fvarId_144_);
v___x_145_ = lean_unsigned_to_nat(0u);
v_bs_x27_146_ = lean_array_uset(v_bs_141_, v_i_140_, v___x_145_);
v___x_147_ = l_Lean_Expr_fvar___override(v_fvarId_144_);
v___x_148_ = ((size_t)1ULL);
v___x_149_ = lean_usize_add(v_i_140_, v___x_148_);
v___x_150_ = lean_array_uset(v_bs_x27_146_, v_i_140_, v___x_147_);
v_i_140_ = v___x_149_;
v_bs_141_ = v___x_150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0___boxed(lean_object* v_sz_152_, lean_object* v_i_153_, lean_object* v_bs_154_){
_start:
{
size_t v_sz_boxed_155_; size_t v_i_boxed_156_; lean_object* v_res_157_; 
v_sz_boxed_155_ = lean_unbox_usize(v_sz_152_);
lean_dec(v_sz_152_);
v_i_boxed_156_ = lean_unbox_usize(v_i_153_);
lean_dec(v_i_153_);
v_res_157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(v_sz_boxed_155_, v_i_boxed_156_, v_bs_154_);
return v_res_157_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0(void){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_unsigned_to_nat(32u);
v___x_162_ = lean_mk_empty_array_with_capacity(v___x_161_);
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3(void){
_start:
{
size_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_164_ = ((size_t)5ULL);
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = lean_unsigned_to_nat(32u);
v___x_167_ = lean_mk_empty_array_with_capacity(v___x_166_);
v___x_168_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2);
v___x_169_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v___x_167_);
lean_ctor_set(v___x_169_, 2, v___x_165_);
lean_ctor_set(v___x_169_, 3, v___x_165_);
lean_ctor_set_usize(v___x_169_, 4, v___x_164_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_170_ = lean_box(1);
v___x_171_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3);
v___x_172_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1);
v___x_173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v___x_171_);
lean_ctor_set(v___x_173_, 2, v___x_170_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(lean_object* v_params_174_, lean_object* v_type_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
size_t v_sz_181_; size_t v___x_182_; lean_object* v_xs_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_sz_181_ = lean_array_size(v_params_174_);
v___x_182_ = ((size_t)0ULL);
v_xs_183_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(v_sz_181_, v___x_182_, v_params_174_);
v___x_184_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_185_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v_xs_183_, v_type_175_, v___x_184_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
lean_dec_ref(v_xs_183_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___boxed(lean_object* v_params_186_, lean_object* v_type_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(v_params_186_, v_type_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec_ref(v_type_187_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams(lean_object* v_params_194_, lean_object* v_type_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(v_params_194_, v_type_195_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___boxed(lean_object* v_params_203_, lean_object* v_type_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams(v_params_203_, v_type_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec_ref(v_type_204_);
return v_res_211_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_instMonadEIO___redArg();
return v___x_212_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0);
v___x_214_ = l_StateRefT_x27_instMonad___redArg(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = l_Lean_Core_instMonadNameGeneratorCoreM;
v___x_222_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__7));
v___x_223_ = l_Lean_monadNameGeneratorLift___redArg(v___x_222_, v___x_221_);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9(void){
_start:
{
lean_object* v___x_224_; lean_object* v___f_225_; lean_object* v___x_226_; 
v___x_224_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8);
v___f_225_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__6));
v___x_226_ = l_Lean_monadNameGeneratorLift___redArg(v___f_225_, v___x_224_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10(void){
_start:
{
lean_object* v___x_227_; lean_object* v___f_228_; lean_object* v___x_229_; 
v___x_227_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9);
v___f_228_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__6));
v___x_229_ = l_Lean_monadNameGeneratorLift___redArg(v___f_228_, v___x_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg(lean_object* v_binderName_230_, lean_object* v_type_231_, uint8_t v_binderInfo_232_, lean_object* v_k_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v___x_240_; lean_object* v_toApplicative_241_; lean_object* v_toFunctor_242_; lean_object* v_toSeq_243_; lean_object* v_toSeqLeft_244_; lean_object* v_toSeqRight_245_; lean_object* v___f_246_; lean_object* v___f_247_; lean_object* v___f_248_; lean_object* v___f_249_; lean_object* v___x_250_; lean_object* v___f_251_; lean_object* v___f_252_; lean_object* v___f_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v_toApplicative_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_301_; 
v___x_240_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_241_ = lean_ctor_get(v___x_240_, 0);
v_toFunctor_242_ = lean_ctor_get(v_toApplicative_241_, 0);
v_toSeq_243_ = lean_ctor_get(v_toApplicative_241_, 2);
v_toSeqLeft_244_ = lean_ctor_get(v_toApplicative_241_, 3);
v_toSeqRight_245_ = lean_ctor_get(v_toApplicative_241_, 4);
v___f_246_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_247_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_242_, 2);
v___f_248_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_248_, 0, v_toFunctor_242_);
v___f_249_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_249_, 0, v_toFunctor_242_);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v___f_248_);
lean_ctor_set(v___x_250_, 1, v___f_249_);
lean_inc(v_toSeqRight_245_);
v___f_251_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_251_, 0, v_toSeqRight_245_);
lean_inc(v_toSeqLeft_244_);
v___f_252_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_252_, 0, v_toSeqLeft_244_);
lean_inc(v_toSeq_243_);
v___f_253_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_253_, 0, v_toSeq_243_);
v___x_254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_254_, 0, v___x_250_);
lean_ctor_set(v___x_254_, 1, v___f_246_);
lean_ctor_set(v___x_254_, 2, v___f_253_);
lean_ctor_set(v___x_254_, 3, v___f_252_);
lean_ctor_set(v___x_254_, 4, v___f_251_);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___f_247_);
v___x_256_ = l_StateRefT_x27_instMonad___redArg(v___x_255_);
v_toApplicative_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; 
v_unused_302_ = lean_ctor_get(v___x_256_, 1);
lean_dec(v_unused_302_);
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_301_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_toApplicative_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_301_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v_toFunctor_261_; lean_object* v_toSeq_262_; lean_object* v_toSeqLeft_263_; lean_object* v_toSeqRight_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_299_; 
v_toFunctor_261_ = lean_ctor_get(v_toApplicative_257_, 0);
v_toSeq_262_ = lean_ctor_get(v_toApplicative_257_, 2);
v_toSeqLeft_263_ = lean_ctor_get(v_toApplicative_257_, 3);
v_toSeqRight_264_ = lean_ctor_get(v_toApplicative_257_, 4);
v_isSharedCheck_299_ = !lean_is_exclusive(v_toApplicative_257_);
if (v_isSharedCheck_299_ == 0)
{
lean_object* v_unused_300_; 
v_unused_300_ = lean_ctor_get(v_toApplicative_257_, 1);
lean_dec(v_unused_300_);
v___x_266_ = v_toApplicative_257_;
v_isShared_267_ = v_isSharedCheck_299_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_toSeqRight_264_);
lean_inc(v_toSeqLeft_263_);
lean_inc(v_toSeq_262_);
lean_inc(v_toFunctor_261_);
lean_dec(v_toApplicative_257_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_299_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___f_268_; lean_object* v___f_269_; lean_object* v___f_270_; lean_object* v___f_271_; lean_object* v___x_272_; lean_object* v___f_273_; lean_object* v___f_274_; lean_object* v___f_275_; lean_object* v___x_277_; 
v___f_268_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__4));
v___f_269_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__5));
lean_inc_ref(v_toFunctor_261_);
v___f_270_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_270_, 0, v_toFunctor_261_);
v___f_271_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_271_, 0, v_toFunctor_261_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___f_270_);
lean_ctor_set(v___x_272_, 1, v___f_271_);
v___f_273_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_273_, 0, v_toSeqRight_264_);
v___f_274_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_274_, 0, v_toSeqLeft_263_);
v___f_275_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_275_, 0, v_toSeq_262_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 4, v___f_273_);
lean_ctor_set(v___x_266_, 3, v___f_274_);
lean_ctor_set(v___x_266_, 2, v___f_275_);
lean_ctor_set(v___x_266_, 1, v___f_268_);
lean_ctor_set(v___x_266_, 0, v___x_272_);
v___x_277_ = v___x_266_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v___f_268_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v___f_275_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v___f_274_);
lean_ctor_set(v_reuseFailAlloc_298_, 4, v___f_273_);
v___x_277_ = v_reuseFailAlloc_298_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
lean_object* v___x_279_; 
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 1, v___f_269_);
lean_ctor_set(v___x_259_, 0, v___x_277_);
v___x_279_ = v___x_259_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___f_269_);
v___x_279_ = v_reuseFailAlloc_297_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_198__overap_282_; lean_object* v___x_283_; 
v___x_280_ = l_ReaderT_instMonad___redArg(v___x_279_);
v___x_281_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10);
v___x_198__overap_282_ = l_Lean_mkFreshFVarId___redArg(v___x_280_, v___x_281_);
lean_inc(v_a_238_);
lean_inc_ref(v_a_237_);
lean_inc(v_a_236_);
lean_inc_ref(v_a_235_);
lean_inc_ref(v_a_234_);
v___x_283_ = lean_apply_6(v___x_198__overap_282_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, lean_box(0));
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_285_; uint8_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc_n(v_a_284_, 2);
lean_dec_ref_known(v___x_283_, 1);
v___x_285_ = l_Lean_Expr_fvar___override(v_a_284_);
v___x_286_ = 0;
lean_inc_ref(v_a_234_);
v___x_287_ = l_Lean_LocalContext_mkLocalDecl(v_a_234_, v_a_284_, v_binderName_230_, v_type_231_, v_binderInfo_232_, v___x_286_);
lean_inc(v_a_238_);
lean_inc_ref(v_a_237_);
lean_inc(v_a_236_);
lean_inc_ref(v_a_235_);
v___x_288_ = lean_apply_7(v_k_233_, v___x_285_, v___x_287_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, lean_box(0));
return v___x_288_;
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec_ref(v_k_233_);
lean_dec_ref(v_type_231_);
lean_dec(v_binderName_230_);
v_a_289_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_283_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_283_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___boxed(lean_object* v_binderName_303_, lean_object* v_type_304_, lean_object* v_binderInfo_305_, lean_object* v_k_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
uint8_t v_binderInfo_boxed_313_; lean_object* v_res_314_; 
v_binderInfo_boxed_313_ = lean_unbox(v_binderInfo_305_);
v_res_314_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg(v_binderName_303_, v_type_304_, v_binderInfo_boxed_313_, v_k_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec_ref(v_a_307_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl(lean_object* v_00_u03b1_315_, lean_object* v_binderName_316_, lean_object* v_type_317_, uint8_t v_binderInfo_318_, lean_object* v_k_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_326_; lean_object* v_toApplicative_327_; lean_object* v_toFunctor_328_; lean_object* v_toSeq_329_; lean_object* v_toSeqLeft_330_; lean_object* v_toSeqRight_331_; lean_object* v___f_332_; lean_object* v___f_333_; lean_object* v___f_334_; lean_object* v___f_335_; lean_object* v___x_336_; lean_object* v___f_337_; lean_object* v___f_338_; lean_object* v___f_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v_toApplicative_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_387_; 
v___x_326_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_327_ = lean_ctor_get(v___x_326_, 0);
v_toFunctor_328_ = lean_ctor_get(v_toApplicative_327_, 0);
v_toSeq_329_ = lean_ctor_get(v_toApplicative_327_, 2);
v_toSeqLeft_330_ = lean_ctor_get(v_toApplicative_327_, 3);
v_toSeqRight_331_ = lean_ctor_get(v_toApplicative_327_, 4);
v___f_332_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_333_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_328_, 2);
v___f_334_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_334_, 0, v_toFunctor_328_);
v___f_335_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_335_, 0, v_toFunctor_328_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___f_334_);
lean_ctor_set(v___x_336_, 1, v___f_335_);
lean_inc(v_toSeqRight_331_);
v___f_337_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_337_, 0, v_toSeqRight_331_);
lean_inc(v_toSeqLeft_330_);
v___f_338_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_338_, 0, v_toSeqLeft_330_);
lean_inc(v_toSeq_329_);
v___f_339_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_339_, 0, v_toSeq_329_);
v___x_340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_340_, 0, v___x_336_);
lean_ctor_set(v___x_340_, 1, v___f_332_);
lean_ctor_set(v___x_340_, 2, v___f_339_);
lean_ctor_set(v___x_340_, 3, v___f_338_);
lean_ctor_set(v___x_340_, 4, v___f_337_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___f_333_);
v___x_342_ = l_StateRefT_x27_instMonad___redArg(v___x_341_);
v_toApplicative_343_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_387_ == 0)
{
lean_object* v_unused_388_; 
v_unused_388_ = lean_ctor_get(v___x_342_, 1);
lean_dec(v_unused_388_);
v___x_345_ = v___x_342_;
v_isShared_346_ = v_isSharedCheck_387_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_toApplicative_343_);
lean_dec(v___x_342_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_387_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v_toFunctor_347_; lean_object* v_toSeq_348_; lean_object* v_toSeqLeft_349_; lean_object* v_toSeqRight_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_385_; 
v_toFunctor_347_ = lean_ctor_get(v_toApplicative_343_, 0);
v_toSeq_348_ = lean_ctor_get(v_toApplicative_343_, 2);
v_toSeqLeft_349_ = lean_ctor_get(v_toApplicative_343_, 3);
v_toSeqRight_350_ = lean_ctor_get(v_toApplicative_343_, 4);
v_isSharedCheck_385_ = !lean_is_exclusive(v_toApplicative_343_);
if (v_isSharedCheck_385_ == 0)
{
lean_object* v_unused_386_; 
v_unused_386_ = lean_ctor_get(v_toApplicative_343_, 1);
lean_dec(v_unused_386_);
v___x_352_ = v_toApplicative_343_;
v_isShared_353_ = v_isSharedCheck_385_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_toSeqRight_350_);
lean_inc(v_toSeqLeft_349_);
lean_inc(v_toSeq_348_);
lean_inc(v_toFunctor_347_);
lean_dec(v_toApplicative_343_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_385_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___f_354_; lean_object* v___f_355_; lean_object* v___f_356_; lean_object* v___f_357_; lean_object* v___x_358_; lean_object* v___f_359_; lean_object* v___f_360_; lean_object* v___f_361_; lean_object* v___x_363_; 
v___f_354_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__4));
v___f_355_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__5));
lean_inc_ref(v_toFunctor_347_);
v___f_356_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_356_, 0, v_toFunctor_347_);
v___f_357_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_357_, 0, v_toFunctor_347_);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___f_356_);
lean_ctor_set(v___x_358_, 1, v___f_357_);
v___f_359_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_359_, 0, v_toSeqRight_350_);
v___f_360_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_360_, 0, v_toSeqLeft_349_);
v___f_361_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_361_, 0, v_toSeq_348_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 4, v___f_359_);
lean_ctor_set(v___x_352_, 3, v___f_360_);
lean_ctor_set(v___x_352_, 2, v___f_361_);
lean_ctor_set(v___x_352_, 1, v___f_354_);
lean_ctor_set(v___x_352_, 0, v___x_358_);
v___x_363_ = v___x_352_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_358_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v___f_354_);
lean_ctor_set(v_reuseFailAlloc_384_, 2, v___f_361_);
lean_ctor_set(v_reuseFailAlloc_384_, 3, v___f_360_);
lean_ctor_set(v_reuseFailAlloc_384_, 4, v___f_359_);
v___x_363_ = v_reuseFailAlloc_384_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_365_; 
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 1, v___f_355_);
lean_ctor_set(v___x_345_, 0, v___x_363_);
v___x_365_ = v___x_345_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___f_355_);
v___x_365_ = v_reuseFailAlloc_383_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_232__overap_368_; lean_object* v___x_369_; 
v___x_366_ = l_ReaderT_instMonad___redArg(v___x_365_);
v___x_367_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10);
v___x_232__overap_368_ = l_Lean_mkFreshFVarId___redArg(v___x_366_, v___x_367_);
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
lean_inc_ref(v_a_320_);
v___x_369_ = lean_apply_6(v___x_232__overap_368_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, lean_box(0));
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_371_; uint8_t v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc_n(v_a_370_, 2);
lean_dec_ref_known(v___x_369_, 1);
v___x_371_ = l_Lean_Expr_fvar___override(v_a_370_);
v___x_372_ = 0;
lean_inc_ref(v_a_320_);
v___x_373_ = l_Lean_LocalContext_mkLocalDecl(v_a_320_, v_a_370_, v_binderName_316_, v_type_317_, v_binderInfo_318_, v___x_372_);
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
v___x_374_ = lean_apply_7(v_k_319_, v___x_371_, v___x_373_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, lean_box(0));
return v___x_374_;
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec_ref(v_k_319_);
lean_dec_ref(v_type_317_);
lean_dec(v_binderName_316_);
v_a_375_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_369_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_369_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___boxed(lean_object* v_00_u03b1_389_, lean_object* v_binderName_390_, lean_object* v_type_391_, lean_object* v_binderInfo_392_, lean_object* v_k_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
uint8_t v_binderInfo_boxed_400_; lean_object* v_res_401_; 
v_binderInfo_boxed_400_ = lean_unbox(v_binderInfo_392_);
v_res_401_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl(v_00_u03b1_389_, v_binderName_390_, v_type_391_, v_binderInfo_boxed_400_, v_k_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec_ref(v_a_394_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(lean_object* v_declName_405_, lean_object* v_us_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_412_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__1));
v___x_413_ = lean_name_eq(v_declName_405_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_407_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; uint8_t v___x_416_; lean_object* v___x_417_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref_known(v___x_414_, 1);
v___x_416_ = lean_unbox(v_a_415_);
lean_dec(v_a_415_);
lean_inc(v_declName_405_);
v___x_417_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_405_, v___x_416_, v_a_409_, v_a_410_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_428_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_428_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_428_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_428_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
if (lean_obj_tag(v_a_418_) == 1)
{
lean_object* v_val_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
lean_dec(v_declName_405_);
v_val_422_ = lean_ctor_get(v_a_418_, 0);
lean_inc(v_val_422_);
lean_dec_ref_known(v_a_418_, 1);
v___x_423_ = l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg(v_val_422_, v_us_406_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_423_);
v___x_425_ = v___x_420_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
else
{
lean_object* v___x_427_; 
lean_del_object(v___x_420_);
lean_dec(v_a_418_);
v___x_427_ = l_Lean_Compiler_LCNF_getOtherDeclType(v_declName_405_, v_us_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
return v___x_427_;
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec(v_us_406_);
lean_dec(v_declName_405_);
v_a_429_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_417_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_417_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
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
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_dec(v_us_406_);
lean_dec(v_declName_405_);
v_a_437_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_414_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_414_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec(v_us_406_);
lean_dec(v_declName_405_);
v___x_445_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___boxed(lean_object* v_declName_447_, lean_object* v_us_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(v_declName_447_, v_us_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
return v_res_454_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_box(0);
v___x_459_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__1));
v___x_460_ = l_Lean_mkConst(v___x_459_, v___x_458_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_464_ = lean_box(0);
v___x_465_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__4));
v___x_466_ = l_Lean_mkConst(v___x_465_, v___x_464_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_box(0);
v___x_471_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__7));
v___x_472_ = l_Lean_mkConst(v___x_471_, v___x_470_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = lean_box(0);
v___x_477_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__10));
v___x_478_ = l_Lean_mkConst(v___x_477_, v___x_476_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = lean_box(0);
v___x_483_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__13));
v___x_484_ = l_Lean_mkConst(v___x_483_, v___x_482_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_box(0);
v___x_489_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__16));
v___x_490_ = l_Lean_mkConst(v___x_489_, v___x_488_);
return v___x_490_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_494_ = lean_box(0);
v___x_495_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__19));
v___x_496_ = l_Lean_mkConst(v___x_495_, v___x_494_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType(lean_object* v_value_497_){
_start:
{
switch(lean_obj_tag(v_value_497_))
{
case 0:
{
lean_object* v___x_498_; 
v___x_498_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2);
return v___x_498_;
}
case 1:
{
lean_object* v___x_499_; 
v___x_499_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5);
return v___x_499_;
}
case 2:
{
lean_object* v___x_500_; 
v___x_500_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8);
return v___x_500_;
}
case 3:
{
lean_object* v___x_501_; 
v___x_501_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11);
return v___x_501_;
}
case 4:
{
lean_object* v___x_502_; 
v___x_502_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14);
return v___x_502_;
}
case 5:
{
lean_object* v___x_503_; 
v___x_503_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17);
return v___x_503_;
}
default: 
{
lean_object* v___x_504_; 
v___x_504_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20);
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___boxed(lean_object* v_value_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType(v_value_505_);
lean_dec_ref(v_value_505_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(lean_object* v___y_507_){
_start:
{
lean_object* v___x_509_; lean_object* v_ngen_510_; lean_object* v_namePrefix_511_; lean_object* v_idx_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_542_; 
v___x_509_ = lean_st_ref_get(v___y_507_);
v_ngen_510_ = lean_ctor_get(v___x_509_, 2);
lean_inc_ref(v_ngen_510_);
lean_dec(v___x_509_);
v_namePrefix_511_ = lean_ctor_get(v_ngen_510_, 0);
v_idx_512_ = lean_ctor_get(v_ngen_510_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v_ngen_510_);
if (v_isSharedCheck_542_ == 0)
{
v___x_514_ = v_ngen_510_;
v_isShared_515_ = v_isSharedCheck_542_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_idx_512_);
lean_inc(v_namePrefix_511_);
lean_dec(v_ngen_510_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_542_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v_r_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_520_; 
lean_inc(v_idx_512_);
lean_inc(v_namePrefix_511_);
v_r_516_ = l_Lean_Name_num___override(v_namePrefix_511_, v_idx_512_);
v___x_517_ = lean_unsigned_to_nat(1u);
v___x_518_ = lean_nat_add(v_idx_512_, v___x_517_);
lean_dec(v_idx_512_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v___x_518_);
v___x_520_ = v___x_514_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_namePrefix_511_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v___x_518_);
v___x_520_ = v_reuseFailAlloc_541_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_521_; lean_object* v_env_522_; lean_object* v_nextMacroScope_523_; lean_object* v_auxDeclNGen_524_; lean_object* v_traceState_525_; lean_object* v_cache_526_; lean_object* v_recordedDeps_527_; lean_object* v_messages_528_; lean_object* v_infoState_529_; lean_object* v_snapshotTasks_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_539_; 
v___x_521_ = lean_st_ref_take(v___y_507_);
v_env_522_ = lean_ctor_get(v___x_521_, 0);
v_nextMacroScope_523_ = lean_ctor_get(v___x_521_, 1);
v_auxDeclNGen_524_ = lean_ctor_get(v___x_521_, 3);
v_traceState_525_ = lean_ctor_get(v___x_521_, 4);
v_cache_526_ = lean_ctor_get(v___x_521_, 5);
v_recordedDeps_527_ = lean_ctor_get(v___x_521_, 6);
v_messages_528_ = lean_ctor_get(v___x_521_, 7);
v_infoState_529_ = lean_ctor_get(v___x_521_, 8);
v_snapshotTasks_530_ = lean_ctor_get(v___x_521_, 9);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; 
v_unused_540_ = lean_ctor_get(v___x_521_, 2);
lean_dec(v_unused_540_);
v___x_532_ = v___x_521_;
v_isShared_533_ = v_isSharedCheck_539_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_snapshotTasks_530_);
lean_inc(v_infoState_529_);
lean_inc(v_messages_528_);
lean_inc(v_recordedDeps_527_);
lean_inc(v_cache_526_);
lean_inc(v_traceState_525_);
lean_inc(v_auxDeclNGen_524_);
lean_inc(v_nextMacroScope_523_);
lean_inc(v_env_522_);
lean_dec(v___x_521_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_539_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 2, v___x_520_);
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_env_522_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_nextMacroScope_523_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_538_, 3, v_auxDeclNGen_524_);
lean_ctor_set(v_reuseFailAlloc_538_, 4, v_traceState_525_);
lean_ctor_set(v_reuseFailAlloc_538_, 5, v_cache_526_);
lean_ctor_set(v_reuseFailAlloc_538_, 6, v_recordedDeps_527_);
lean_ctor_set(v_reuseFailAlloc_538_, 7, v_messages_528_);
lean_ctor_set(v_reuseFailAlloc_538_, 8, v_infoState_529_);
lean_ctor_set(v_reuseFailAlloc_538_, 9, v_snapshotTasks_530_);
v___x_535_ = v_reuseFailAlloc_538_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_st_ref_put(v___y_507_, v___x_535_);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v_r_516_);
return v___x_537_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg___boxed(lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(v___y_543_);
lean_dec(v___y_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___x_552_; lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
v___x_552_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(v___y_550_);
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0___boxed(lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec_ref(v___y_561_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(lean_object* v_msg_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v___x_575_; lean_object* v_toApplicative_576_; lean_object* v_toFunctor_577_; lean_object* v_toSeq_578_; lean_object* v_toSeqLeft_579_; lean_object* v_toSeqRight_580_; lean_object* v___f_581_; lean_object* v___f_582_; lean_object* v___f_583_; lean_object* v___f_584_; lean_object* v___x_585_; lean_object* v___f_586_; lean_object* v___f_587_; lean_object* v___f_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___f_594_; lean_object* v___f_595_; lean_object* v___x_6180__overap_596_; lean_object* v___x_597_; 
v___x_575_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_576_ = lean_ctor_get(v___x_575_, 0);
v_toFunctor_577_ = lean_ctor_get(v_toApplicative_576_, 0);
v_toSeq_578_ = lean_ctor_get(v_toApplicative_576_, 2);
v_toSeqLeft_579_ = lean_ctor_get(v_toApplicative_576_, 3);
v_toSeqRight_580_ = lean_ctor_get(v_toApplicative_576_, 4);
v___f_581_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_582_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_577_, 2);
v___f_583_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_583_, 0, v_toFunctor_577_);
v___f_584_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_584_, 0, v_toFunctor_577_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v___f_583_);
lean_ctor_set(v___x_585_, 1, v___f_584_);
lean_inc(v_toSeqRight_580_);
v___f_586_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_586_, 0, v_toSeqRight_580_);
lean_inc(v_toSeqLeft_579_);
v___f_587_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_587_, 0, v_toSeqLeft_579_);
lean_inc(v_toSeq_578_);
v___f_588_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_588_, 0, v_toSeq_578_);
v___x_589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_589_, 0, v___x_585_);
lean_ctor_set(v___x_589_, 1, v___f_581_);
lean_ctor_set(v___x_589_, 2, v___f_588_);
lean_ctor_set(v___x_589_, 3, v___f_587_);
lean_ctor_set(v___x_589_, 4, v___f_586_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v___f_582_);
v___x_591_ = l_StateRefT_x27_instMonad___redArg(v___x_590_);
v___x_592_ = l_Lean_instInhabitedExpr;
v___x_593_ = l_instInhabitedOfMonad___redArg(v___x_591_, v___x_592_);
v___f_594_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_594_, 0, v___x_593_);
v___f_595_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_595_, 0, v___f_594_);
v___x_6180__overap_596_ = lean_panic_fn_borrowed(v___f_595_, v_msg_568_);
lean_dec_ref(v___f_595_);
lean_inc(v___y_573_);
lean_inc_ref(v___y_572_);
lean_inc(v___y_571_);
lean_inc_ref(v___y_570_);
lean_inc_ref(v___y_569_);
v___x_597_ = lean_apply_6(v___x_6180__overap_596_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, lean_box(0));
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2___boxed(lean_object* v_msg_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(v_msg_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec_ref(v___y_599_);
return v_res_605_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(lean_object* v_upperBound_608_, lean_object* v___x_609_, lean_object* v_a_610_, lean_object* v_b_611_){
_start:
{
lean_object* v_a_614_; uint8_t v___x_618_; 
v___x_618_ = lean_nat_dec_lt(v_a_610_, v_upperBound_608_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; 
lean_dec(v_a_610_);
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v_b_611_);
return v___x_619_;
}
else
{
lean_object* v_snd_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_656_; 
v_snd_620_ = lean_ctor_get(v_b_611_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_b_611_);
if (v_isSharedCheck_656_ == 0)
{
lean_object* v_unused_657_; 
v_unused_657_ = lean_ctor_get(v_b_611_, 0);
lean_dec(v_unused_657_);
v___x_622_ = v_b_611_;
v_isShared_623_ = v_isSharedCheck_656_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_snd_620_);
lean_dec(v_b_611_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_656_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_fst_624_; lean_object* v_snd_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_655_; 
v_fst_624_ = lean_ctor_get(v_snd_620_, 0);
v_snd_625_ = lean_ctor_get(v_snd_620_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_snd_620_);
if (v_isSharedCheck_655_ == 0)
{
v___x_627_ = v_snd_620_;
v_isShared_628_ = v_isSharedCheck_655_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_snd_625_);
lean_inc(v_fst_624_);
lean_dec(v_snd_620_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_655_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_box(0);
v___x_630_ = l_Lean_Expr_headBeta(v_snd_625_);
if (lean_obj_tag(v___x_630_) == 7)
{
lean_object* v_body_631_; lean_object* v___x_633_; 
v_body_631_ = lean_ctor_get(v___x_630_, 2);
lean_inc_ref(v_body_631_);
lean_dec_ref_known(v___x_630_, 3);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v_body_631_);
v___x_633_ = v___x_627_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_fst_624_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_body_631_);
v___x_633_ = v_reuseFailAlloc_637_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_635_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v___x_633_);
lean_ctor_set(v___x_622_, 0, v___x_629_);
v___x_635_ = v___x_622_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
v_a_614_ = v___x_635_;
goto v___jp_613_;
}
}
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_expr_instantiate_rev_range(v___x_630_, v_fst_624_, v_a_610_, v___x_609_);
lean_dec_ref(v___x_630_);
v___x_639_ = l_Lean_Expr_headBeta(v___x_638_);
if (lean_obj_tag(v___x_639_) == 7)
{
lean_object* v_body_640_; lean_object* v___x_642_; 
lean_dec(v_fst_624_);
v_body_640_ = lean_ctor_get(v___x_639_, 2);
lean_inc_ref(v_body_640_);
lean_dec_ref_known(v___x_639_, 3);
lean_inc(v_a_610_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v_body_640_);
lean_ctor_set(v___x_627_, 0, v_a_610_);
v___x_642_ = v___x_627_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_610_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_body_640_);
v___x_642_ = v_reuseFailAlloc_646_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_644_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v___x_642_);
lean_ctor_set(v___x_622_, 0, v___x_629_);
v___x_644_ = v___x_622_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
v_a_614_ = v___x_644_;
goto v___jp_613_;
}
}
}
else
{
lean_object* v___x_647_; lean_object* v___x_649_; 
lean_dec(v_a_610_);
v___x_647_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v___x_639_);
v___x_649_ = v___x_627_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_fst_624_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v___x_639_);
v___x_649_ = v_reuseFailAlloc_654_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_651_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v___x_649_);
lean_ctor_set(v___x_622_, 0, v___x_647_);
v___x_651_ = v___x_622_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_649_);
v___x_651_ = v_reuseFailAlloc_653_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_652_; 
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
}
}
}
}
}
v___jp_613_:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_nat_add(v_a_610_, v___x_615_);
lean_dec(v_a_610_);
v_a_610_ = v___x_616_;
v_b_611_ = v_a_614_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___boxed(lean_object* v_upperBound_658_, lean_object* v___x_659_, lean_object* v_a_660_, lean_object* v_b_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v_upperBound_658_, v___x_659_, v_a_660_, v_b_661_);
lean_dec_ref(v___x_659_);
lean_dec(v_upperBound_658_);
return v_res_663_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0(void){
_start:
{
lean_object* v___x_666_; lean_object* v_dummy_667_; 
v___x_666_ = lean_box(0);
v_dummy_667_ = l_Lean_Expr_sort___override(v___x_666_);
return v_dummy_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(lean_object* v_e_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v_j_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_j_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = l_Lean_Expr_getAppFn(v_e_668_);
v___x_677_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v___x_676_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v_dummy_679_; lean_object* v_nargs_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v___x_677_, 1);
v_dummy_679_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0);
v_nargs_680_ = l_Lean_Expr_getAppNumArgs(v_e_668_);
lean_inc(v_nargs_680_);
v___x_681_ = lean_mk_array(v_nargs_680_, v_dummy_679_);
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = lean_nat_sub(v_nargs_680_, v___x_682_);
lean_dec(v_nargs_680_);
v___x_684_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_668_, v___x_681_, v___x_683_);
v___x_685_ = lean_array_get_size(v___x_684_);
v___x_686_ = lean_box(0);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v_j_675_);
lean_ctor_set(v___x_687_, 1, v_a_678_);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v___x_685_, v___x_684_, v_j_675_, v___x_688_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_707_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_707_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_707_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_707_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_fst_694_; 
v_fst_694_ = lean_ctor_get(v_a_690_, 0);
if (lean_obj_tag(v_fst_694_) == 0)
{
lean_object* v_snd_695_; lean_object* v_fst_696_; lean_object* v_snd_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_701_; 
v_snd_695_ = lean_ctor_get(v_a_690_, 1);
lean_inc(v_snd_695_);
lean_dec(v_a_690_);
v_fst_696_ = lean_ctor_get(v_snd_695_, 0);
lean_inc(v_fst_696_);
v_snd_697_ = lean_ctor_get(v_snd_695_, 1);
lean_inc(v_snd_697_);
lean_dec(v_snd_695_);
v___x_698_ = lean_expr_instantiate_rev_range(v_snd_697_, v_fst_696_, v___x_685_, v___x_684_);
lean_dec_ref(v___x_684_);
lean_dec(v_fst_696_);
lean_dec(v_snd_697_);
v___x_699_ = l_Lean_Expr_headBeta(v___x_698_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_699_);
v___x_701_ = v___x_692_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
else
{
lean_object* v_val_703_; lean_object* v___x_705_; 
lean_inc_ref(v_fst_694_);
lean_dec(v_a_690_);
lean_dec_ref(v___x_684_);
v_val_703_ = lean_ctor_get(v_fst_694_, 0);
lean_inc(v_val_703_);
lean_dec_ref_known(v_fst_694_, 1);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v_val_703_);
v___x_705_ = v___x_692_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_val_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec_ref(v___x_684_);
v_a_708_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_689_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_689_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_dec_ref(v_e_668_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(lean_object* v_e_716_, lean_object* v_fvars_717_, lean_object* v_all_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
switch(lean_obj_tag(v_e_716_))
{
case 6:
{
lean_object* v_binderName_725_; lean_object* v_binderType_726_; lean_object* v_body_727_; uint8_t v_binderInfo_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_binderName_725_ = lean_ctor_get(v_e_716_, 0);
lean_inc(v_binderName_725_);
v_binderType_726_ = lean_ctor_get(v_e_716_, 1);
lean_inc_ref(v_binderType_726_);
v_body_727_ = lean_ctor_get(v_e_716_, 2);
lean_inc_ref(v_body_727_);
v_binderInfo_728_ = lean_ctor_get_uint8(v_e_716_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_716_, 3);
v___x_729_ = lean_expr_instantiate_rev(v_binderType_726_, v_all_718_);
lean_dec_ref(v_binderType_726_);
v___x_730_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_732_; uint8_t v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc_n(v_a_731_, 2);
lean_dec_ref_known(v___x_730_, 1);
v___x_732_ = l_Lean_Expr_fvar___override(v_a_731_);
v___x_733_ = 0;
v___x_734_ = l_Lean_LocalContext_mkLocalDecl(v_a_719_, v_a_731_, v_binderName_725_, v___x_729_, v_binderInfo_728_, v___x_733_);
lean_inc_ref(v___x_732_);
v___x_735_ = lean_array_push(v_fvars_717_, v___x_732_);
v___x_736_ = lean_array_push(v_all_718_, v___x_732_);
v_e_716_ = v_body_727_;
v_fvars_717_ = v___x_735_;
v_all_718_ = v___x_736_;
v_a_719_ = v___x_734_;
goto _start;
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec_ref(v___x_729_);
lean_dec_ref(v_body_727_);
lean_dec(v_binderName_725_);
lean_dec_ref(v_a_719_);
lean_dec_ref(v_all_718_);
lean_dec_ref(v_fvars_717_);
v_a_738_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_730_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_730_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
case 8:
{
lean_object* v_declName_746_; lean_object* v_type_747_; lean_object* v_body_748_; lean_object* v___x_749_; uint8_t v___x_750_; lean_object* v___x_751_; 
v_declName_746_ = lean_ctor_get(v_e_716_, 0);
lean_inc(v_declName_746_);
v_type_747_ = lean_ctor_get(v_e_716_, 1);
lean_inc_ref(v_type_747_);
v_body_748_ = lean_ctor_get(v_e_716_, 3);
lean_inc_ref(v_body_748_);
lean_dec_ref_known(v_e_716_, 4);
v___x_749_ = lean_expr_instantiate_rev(v_type_747_, v_all_718_);
lean_dec_ref(v_type_747_);
v___x_750_ = 0;
v___x_751_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_753_; uint8_t v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc_n(v_a_752_, 2);
lean_dec_ref_known(v___x_751_, 1);
v___x_753_ = l_Lean_Expr_fvar___override(v_a_752_);
v___x_754_ = 0;
v___x_755_ = l_Lean_LocalContext_mkLocalDecl(v_a_719_, v_a_752_, v_declName_746_, v___x_749_, v___x_750_, v___x_754_);
v___x_756_ = lean_array_push(v_all_718_, v___x_753_);
v_e_716_ = v_body_748_;
v_all_718_ = v___x_756_;
v_a_719_ = v___x_755_;
goto _start;
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec_ref(v___x_749_);
lean_dec_ref(v_body_748_);
lean_dec(v_declName_746_);
lean_dec_ref(v_a_719_);
lean_dec_ref(v_all_718_);
lean_dec_ref(v_fvars_717_);
v_a_758_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_751_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_751_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
default: 
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_expr_instantiate_rev(v_e_716_, v_all_718_);
lean_dec_ref(v_all_718_);
lean_dec_ref(v_e_716_);
v___x_767_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v___x_766_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_769_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v___x_767_, 1);
v___x_769_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v_fvars_717_, v_a_768_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_768_);
lean_dec_ref(v_fvars_717_);
return v___x_769_;
}
else
{
lean_dec_ref(v_a_719_);
lean_dec_ref(v_fvars_717_);
return v___x_767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(lean_object* v_e_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0));
lean_inc_ref(v_a_771_);
v___x_778_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(v_e_770_, v___x_777_, v___x_777_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_782_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2));
v___x_783_ = lean_unsigned_to_nat(73u);
v___x_784_ = lean_unsigned_to_nat(135u);
v___x_785_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__1));
v___x_786_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_787_ = l_mkPanicMessageWithDecl(v___x_786_, v___x_785_, v___x_784_, v___x_783_, v___x_782_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType(lean_object* v_e_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
switch(lean_obj_tag(v_e_788_))
{
case 1:
{
lean_object* v_fvarId_795_; lean_object* v___x_796_; 
v_fvarId_795_ = lean_ctor_get(v_e_788_, 0);
lean_inc(v_fvarId_795_);
lean_dec_ref_known(v_e_788_, 1);
v___x_796_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_fvarId_795_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
return v___x_796_;
}
case 3:
{
lean_object* v_u_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_u_797_ = lean_ctor_get(v_e_788_, 0);
lean_inc(v_u_797_);
lean_dec_ref_known(v_e_788_, 1);
v___x_798_ = l_Lean_Level_succ___override(v_u_797_);
v___x_799_ = l_Lean_Expr_sort___override(v___x_798_);
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
return v___x_800_;
}
case 4:
{
lean_object* v_declName_801_; lean_object* v_us_802_; lean_object* v___x_803_; 
v_declName_801_ = lean_ctor_get(v_e_788_, 0);
lean_inc(v_declName_801_);
v_us_802_ = lean_ctor_get(v_e_788_, 1);
lean_inc(v_us_802_);
lean_dec_ref_known(v_e_788_, 2);
v___x_803_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(v_declName_801_, v_us_802_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
return v___x_803_;
}
case 5:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(v_e_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
return v___x_804_;
}
case 6:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(v_e_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
return v___x_805_;
}
case 7:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(v_e_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
return v___x_806_;
}
default: 
{
lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec_ref(v_e_788_);
v___x_807_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3, &l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3);
v___x_808_ = l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(v___x_807_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
return v___x_808_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(lean_object* v_type_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_type_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_830_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_830_ == 0)
{
v___x_819_ = v___x_816_;
v_isShared_820_ = v_isSharedCheck_830_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_830_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
if (lean_obj_tag(v_a_817_) == 3)
{
lean_object* v_u_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
v_u_821_ = lean_ctor_get(v_a_817_, 0);
lean_inc(v_u_821_);
lean_dec_ref_known(v_a_817_, 1);
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v_u_821_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_822_);
v___x_824_ = v___x_819_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
else
{
lean_object* v___x_826_; lean_object* v___x_828_; 
lean_dec(v_a_817_);
v___x_826_ = lean_box(0);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_826_);
v___x_828_ = v___x_819_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
v_a_831_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_816_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_816_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(lean_object* v_as_841_, size_t v_sz_842_, size_t v_i_843_, lean_object* v_b_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
uint8_t v___x_851_; 
v___x_851_ = lean_usize_dec_lt(v_i_843_, v_sz_842_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; 
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v_b_844_);
return v___x_852_;
}
else
{
lean_object* v_snd_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_898_; 
v_snd_853_ = lean_ctor_get(v_b_844_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v_b_844_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v_b_844_, 0);
lean_dec(v_unused_899_);
v___x_855_ = v_b_844_;
v_isShared_856_ = v_isSharedCheck_898_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_snd_853_);
lean_dec(v_b_844_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_898_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v_a_858_; lean_object* v___x_859_; 
v___x_857_ = lean_box(0);
v_a_858_ = lean_array_uget_borrowed(v_as_841_, v_i_843_);
lean_inc(v_a_858_);
v___x_859_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_a_858_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_861_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v___x_859_, 1);
v___x_861_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(v_a_860_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_881_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_881_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_881_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_881_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
if (lean_obj_tag(v_a_862_) == 1)
{
lean_object* v_val_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
lean_del_object(v___x_864_);
v_val_866_ = lean_ctor_get(v_a_862_, 0);
lean_inc(v_val_866_);
lean_dec_ref_known(v_a_862_, 1);
v___x_867_ = l_Lean_mkLevelIMax_x27(v_val_866_, v_snd_853_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 1, v___x_867_);
lean_ctor_set(v___x_855_, 0, v___x_857_);
v___x_869_ = v___x_855_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_867_);
v___x_869_ = v_reuseFailAlloc_873_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
size_t v___x_870_; size_t v___x_871_; 
v___x_870_ = ((size_t)1ULL);
v___x_871_ = lean_usize_add(v_i_843_, v___x_870_);
v_i_843_ = v___x_871_;
v_b_844_ = v___x_869_;
goto _start;
}
}
else
{
lean_object* v___x_874_; lean_object* v___x_876_; 
lean_dec(v_a_862_);
v___x_874_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_874_);
v___x_876_ = v___x_855_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_snd_853_);
v___x_876_ = v_reuseFailAlloc_880_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_878_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_876_);
v___x_878_ = v___x_864_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_del_object(v___x_855_);
lean_dec(v_snd_853_);
v_a_882_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_861_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_861_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_del_object(v___x_855_);
lean_dec(v_snd_853_);
v_a_890_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_859_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_859_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(lean_object* v_e_900_, lean_object* v_fvars_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
if (lean_obj_tag(v_e_900_) == 7)
{
lean_object* v_binderName_908_; lean_object* v_binderType_909_; lean_object* v_body_910_; uint8_t v_binderInfo_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v_binderName_908_ = lean_ctor_get(v_e_900_, 0);
lean_inc(v_binderName_908_);
v_binderType_909_ = lean_ctor_get(v_e_900_, 1);
lean_inc_ref(v_binderType_909_);
v_body_910_ = lean_ctor_get(v_e_900_, 2);
lean_inc_ref(v_body_910_);
v_binderInfo_911_ = lean_ctor_get_uint8(v_e_900_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_900_, 3);
v___x_912_ = lean_expr_instantiate_rev(v_binderType_909_, v_fvars_901_);
lean_dec_ref(v_binderType_909_);
v___x_913_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_915_; uint8_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc_n(v_a_914_, 2);
lean_dec_ref_known(v___x_913_, 1);
v___x_915_ = l_Lean_Expr_fvar___override(v_a_914_);
v___x_916_ = 0;
v___x_917_ = l_Lean_LocalContext_mkLocalDecl(v_a_902_, v_a_914_, v_binderName_908_, v___x_912_, v_binderInfo_911_, v___x_916_);
v___x_918_ = lean_array_push(v_fvars_901_, v___x_915_);
v_e_900_ = v_body_910_;
v_fvars_901_ = v___x_918_;
v_a_902_ = v___x_917_;
goto _start;
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec_ref(v___x_912_);
lean_dec_ref(v_body_910_);
lean_dec(v_binderName_908_);
lean_dec_ref(v_a_902_);
lean_dec_ref(v_fvars_901_);
v_a_920_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_913_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_913_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
else
{
lean_object* v_e_928_; lean_object* v___x_929_; 
v_e_928_ = lean_expr_instantiate_rev(v_e_900_, v_fvars_901_);
lean_dec_ref(v_e_900_);
v___x_929_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(v_e_928_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_969_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_969_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_969_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_969_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
if (lean_obj_tag(v_a_930_) == 1)
{
lean_object* v_val_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; size_t v_sz_938_; size_t v___x_939_; lean_object* v___x_940_; 
lean_del_object(v___x_932_);
v_val_934_ = lean_ctor_get(v_a_930_, 0);
lean_inc(v_val_934_);
lean_dec_ref_known(v_a_930_, 1);
v___x_935_ = l_Array_reverse___redArg(v_fvars_901_);
v___x_936_ = lean_box(0);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v_val_934_);
v_sz_938_ = lean_array_size(v___x_935_);
v___x_939_ = ((size_t)0ULL);
v___x_940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(v___x_935_, v_sz_938_, v___x_939_, v___x_937_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
lean_dec_ref(v_a_902_);
lean_dec_ref(v___x_935_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_956_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_956_ == 0)
{
v___x_943_ = v___x_940_;
v_isShared_944_ = v_isSharedCheck_956_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_940_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_956_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_fst_945_; 
v_fst_945_ = lean_ctor_get(v_a_941_, 0);
if (lean_obj_tag(v_fst_945_) == 0)
{
lean_object* v_snd_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_950_; 
v_snd_946_ = lean_ctor_get(v_a_941_, 1);
lean_inc(v_snd_946_);
lean_dec(v_a_941_);
v___x_947_ = l_Lean_Level_normalize(v_snd_946_);
lean_dec(v_snd_946_);
v___x_948_ = l_Lean_Expr_sort___override(v___x_947_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_948_);
v___x_950_ = v___x_943_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
else
{
lean_object* v_val_952_; lean_object* v___x_954_; 
lean_inc_ref(v_fst_945_);
lean_dec(v_a_941_);
v_val_952_ = lean_ctor_get(v_fst_945_, 0);
lean_inc(v_val_952_);
lean_dec_ref_known(v_fst_945_, 1);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v_val_952_);
v___x_954_ = v___x_943_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_val_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_a_957_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_940_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_940_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
else
{
lean_object* v___x_965_; lean_object* v___x_967_; 
lean_dec(v_a_930_);
lean_dec_ref(v_a_902_);
lean_dec_ref(v_fvars_901_);
v___x_965_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_965_);
v___x_967_ = v___x_932_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_dec_ref(v_a_902_);
lean_dec_ref(v_fvars_901_);
v_a_970_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_929_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_929_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(lean_object* v_e_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0));
lean_inc_ref(v_a_979_);
v___x_986_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(v_e_978_, v___x_985_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___boxed(lean_object* v_e_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(v_e_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec_ref(v_a_988_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType___boxed(lean_object* v_e_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(v_e_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec_ref(v_a_996_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f___boxed(lean_object* v_type_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(v_type_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
lean_dec_ref(v_a_1004_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType___boxed(lean_object* v_e_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_e_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec_ref(v_a_1012_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___boxed(lean_object* v_as_1019_, lean_object* v_sz_1020_, lean_object* v_i_1021_, lean_object* v_b_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
size_t v_sz_boxed_1029_; size_t v_i_boxed_1030_; lean_object* v_res_1031_; 
v_sz_boxed_1029_ = lean_unbox_usize(v_sz_1020_);
lean_dec(v_sz_1020_);
v_i_boxed_1030_ = lean_unbox_usize(v_i_1021_);
lean_dec(v_i_1021_);
v_res_1031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(v_as_1019_, v_sz_boxed_1029_, v_i_boxed_1030_, v_b_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec_ref(v_as_1019_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___boxed(lean_object* v_e_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(v_e_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec_ref(v_a_1033_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go___boxed(lean_object* v_e_1040_, lean_object* v_fvars_1041_, lean_object* v_all_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(v_e_1040_, v_fvars_1041_, v_all_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go___boxed(lean_object* v_e_1050_, lean_object* v_fvars_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(v_e_1050_, v_fvars_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3(lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(v___y_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___boxed(lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3(v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec_ref(v___y_1066_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9(lean_object* v_upperBound_1073_, lean_object* v___x_1074_, lean_object* v_inst_1075_, lean_object* v_R_1076_, lean_object* v_a_1077_, lean_object* v_b_1078_, lean_object* v_c_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v_upperBound_1073_, v___x_1074_, v_a_1077_, v_b_1078_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___boxed(lean_object* v_upperBound_1087_, lean_object* v___x_1088_, lean_object* v_inst_1089_, lean_object* v_R_1090_, lean_object* v_a_1091_, lean_object* v_b_1092_, lean_object* v_c_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9(v_upperBound_1087_, v___x_1088_, v_inst_1089_, v_R_1090_, v_a_1091_, v_b_1092_, v_c_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec_ref(v___x_1088_);
lean_dec(v_upperBound_1087_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(lean_object* v_arg_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
switch(lean_obj_tag(v_arg_1101_))
{
case 0:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
return v___x_1109_;
}
case 1:
{
lean_object* v_fvarId_1110_; lean_object* v___x_1111_; 
v_fvarId_1110_ = lean_ctor_get(v_arg_1101_, 0);
lean_inc(v_fvarId_1110_);
lean_dec_ref_known(v_arg_1101_, 1);
v___x_1111_ = l_Lean_Compiler_LCNF_getType(v_fvarId_1110_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
return v___x_1111_;
}
default: 
{
lean_object* v_expr_1112_; lean_object* v___x_1113_; 
v_expr_1112_ = lean_ctor_get(v_arg_1101_, 0);
lean_inc_ref(v_expr_1112_);
lean_dec_ref_known(v_arg_1101_, 1);
v___x_1113_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_expr_1112_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
return v___x_1113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferArgType___boxed(lean_object* v_arg_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(v_arg_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec_ref(v_a_1115_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(lean_object* v_upperBound_1122_, lean_object* v_args_1123_, lean_object* v_a_1124_, lean_object* v_b_1125_){
_start:
{
lean_object* v_a_1128_; uint8_t v___x_1132_; 
v___x_1132_ = lean_nat_dec_lt(v_a_1124_, v_upperBound_1122_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; 
lean_dec(v_a_1124_);
lean_dec_ref(v_args_1123_);
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v_b_1125_);
return v___x_1133_;
}
else
{
lean_object* v_snd_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1170_; 
v_snd_1134_ = lean_ctor_get(v_b_1125_, 1);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_b_1125_);
if (v_isSharedCheck_1170_ == 0)
{
lean_object* v_unused_1171_; 
v_unused_1171_ = lean_ctor_get(v_b_1125_, 0);
lean_dec(v_unused_1171_);
v___x_1136_ = v_b_1125_;
v_isShared_1137_ = v_isSharedCheck_1170_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_snd_1134_);
lean_dec(v_b_1125_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1170_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v_fst_1138_; lean_object* v_snd_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1169_; 
v_fst_1138_ = lean_ctor_get(v_snd_1134_, 0);
v_snd_1139_ = lean_ctor_get(v_snd_1134_, 1);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_snd_1134_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1141_ = v_snd_1134_;
v_isShared_1142_ = v_isSharedCheck_1169_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_snd_1139_);
lean_inc(v_fst_1138_);
lean_dec(v_snd_1134_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1169_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_box(0);
v___x_1144_ = l_Lean_Expr_headBeta(v_snd_1139_);
if (lean_obj_tag(v___x_1144_) == 7)
{
lean_object* v_body_1145_; lean_object* v___x_1147_; 
v_body_1145_ = lean_ctor_get(v___x_1144_, 2);
lean_inc_ref(v_body_1145_);
lean_dec_ref_known(v___x_1144_, 3);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 1, v_body_1145_);
v___x_1147_ = v___x_1141_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_fst_1138_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_body_1145_);
v___x_1147_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1149_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v___x_1147_);
lean_ctor_set(v___x_1136_, 0, v___x_1143_);
v___x_1149_ = v___x_1136_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
v_a_1128_ = v___x_1149_;
goto v___jp_1127_;
}
}
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_inc_ref(v_args_1123_);
v___x_1152_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(v___x_1144_, v_fst_1138_, v_a_1124_, v_args_1123_);
lean_dec_ref(v___x_1144_);
v___x_1153_ = l_Lean_Expr_headBeta(v___x_1152_);
if (lean_obj_tag(v___x_1153_) == 7)
{
lean_object* v_body_1154_; lean_object* v___x_1156_; 
lean_dec(v_fst_1138_);
v_body_1154_ = lean_ctor_get(v___x_1153_, 2);
lean_inc_ref(v_body_1154_);
lean_dec_ref_known(v___x_1153_, 3);
lean_inc(v_a_1124_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 1, v_body_1154_);
lean_ctor_set(v___x_1141_, 0, v_a_1124_);
v___x_1156_ = v___x_1141_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1124_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_body_1154_);
v___x_1156_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1158_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v___x_1156_);
lean_ctor_set(v___x_1136_, 0, v___x_1143_);
v___x_1158_ = v___x_1136_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
v_a_1128_ = v___x_1158_;
goto v___jp_1127_;
}
}
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1163_; 
lean_dec(v_a_1124_);
lean_dec_ref(v_args_1123_);
v___x_1161_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 1, v___x_1153_);
v___x_1163_ = v___x_1141_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_fst_1138_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v___x_1153_);
v___x_1163_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1165_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v___x_1163_);
lean_ctor_set(v___x_1136_, 0, v___x_1161_);
v___x_1165_ = v___x_1136_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
}
}
}
}
}
}
v___jp_1127_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_unsigned_to_nat(1u);
v___x_1130_ = lean_nat_add(v_a_1124_, v___x_1129_);
lean_dec(v_a_1124_);
v_a_1124_ = v___x_1130_;
v_b_1125_ = v_a_1128_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg___boxed(lean_object* v_upperBound_1172_, lean_object* v_args_1173_, lean_object* v_a_1174_, lean_object* v_b_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v_upperBound_1172_, v_args_1173_, v_a_1174_, v_b_1175_);
lean_dec(v_upperBound_1172_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(lean_object* v_fType_1178_, lean_object* v_args_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1186_ = lean_array_get_size(v_args_1179_);
v___x_1187_ = lean_unsigned_to_nat(0u);
v___x_1188_ = lean_box(0);
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v_fType_1178_);
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1188_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
lean_inc_ref(v_args_1179_);
v___x_1191_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v___x_1186_, v_args_1179_, v___x_1187_, v___x_1190_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1209_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1209_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1209_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v_fst_1196_; 
v_fst_1196_ = lean_ctor_get(v_a_1192_, 0);
if (lean_obj_tag(v_fst_1196_) == 0)
{
lean_object* v_snd_1197_; lean_object* v_fst_1198_; lean_object* v_snd_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1203_; 
v_snd_1197_ = lean_ctor_get(v_a_1192_, 1);
lean_inc(v_snd_1197_);
lean_dec(v_a_1192_);
v_fst_1198_ = lean_ctor_get(v_snd_1197_, 0);
lean_inc(v_fst_1198_);
v_snd_1199_ = lean_ctor_get(v_snd_1197_, 1);
lean_inc(v_snd_1199_);
lean_dec(v_snd_1197_);
v___x_1200_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(v_snd_1199_, v_fst_1198_, v___x_1186_, v_args_1179_);
lean_dec(v_fst_1198_);
lean_dec(v_snd_1199_);
v___x_1201_ = l_Lean_Expr_headBeta(v___x_1200_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1201_);
v___x_1203_ = v___x_1194_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
else
{
lean_object* v_val_1205_; lean_object* v___x_1207_; 
lean_inc_ref(v_fst_1196_);
lean_dec(v_a_1192_);
lean_dec_ref(v_args_1179_);
v_val_1205_ = lean_ctor_get(v_fst_1196_, 0);
lean_inc(v_val_1205_);
lean_dec_ref_known(v_fst_1196_, 1);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v_val_1205_);
v___x_1207_ = v___x_1194_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_val_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec_ref(v_args_1179_);
v_a_1210_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1191_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1191_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore___boxed(lean_object* v_fType_1218_, lean_object* v_args_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_fType_1218_, v_args_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec_ref(v_a_1220_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0(lean_object* v_upperBound_1227_, lean_object* v_args_1228_, lean_object* v_inst_1229_, lean_object* v_R_1230_, lean_object* v_a_1231_, lean_object* v_b_1232_, lean_object* v_c_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v_upperBound_1227_, v_args_1228_, v_a_1231_, v_b_1232_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___boxed(lean_object* v_upperBound_1241_, lean_object* v_args_1242_, lean_object* v_inst_1243_, lean_object* v_R_1244_, lean_object* v_a_1245_, lean_object* v_b_1246_, lean_object* v_c_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0(v_upperBound_1241_, v_args_1242_, v_inst_1243_, v_R_1244_, v_a_1245_, v_b_1246_, v_c_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v_upperBound_1241_);
return v_res_1254_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0);
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
return v___x_1256_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0);
v___x_1258_ = lean_unsigned_to_nat(0u);
v___x_1259_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
lean_ctor_set(v___x_1259_, 2, v___x_1258_);
lean_ctor_set(v___x_1259_, 3, v___x_1258_);
lean_ctor_set(v___x_1259_, 4, v___x_1257_);
lean_ctor_set(v___x_1259_, 5, v___x_1257_);
lean_ctor_set(v___x_1259_, 6, v___x_1257_);
lean_ctor_set(v___x_1259_, 7, v___x_1257_);
lean_ctor_set(v___x_1259_, 8, v___x_1257_);
lean_ctor_set(v___x_1259_, 9, v___x_1257_);
lean_ctor_set(v___x_1259_, 10, v___x_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(lean_object* v_msg_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_ref_1266_; lean_object* v___x_1267_; lean_object* v_env_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v_ref_1266_ = lean_ctor_get(v___y_1263_, 2);
v___x_1267_ = lean_st_ref_get(v___y_1264_);
v_env_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc_ref(v_env_1268_);
lean_dec(v___x_1267_);
v___x_1269_ = lean_st_ref_get(v___y_1262_);
v___x_1270_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1261_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1293_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1293_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1293_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v_lctx_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1291_; 
v_lctx_1275_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1291_ == 0)
{
lean_object* v_unused_1292_; 
v_unused_1292_ = lean_ctor_get(v___x_1269_, 1);
lean_dec(v_unused_1292_);
v___x_1277_ = v___x_1269_;
v_isShared_1278_ = v_isSharedCheck_1291_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_lctx_1275_);
lean_dec(v___x_1269_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1291_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
uint8_t v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___x_1279_ = lean_unbox(v_a_1271_);
lean_dec(v_a_1271_);
v___x_1280_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1275_, v___x_1279_);
lean_dec_ref(v_lctx_1275_);
v___x_1281_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1263_);
v___x_1282_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1);
v___x_1283_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1283_, 0, v_env_1268_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
lean_ctor_set(v___x_1283_, 2, v___x_1280_);
lean_ctor_set(v___x_1283_, 3, v___x_1281_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set_tag(v___x_1277_, 3);
lean_ctor_set(v___x_1277_, 1, v_msg_1260_);
lean_ctor_set(v___x_1277_, 0, v___x_1283_);
v___x_1285_ = v___x_1277_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_msg_1260_);
v___x_1285_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; lean_object* v___x_1288_; 
lean_inc(v_ref_1266_);
v___x_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1286_, 0, v_ref_1266_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set_tag(v___x_1273_, 1);
lean_ctor_set(v___x_1273_, 0, v___x_1286_);
v___x_1288_ = v___x_1273_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec(v___x_1269_);
lean_dec_ref(v_env_1268_);
lean_dec_ref(v_msg_1260_);
v_a_1294_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1270_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1270_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___boxed(lean_object* v_msg_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v_msg_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0(lean_object* v_00_u03b1_1309_, lean_object* v_msg_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v_msg_1310_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___boxed(lean_object* v_00_u03b1_1318_, lean_object* v_msg_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0(v_00_u03b1_1318_, v_msg_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec_ref(v___y_1320_);
return v_res_1326_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__0));
v___x_1329_ = l_Lean_stringToMessageData(v___x_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(lean_object* v_upperBound_1330_, lean_object* v_s_1331_, lean_object* v_structName_1332_, lean_object* v_idx_1333_, lean_object* v_a_1334_, lean_object* v_b_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_a_1343_; uint8_t v___x_1347_; 
v___x_1347_ = lean_nat_dec_lt(v_a_1334_, v_upperBound_1330_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; 
lean_dec(v_a_1334_);
lean_dec(v_idx_1333_);
lean_dec(v_structName_1332_);
lean_dec(v_s_1331_);
v___x_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1348_, 0, v_b_1335_);
return v___x_1348_;
}
else
{
lean_object* v_snd_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1387_; 
v_snd_1349_ = lean_ctor_get(v_b_1335_, 1);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_b_1335_);
if (v_isSharedCheck_1387_ == 0)
{
lean_object* v_unused_1388_; 
v_unused_1388_ = lean_ctor_get(v_b_1335_, 0);
lean_dec(v_unused_1388_);
v___x_1351_ = v_b_1335_;
v_isShared_1352_ = v_isSharedCheck_1387_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_snd_1349_);
lean_dec(v_b_1335_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1387_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; 
v___x_1353_ = lean_box(0);
if (lean_obj_tag(v_snd_1349_) == 7)
{
lean_object* v_body_1354_; uint8_t v___x_1355_; 
v_body_1354_ = lean_ctor_get(v_snd_1349_, 2);
lean_inc_ref(v_body_1354_);
lean_dec_ref_known(v_snd_1349_, 3);
v___x_1355_ = l_Lean_Expr_hasLooseBVars(v_body_1354_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1357_; 
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 1, v_body_1354_);
lean_ctor_set(v___x_1351_, 0, v___x_1353_);
v___x_1357_ = v___x_1351_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_body_1354_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
v_a_1343_ = v___x_1357_;
goto v___jp_1342_;
}
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1359_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_1360_ = lean_expr_instantiate1(v_body_1354_, v___x_1359_);
lean_dec_ref(v_body_1354_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 1, v___x_1360_);
lean_ctor_set(v___x_1351_, 0, v___x_1353_);
v___x_1362_ = v___x_1351_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
v_a_1343_ = v___x_1362_;
goto v___jp_1342_;
}
}
}
else
{
uint8_t v___x_1364_; 
v___x_1364_ = l_Lean_Expr_isErased(v_snd_1349_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1365_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
lean_inc(v_s_1331_);
v___x_1366_ = l_Lean_mkFVar(v_s_1331_);
lean_inc(v_idx_1333_);
lean_inc(v_structName_1332_);
v___x_1367_ = l_Lean_mkProj(v_structName_1332_, v_idx_1333_, v___x_1366_);
v___x_1368_ = l_Lean_indentExpr(v___x_1367_);
v___x_1369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1365_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
v___x_1370_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_1369_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v___x_1372_; 
lean_dec_ref_known(v___x_1370_, 1);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v___x_1353_);
v___x_1372_ = v___x_1351_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_snd_1349_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
v_a_1343_ = v___x_1372_;
goto v___jp_1342_;
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_del_object(v___x_1351_);
lean_dec(v_snd_1349_);
lean_dec(v_a_1334_);
lean_dec(v_idx_1333_);
lean_dec(v_structName_1332_);
lean_dec(v_s_1331_);
v_a_1374_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1370_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1370_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
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
else
{
lean_object* v___x_1382_; lean_object* v___x_1384_; 
lean_dec(v_a_1334_);
lean_dec(v_idx_1333_);
lean_dec(v_structName_1332_);
lean_dec(v_s_1331_);
v___x_1382_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v___x_1382_);
v___x_1384_ = v___x_1351_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_snd_1349_);
v___x_1384_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1385_; 
v___x_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
return v___x_1385_;
}
}
}
}
}
v___jp_1342_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = lean_unsigned_to_nat(1u);
v___x_1345_ = lean_nat_add(v_a_1334_, v___x_1344_);
lean_dec(v_a_1334_);
v_a_1334_ = v___x_1345_;
v_b_1335_ = v_a_1343_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___boxed(lean_object* v_upperBound_1389_, lean_object* v_s_1390_, lean_object* v_structName_1391_, lean_object* v_idx_1392_, lean_object* v_a_1393_, lean_object* v_b_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_1389_, v_s_1390_, v_structName_1391_, v_idx_1392_, v_a_1393_, v_b_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v_upperBound_1389_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(lean_object* v_upperBound_1402_, lean_object* v_s_1403_, lean_object* v_structName_1404_, lean_object* v_idx_1405_, lean_object* v_a_1406_, lean_object* v_b_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_a_1415_; uint8_t v___x_1419_; 
v___x_1419_ = lean_nat_dec_lt(v_a_1406_, v_upperBound_1402_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; 
lean_dec(v_idx_1405_);
lean_dec(v_structName_1404_);
lean_dec(v_s_1403_);
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v_b_1407_);
return v___x_1420_;
}
else
{
lean_object* v_snd_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1459_; 
v_snd_1421_ = lean_ctor_get(v_b_1407_, 1);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_b_1407_);
if (v_isSharedCheck_1459_ == 0)
{
lean_object* v_unused_1460_; 
v_unused_1460_ = lean_ctor_get(v_b_1407_, 0);
lean_dec(v_unused_1460_);
v___x_1423_ = v_b_1407_;
v_isShared_1424_ = v_isSharedCheck_1459_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_snd_1421_);
lean_dec(v_b_1407_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1459_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_box(0);
if (lean_obj_tag(v_snd_1421_) == 7)
{
lean_object* v_body_1426_; uint8_t v___x_1427_; 
v_body_1426_ = lean_ctor_get(v_snd_1421_, 2);
lean_inc_ref(v_body_1426_);
lean_dec_ref_known(v_snd_1421_, 3);
v___x_1427_ = l_Lean_Expr_hasLooseBVars(v_body_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1429_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v_body_1426_);
lean_ctor_set(v___x_1423_, 0, v___x_1425_);
v___x_1429_ = v___x_1423_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_body_1426_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
v_a_1415_ = v___x_1429_;
goto v___jp_1414_;
}
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1431_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_1432_ = lean_expr_instantiate1(v_body_1426_, v___x_1431_);
lean_dec_ref(v_body_1426_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v___x_1432_);
lean_ctor_set(v___x_1423_, 0, v___x_1425_);
v___x_1434_ = v___x_1423_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
v_a_1415_ = v___x_1434_;
goto v___jp_1414_;
}
}
}
else
{
uint8_t v___x_1436_; 
v___x_1436_ = l_Lean_Expr_isErased(v_snd_1421_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1437_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
lean_inc(v_s_1403_);
v___x_1438_ = l_Lean_mkFVar(v_s_1403_);
lean_inc(v_idx_1405_);
lean_inc(v_structName_1404_);
v___x_1439_ = l_Lean_mkProj(v_structName_1404_, v_idx_1405_, v___x_1438_);
v___x_1440_ = l_Lean_indentExpr(v___x_1439_);
v___x_1441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1437_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_1441_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v___x_1444_; 
lean_dec_ref_known(v___x_1442_, 1);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1425_);
v___x_1444_ = v___x_1423_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_snd_1421_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
v_a_1415_ = v___x_1444_;
goto v___jp_1414_;
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_del_object(v___x_1423_);
lean_dec(v_snd_1421_);
lean_dec(v_idx_1405_);
lean_dec(v_structName_1404_);
lean_dec(v_s_1403_);
v_a_1446_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1442_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1442_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1456_; 
lean_dec(v_idx_1405_);
lean_dec(v_structName_1404_);
lean_dec(v_s_1403_);
v___x_1454_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1454_);
v___x_1456_ = v___x_1423_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1454_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_snd_1421_);
v___x_1456_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1457_; 
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
return v___x_1457_;
}
}
}
}
}
v___jp_1414_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1416_ = lean_unsigned_to_nat(1u);
v___x_1417_ = lean_nat_add(v_a_1406_, v___x_1416_);
v___x_1418_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_1402_, v_s_1403_, v_structName_1404_, v_idx_1405_, v___x_1417_, v_a_1415_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1418_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg___boxed(lean_object* v_upperBound_1461_, lean_object* v_s_1462_, lean_object* v_structName_1463_, lean_object* v_idx_1464_, lean_object* v_a_1465_, lean_object* v_b_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_upperBound_1461_, v_s_1462_, v_structName_1463_, v_idx_1464_, v_a_1465_, v_b_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v_a_1465_);
lean_dec(v_upperBound_1461_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_ref_1474_, lean_object* v_msg_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_toCold_1482_; lean_object* v_currRecDepth_1483_; lean_object* v_ref_1484_; uint16_t v_optionFlags_1485_; uint8_t v_suppressElabErrors_1486_; uint8_t v_checkDeprecated_1487_; uint8_t v_isRecordingDeps_1488_; lean_object* v_ref_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_toCold_1482_ = lean_ctor_get(v___y_1479_, 0);
v_currRecDepth_1483_ = lean_ctor_get(v___y_1479_, 1);
v_ref_1484_ = lean_ctor_get(v___y_1479_, 2);
v_optionFlags_1485_ = lean_ctor_get_uint16(v___y_1479_, sizeof(void*)*3);
v_suppressElabErrors_1486_ = lean_ctor_get_uint8(v___y_1479_, sizeof(void*)*3 + 2);
v_checkDeprecated_1487_ = lean_ctor_get_uint8(v___y_1479_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1488_ = lean_ctor_get_uint8(v___y_1479_, sizeof(void*)*3 + 4);
v_ref_1489_ = l_Lean_replaceRef(v_ref_1474_, v_ref_1484_);
lean_inc(v_currRecDepth_1483_);
lean_inc_ref(v_toCold_1482_);
v___x_1490_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1490_, 0, v_toCold_1482_);
lean_ctor_set(v___x_1490_, 1, v_currRecDepth_1483_);
lean_ctor_set(v___x_1490_, 2, v_ref_1489_);
lean_ctor_set_uint16(v___x_1490_, sizeof(void*)*3, v_optionFlags_1485_);
lean_ctor_set_uint8(v___x_1490_, sizeof(void*)*3 + 2, v_suppressElabErrors_1486_);
lean_ctor_set_uint8(v___x_1490_, sizeof(void*)*3 + 3, v_checkDeprecated_1487_);
lean_ctor_set_uint8(v___x_1490_, sizeof(void*)*3 + 4, v_isRecordingDeps_1488_);
v___x_1491_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v_msg_1475_, v___y_1477_, v___y_1478_, v___x_1490_, v___y_1480_);
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
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__16(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__15));
v___x_1528_ = l_Lean_stringToMessageData(v___x_1527_);
return v___x_1528_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__18(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__17));
v___x_1531_ = l_Lean_stringToMessageData(v___x_1530_);
return v___x_1531_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__20(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__19));
v___x_1534_ = l_Lean_stringToMessageData(v___x_1533_);
return v___x_1534_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__22(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__21));
v___x_1537_ = l_Lean_stringToMessageData(v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(lean_object* v_msg_1538_, lean_object* v_declHint_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v_env_1544_; uint8_t v___x_1545_; 
v___x_1542_ = lean_box(0);
v___x_1543_ = lean_st_ref_get(v___y_1540_);
v_env_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc_ref(v_env_1544_);
lean_dec(v___x_1543_);
v___x_1545_ = l_Lean_Name_isAnonymous(v_declHint_1539_);
if (v___x_1545_ == 0)
{
uint8_t v_isExporting_1546_; 
v_isExporting_1546_ = lean_ctor_get_uint8(v_env_1544_, sizeof(void*)*13);
if (v_isExporting_1546_ == 0)
{
lean_object* v___x_1547_; 
lean_dec_ref(v_env_1544_);
lean_dec(v_declHint_1539_);
v___x_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1547_, 0, v_msg_1538_);
return v___x_1547_;
}
else
{
lean_object* v___x_1548_; uint8_t v___x_1549_; 
lean_inc_ref(v_env_1544_);
v___x_1548_ = l_Lean_Environment_setExporting(v_env_1544_, v___x_1545_);
lean_inc(v_declHint_1539_);
lean_inc_ref(v___x_1548_);
v___x_1549_ = l_Lean_Environment_contains(v___x_1548_, v_declHint_1539_, v_isExporting_1546_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; 
lean_dec_ref(v___x_1548_);
lean_dec_ref(v_env_1544_);
lean_dec(v_declHint_1539_);
v___x_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1550_, 0, v_msg_1538_);
return v___x_1550_;
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v_c_1556_; lean_object* v___x_1557_; 
v___x_1551_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1);
v___x_1552_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0);
v___x_1553_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1548_);
v___x_1554_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1548_);
lean_ctor_set(v___x_1554_, 1, v___x_1551_);
lean_ctor_set(v___x_1554_, 2, v___x_1552_);
lean_ctor_set(v___x_1554_, 3, v___x_1553_);
lean_inc(v_declHint_1539_);
v___x_1555_ = l_Lean_MessageData_ofConstName(v_declHint_1539_, v___x_1545_);
v_c_1556_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1556_, 0, v___x_1554_);
lean_ctor_set(v_c_1556_, 1, v___x_1555_);
v___x_1557_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1548_, v_declHint_1539_);
lean_dec_ref(v___x_1548_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_dec_ref(v_env_1544_);
lean_dec(v_declHint_1539_);
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
lean_ctor_set(v___x_1563_, 0, v_msg_1538_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
return v___x_1564_;
}
else
{
lean_object* v_val_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1618_; 
v_val_1565_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1567_ = v___x_1557_;
v_isShared_1568_ = v_isSharedCheck_1618_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_val_1565_);
lean_dec(v___x_1557_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1618_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1569_; lean_object* v_modules_1570_; lean_object* v_moduleNames_1571_; lean_object* v_mod_1572_; uint8_t v___x_1587_; 
v___x_1569_ = l_Lean_Environment_header(v_env_1544_);
lean_dec_ref(v_env_1544_);
v_modules_1570_ = lean_ctor_get(v___x_1569_, 3);
lean_inc_ref(v_modules_1570_);
v_moduleNames_1571_ = lean_ctor_get(v___x_1569_, 4);
lean_inc_ref(v_moduleNames_1571_);
lean_dec_ref(v___x_1569_);
v_mod_1572_ = lean_array_get(v___x_1542_, v_moduleNames_1571_, v_val_1565_);
lean_dec_ref(v_moduleNames_1571_);
v___x_1587_ = l_Lean_isPrivateName(v_declHint_1539_);
lean_dec(v_declHint_1539_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; uint8_t v___x_1589_; 
v___x_1588_ = lean_array_get_size(v_modules_1570_);
v___x_1589_ = lean_nat_dec_lt(v_val_1565_, v___x_1588_);
if (v___x_1589_ == 0)
{
lean_dec_ref(v_modules_1570_);
lean_dec(v_val_1565_);
goto v___jp_1573_;
}
else
{
lean_object* v___x_1590_; lean_object* v_toImport_1591_; uint8_t v_isExported_1592_; 
v___x_1590_ = lean_array_fget(v_modules_1570_, v_val_1565_);
lean_dec(v_val_1565_);
lean_dec_ref(v_modules_1570_);
v_toImport_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc_ref(v_toImport_1591_);
lean_dec(v___x_1590_);
v_isExported_1592_ = lean_ctor_get_uint8(v_toImport_1591_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1591_);
if (v_isExported_1592_ == 0)
{
goto v___jp_1573_;
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
lean_del_object(v___x_1567_);
v___x_1593_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12);
v___x_1594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v_c_1556_);
v___x_1595_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14);
v___x_1596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1594_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
v___x_1597_ = l_Lean_MessageData_ofName(v_mod_1572_);
lean_inc_ref(v___x_1597_);
v___x_1598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1596_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__16);
v___x_1600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1598_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
v___x_1601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
lean_ctor_set(v___x_1601_, 1, v___x_1597_);
v___x_1602_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__18);
v___x_1603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1601_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
v___x_1604_ = l_Lean_MessageData_note(v___x_1603_);
v___x_1605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1605_, 0, v_msg_1538_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
return v___x_1606_;
}
}
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec_ref(v_modules_1570_);
lean_del_object(v___x_1567_);
lean_dec(v_val_1565_);
v___x_1607_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2);
v___x_1608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
lean_ctor_set(v___x_1608_, 1, v_c_1556_);
v___x_1609_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__20);
v___x_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1608_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = l_Lean_MessageData_ofName(v_mod_1572_);
v___x_1612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__22);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = l_Lean_MessageData_note(v___x_1614_);
v___x_1616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1616_, 0, v_msg_1538_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
return v___x_1617_;
}
v___jp_1573_:
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
lean_ctor_set(v___x_1583_, 0, v_msg_1538_);
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
}
}
}
}
}
else
{
lean_object* v___x_1619_; 
lean_dec_ref(v_env_1544_);
lean_dec(v_declHint_1539_);
v___x_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1619_, 0, v_msg_1538_);
return v___x_1619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_msg_1620_, lean_object* v_declHint_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_1620_, v_declHint_1621_, v___y_1622_);
lean_dec(v___y_1622_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(lean_object* v_msg_1625_, lean_object* v_declHint_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1643_; 
v___x_1633_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_1625_, v_declHint_1626_, v___y_1631_);
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1643_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1643_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1638_ = l_Lean_unknownIdentifierMessageTag;
v___x_1639_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
lean_ctor_set(v___x_1639_, 1, v_a_1634_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1639_);
v___x_1641_ = v___x_1636_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_msg_1644_, lean_object* v_declHint_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(v_msg_1644_, v_declHint_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec_ref(v___y_1646_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1653_, lean_object* v_msg_1654_, lean_object* v_declHint_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___x_1662_; lean_object* v_a_1663_; lean_object* v___x_1664_; 
v___x_1662_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(v_msg_1654_, v_declHint_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1663_);
lean_dec_ref(v___x_1662_);
v___x_1664_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_1653_, v_a_1663_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1665_, lean_object* v_msg_1666_, lean_object* v_declHint_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1665_, v_msg_1666_, v_declHint_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v_ref_1665_);
return v_res_1674_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__0));
v___x_1677_ = l_Lean_stringToMessageData(v___x_1676_);
return v___x_1677_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__2));
v___x_1680_ = l_Lean_stringToMessageData(v___x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(lean_object* v_ref_1681_, lean_object* v_constName_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___x_1689_; uint8_t v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1689_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_1690_ = 0;
lean_inc(v_constName_1682_);
v___x_1691_ = l_Lean_MessageData_ofConstName(v_constName_1682_, v___x_1690_);
v___x_1692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1689_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v___x_1693_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3);
v___x_1694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1692_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v___x_1695_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1681_, v___x_1694_, v_constName_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1696_, lean_object* v_constName_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1696_, v_constName_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v_ref_1696_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(lean_object* v_constName_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v_ref_1712_; lean_object* v___x_1713_; 
v_ref_1712_ = lean_ctor_get(v___y_1709_, 2);
v___x_1713_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1712_, v_constName_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_constName_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec_ref(v___y_1715_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(lean_object* v_constName_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v___x_1729_; lean_object* v_env_1730_; uint8_t v___x_1731_; lean_object* v___x_1732_; 
v___x_1729_ = lean_st_ref_get(v___y_1727_);
v_env_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc_ref(v_env_1730_);
lean_dec(v___x_1729_);
v___x_1731_ = 0;
lean_inc(v_constName_1722_);
v___x_1732_ = l_Lean_Environment_find_x3f(v_env_1730_, v_constName_1722_, v___x_1731_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
return v___x_1733_;
}
else
{
lean_object* v_val_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
lean_dec(v_constName_1722_);
v_val_1734_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1732_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_val_1734_);
lean_dec(v___x_1732_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set_tag(v___x_1736_, 0);
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_val_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1___boxed(lean_object* v_constName_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(v_constName_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec_ref(v___y_1743_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(lean_object* v_structName_1750_, lean_object* v_idx_1751_, lean_object* v_s_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___x_1771_; 
lean_inc(v_s_1752_);
v___x_1771_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_s_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1867_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1774_ = v___x_1771_;
v_isShared_1775_ = v_isSharedCheck_1867_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1771_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1867_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = l_Lean_Expr_headBeta(v_a_1772_);
v___x_1777_ = l_Lean_Expr_isErased(v___x_1776_);
if (v___x_1777_ == 0)
{
uint8_t v___x_1778_; 
v___x_1778_ = l_Lean_Expr_isAny(v___x_1776_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; 
lean_del_object(v___x_1774_);
v___x_1779_ = l_Lean_Expr_getAppFn(v___x_1776_);
if (lean_obj_tag(v___x_1779_) == 4)
{
lean_object* v_declName_1780_; lean_object* v_us_1781_; lean_object* v___x_1782_; lean_object* v_env_1783_; lean_object* v___x_1784_; 
v_declName_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_declName_1780_);
v_us_1781_ = lean_ctor_get(v___x_1779_, 1);
lean_inc(v_us_1781_);
lean_dec_ref_known(v___x_1779_, 2);
v___x_1782_ = lean_st_ref_get(v_a_1757_);
v_env_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc_ref(v_env_1783_);
lean_dec(v___x_1782_);
v___x_1784_ = l_Lean_Environment_find_x3f(v_env_1783_, v_declName_1780_, v___x_1778_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_dec(v_us_1781_);
lean_dec_ref(v___x_1776_);
v___y_1760_ = v_a_1753_;
v___y_1761_ = v_a_1754_;
v___y_1762_ = v_a_1755_;
v___y_1763_ = v_a_1756_;
v___y_1764_ = v_a_1757_;
goto v___jp_1759_;
}
else
{
lean_object* v_val_1785_; 
v_val_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_val_1785_);
lean_dec_ref_known(v___x_1784_, 1);
if (lean_obj_tag(v_val_1785_) == 5)
{
lean_object* v_val_1786_; lean_object* v_ctors_1787_; 
v_val_1786_ = lean_ctor_get(v_val_1785_, 0);
lean_inc_ref(v_val_1786_);
lean_dec_ref_known(v_val_1785_, 1);
v_ctors_1787_ = lean_ctor_get(v_val_1786_, 4);
lean_inc(v_ctors_1787_);
if (lean_obj_tag(v_ctors_1787_) == 1)
{
lean_object* v_tail_1788_; 
v_tail_1788_ = lean_ctor_get(v_ctors_1787_, 1);
if (lean_obj_tag(v_tail_1788_) == 0)
{
lean_object* v_numParams_1789_; lean_object* v_numIndices_1790_; lean_object* v_head_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1857_; 
v_numParams_1789_ = lean_ctor_get(v_val_1786_, 1);
lean_inc(v_numParams_1789_);
v_numIndices_1790_ = lean_ctor_get(v_val_1786_, 2);
lean_inc(v_numIndices_1790_);
lean_dec_ref(v_val_1786_);
v_head_1791_ = lean_ctor_get(v_ctors_1787_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v_ctors_1787_);
if (v_isSharedCheck_1857_ == 0)
{
lean_object* v_unused_1858_; 
v_unused_1858_ = lean_ctor_get(v_ctors_1787_, 1);
lean_dec(v_unused_1858_);
v___x_1793_ = v_ctors_1787_;
v_isShared_1794_ = v_isSharedCheck_1857_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_head_1791_);
lean_dec(v_ctors_1787_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1857_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(v_head_1791_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_a_1796_);
lean_dec_ref_known(v___x_1795_, 1);
if (lean_obj_tag(v_a_1796_) == 6)
{
lean_object* v_val_1797_; lean_object* v_dummy_1798_; lean_object* v_nargs_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v_val_1797_ = lean_ctor_get(v_a_1796_, 0);
lean_inc_ref(v_val_1797_);
lean_dec_ref_known(v_a_1796_, 1);
v_dummy_1798_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0);
v_nargs_1799_ = l_Lean_Expr_getAppNumArgs(v___x_1776_);
lean_inc(v_nargs_1799_);
v___x_1800_ = lean_mk_array(v_nargs_1799_, v_dummy_1798_);
v___x_1801_ = lean_unsigned_to_nat(1u);
v___x_1802_ = lean_nat_sub(v_nargs_1799_, v___x_1801_);
lean_dec(v_nargs_1799_);
v___x_1803_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1776_, v___x_1800_, v___x_1802_);
v___x_1804_ = lean_nat_add(v_numParams_1789_, v_numIndices_1790_);
lean_dec(v_numIndices_1790_);
v___x_1805_ = lean_array_get_size(v___x_1803_);
v___x_1806_ = lean_nat_dec_eq(v___x_1804_, v___x_1805_);
lean_dec(v___x_1804_);
if (v___x_1806_ == 0)
{
lean_dec_ref(v___x_1803_);
lean_dec_ref(v_val_1797_);
lean_del_object(v___x_1793_);
lean_dec(v_numParams_1789_);
lean_dec(v_us_1781_);
v___y_1760_ = v_a_1753_;
v___y_1761_ = v_a_1754_;
v___y_1762_ = v_a_1755_;
v___y_1763_ = v_a_1756_;
v___y_1764_ = v_a_1757_;
goto v___jp_1759_;
}
else
{
lean_object* v_toConstantVal_1807_; lean_object* v_name_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v_toConstantVal_1807_ = lean_ctor_get(v_val_1797_, 0);
lean_inc_ref(v_toConstantVal_1807_);
lean_dec_ref(v_val_1797_);
v_name_1808_ = lean_ctor_get(v_toConstantVal_1807_, 0);
lean_inc(v_name_1808_);
lean_dec_ref(v_toConstantVal_1807_);
v___x_1809_ = l_Lean_mkConst(v_name_1808_, v_us_1781_);
v___x_1810_ = lean_unsigned_to_nat(0u);
v___x_1811_ = l_Array_toSubarray___redArg(v___x_1803_, v___x_1810_, v_numParams_1789_);
v___x_1812_ = l_Subarray_copy___redArg(v___x_1811_);
v___x_1813_ = l_Lean_mkAppN(v___x_1809_, v___x_1812_);
lean_dec_ref(v___x_1812_);
v___x_1814_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(v___x_1813_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1816_; lean_object* v___x_1818_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
lean_dec_ref_known(v___x_1814_, 1);
v___x_1816_ = lean_box(0);
if (v_isShared_1794_ == 0)
{
lean_ctor_set_tag(v___x_1793_, 0);
lean_ctor_set(v___x_1793_, 1, v_a_1815_);
lean_ctor_set(v___x_1793_, 0, v___x_1816_);
v___x_1818_ = v___x_1793_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_a_1815_);
v___x_1818_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1819_; 
lean_inc(v_structName_1750_);
lean_inc(v_s_1752_);
lean_inc(v_idx_1751_);
v___x_1819_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_idx_1751_, v_s_1752_, v_structName_1750_, v_idx_1751_, v___x_1810_, v___x_1818_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1839_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1822_ = v___x_1819_;
v_isShared_1823_ = v_isSharedCheck_1839_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1839_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v_fst_1824_; 
v_fst_1824_ = lean_ctor_get(v_a_1820_, 0);
if (lean_obj_tag(v_fst_1824_) == 0)
{
lean_object* v_snd_1825_; 
v_snd_1825_ = lean_ctor_get(v_a_1820_, 1);
lean_inc(v_snd_1825_);
lean_dec(v_a_1820_);
if (lean_obj_tag(v_snd_1825_) == 7)
{
lean_object* v_binderType_1826_; lean_object* v___x_1828_; 
lean_dec(v_s_1752_);
lean_dec(v_idx_1751_);
lean_dec(v_structName_1750_);
v_binderType_1826_ = lean_ctor_get(v_snd_1825_, 1);
lean_inc_ref(v_binderType_1826_);
lean_dec_ref_known(v_snd_1825_, 3);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v_binderType_1826_);
v___x_1828_ = v___x_1822_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_binderType_1826_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
else
{
uint8_t v___x_1830_; 
v___x_1830_ = l_Lean_Expr_isErased(v_snd_1825_);
lean_dec(v_snd_1825_);
if (v___x_1830_ == 0)
{
lean_del_object(v___x_1822_);
v___y_1760_ = v_a_1753_;
v___y_1761_ = v_a_1754_;
v___y_1762_ = v_a_1755_;
v___y_1763_ = v_a_1756_;
v___y_1764_ = v_a_1757_;
goto v___jp_1759_;
}
else
{
lean_object* v___x_1831_; lean_object* v___x_1833_; 
lean_dec(v_s_1752_);
lean_dec(v_idx_1751_);
lean_dec(v_structName_1750_);
v___x_1831_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v___x_1831_);
v___x_1833_ = v___x_1822_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
else
{
lean_object* v_val_1835_; lean_object* v___x_1837_; 
lean_inc_ref(v_fst_1824_);
lean_dec(v_a_1820_);
lean_dec(v_s_1752_);
lean_dec(v_idx_1751_);
lean_dec(v_structName_1750_);
v_val_1835_ = lean_ctor_get(v_fst_1824_, 0);
lean_inc(v_val_1835_);
lean_dec_ref_known(v_fst_1824_, 1);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v_val_1835_);
v___x_1837_ = v___x_1822_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_val_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_dec(v_s_1752_);
lean_dec(v_idx_1751_);
lean_dec(v_structName_1750_);
v_a_1840_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1819_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1819_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
else
{
lean_del_object(v___x_1793_);
lean_dec(v_s_1752_);
lean_dec(v_idx_1751_);
lean_dec(v_structName_1750_);
return v___x_1814_;
}
}
}
else
{
lean_dec(v_a_1796_);
lean_del_object(v___x_1793_);
lean_dec(v_numIndices_1790_);
lean_dec(v_numParams_1789_);
lean_dec(v_us_1781_);
lean_dec_ref(v___x_1776_);
v___y_1760_ = v_a_1753_;
v___y_1761_ = v_a_1754_;
v___y_1762_ = v_a_1755_;
v___y_1763_ = v_a_1756_;
v___y_1764_ = v_a_1757_;
goto v___jp_1759_;
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_del_object(v___x_1793_);
lean_dec(v_numIndices_1790_);
lean_dec(v_numParams_1789_);
lean_dec(v_us_1781_);
lean_dec_ref(v___x_1776_);
lean_dec(v_s_1752_);
lean_dec(v_idx_1751_);
lean_dec(v_structName_1750_);
v_a_1849_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1795_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1795_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1787_, 2);
lean_dec_ref(v_val_1786_);
lean_dec(v_us_1781_);
lean_dec_ref(v___x_1776_);
v___y_1760_ = v_a_1753_;
v___y_1761_ = v_a_1754_;
v___y_1762_ = v_a_1755_;
v___y_1763_ = v_a_1756_;
v___y_1764_ = v_a_1757_;
goto v___jp_1759_;
}
}
else
{
lean_dec(v_ctors_1787_);
lean_dec_ref(v_val_1786_);
lean_dec(v_us_1781_);
lean_dec_ref(v___x_1776_);
v___y_1760_ = v_a_1753_;
v___y_1761_ = v_a_1754_;
v___y_1762_ = v_a_1755_;
v___y_1763_ = v_a_1756_;
v___y_1764_ = v_a_1757_;
goto v___jp_1759_;
}
}
else
{
lean_dec(v_val_1785_);
lean_dec(v_us_1781_);
lean_dec_ref(v___x_1776_);
v___y_1760_ = v_a_1753_;
v___y_1761_ = v_a_1754_;
v___y_1762_ = v_a_1755_;
v___y_1763_ = v_a_1756_;
v___y_1764_ = v_a_1757_;
goto v___jp_1759_;
}
}
}
else
{
lean_dec_ref(v___x_1779_);
lean_dec_ref(v___x_1776_);
v___y_1760_ = v_a_1753_;
v___y_1761_ = v_a_1754_;
v___y_1762_ = v_a_1755_;
v___y_1763_ = v_a_1756_;
v___y_1764_ = v_a_1757_;
goto v___jp_1759_;
}
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
lean_dec_ref(v___x_1776_);
lean_dec(v_s_1752_);
lean_dec(v_idx_1751_);
lean_dec(v_structName_1750_);
v___x_1859_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v___x_1859_);
v___x_1861_ = v___x_1774_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1865_; 
lean_dec_ref(v___x_1776_);
lean_dec(v_s_1752_);
lean_dec(v_idx_1751_);
lean_dec(v_structName_1750_);
v___x_1863_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v___x_1863_);
v___x_1865_ = v___x_1774_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
else
{
lean_dec(v_s_1752_);
lean_dec(v_idx_1751_);
lean_dec(v_structName_1750_);
return v___x_1771_;
}
v___jp_1759_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1765_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
v___x_1766_ = l_Lean_mkFVar(v_s_1752_);
v___x_1767_ = l_Lean_mkProj(v_structName_1750_, v_idx_1751_, v___x_1766_);
v___x_1768_ = l_Lean_indentExpr(v___x_1767_);
v___x_1769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1765_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
v___x_1770_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_1769_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
return v___x_1770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferProjType___boxed(lean_object* v_structName_1868_, lean_object* v_idx_1869_, lean_object* v_s_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(v_structName_1868_, v_idx_1869_, v_s_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec_ref(v_a_1871_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2(lean_object* v_upperBound_1878_, lean_object* v_s_1879_, lean_object* v_structName_1880_, lean_object* v_idx_1881_, lean_object* v_inst_1882_, lean_object* v_R_1883_, lean_object* v_a_1884_, lean_object* v_b_1885_, lean_object* v_c_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_upperBound_1878_, v_s_1879_, v_structName_1880_, v_idx_1881_, v_a_1884_, v_b_1885_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___boxed(lean_object* v_upperBound_1894_, lean_object* v_s_1895_, lean_object* v_structName_1896_, lean_object* v_idx_1897_, lean_object* v_inst_1898_, lean_object* v_R_1899_, lean_object* v_a_1900_, lean_object* v_b_1901_, lean_object* v_c_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2(v_upperBound_1894_, v_s_1895_, v_structName_1896_, v_idx_1897_, v_inst_1898_, v_R_1899_, v_a_1900_, v_b_1901_, v_c_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v_a_1900_);
lean_dec(v_upperBound_1894_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1(lean_object* v_00_u03b1_1910_, lean_object* v_constName_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___boxed(lean_object* v_00_u03b1_1919_, lean_object* v_constName_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1(v_00_u03b1_1919_, v_constName_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec_ref(v___y_1921_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3(lean_object* v_upperBound_1928_, lean_object* v_s_1929_, lean_object* v_structName_1930_, lean_object* v_idx_1931_, lean_object* v_inst_1932_, lean_object* v_R_1933_, lean_object* v_a_1934_, lean_object* v_b_1935_, lean_object* v_c_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_1928_, v_s_1929_, v_structName_1930_, v_idx_1931_, v_a_1934_, v_b_1935_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___boxed(lean_object* v_upperBound_1944_, lean_object* v_s_1945_, lean_object* v_structName_1946_, lean_object* v_idx_1947_, lean_object* v_inst_1948_, lean_object* v_R_1949_, lean_object* v_a_1950_, lean_object* v_b_1951_, lean_object* v_c_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3(v_upperBound_1944_, v_s_1945_, v_structName_1946_, v_idx_1947_, v_inst_1948_, v_R_1949_, v_a_1950_, v_b_1951_, v_c_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v_upperBound_1944_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_1960_, lean_object* v_ref_1961_, lean_object* v_constName_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1961_, v_constName_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1970_, lean_object* v_ref_1971_, lean_object* v_constName_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2(v_00_u03b1_1970_, v_ref_1971_, v_constName_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v_ref_1971_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1980_, lean_object* v_ref_1981_, lean_object* v_msg_1982_, lean_object* v_declHint_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1981_, v_msg_1982_, v_declHint_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1991_, lean_object* v_ref_1992_, lean_object* v_msg_1993_, lean_object* v_declHint_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4(v_00_u03b1_1991_, v_ref_1992_, v_msg_1993_, v_declHint_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v_ref_1992_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msg_2002_, lean_object* v_declHint_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_2002_, v_declHint_2003_, v___y_2008_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_2011_, lean_object* v_declHint_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_2011_, v_declHint_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec_ref(v___y_2013_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b1_2020_, lean_object* v_ref_2021_, lean_object* v_msg_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_2021_, v_msg_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b1_2030_, lean_object* v_ref_2031_, lean_object* v_msg_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7(v_00_u03b1_2030_, v_ref_2031_, v_msg_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v_ref_2031_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(lean_object* v_e_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_){
_start:
{
switch(lean_obj_tag(v_e_2040_))
{
case 0:
{
lean_object* v_value_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2055_; 
v_value_2047_ = lean_ctor_get(v_e_2040_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_e_2040_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2049_ = v_e_2040_;
v_isShared_2050_ = v_isSharedCheck_2055_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_value_2047_);
lean_dec(v_e_2040_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2055_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; lean_object* v___x_2053_; 
v___x_2051_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType(v_value_2047_);
lean_dec_ref(v_value_2047_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2051_);
v___x_2053_ = v___x_2049_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2051_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
case 1:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2056_);
return v___x_2057_;
}
case 2:
{
lean_object* v_typeName_2058_; lean_object* v_idx_2059_; lean_object* v_struct_2060_; lean_object* v___x_2061_; 
v_typeName_2058_ = lean_ctor_get(v_e_2040_, 0);
lean_inc(v_typeName_2058_);
v_idx_2059_ = lean_ctor_get(v_e_2040_, 1);
lean_inc(v_idx_2059_);
v_struct_2060_ = lean_ctor_get(v_e_2040_, 2);
lean_inc(v_struct_2060_);
lean_dec_ref_known(v_e_2040_, 3);
v___x_2061_ = l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(v_typeName_2058_, v_idx_2059_, v_struct_2060_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
return v___x_2061_;
}
case 3:
{
lean_object* v_declName_2062_; lean_object* v_us_2063_; lean_object* v_args_2064_; lean_object* v___x_2065_; 
v_declName_2062_ = lean_ctor_get(v_e_2040_, 0);
lean_inc(v_declName_2062_);
v_us_2063_ = lean_ctor_get(v_e_2040_, 1);
lean_inc(v_us_2063_);
v_args_2064_ = lean_ctor_get(v_e_2040_, 2);
lean_inc_ref(v_args_2064_);
lean_dec_ref_known(v_e_2040_, 3);
v___x_2065_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(v_declName_2062_, v_us_2063_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v___x_2067_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref_known(v___x_2065_, 1);
v___x_2067_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2066_, v_args_2064_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
return v___x_2067_;
}
else
{
lean_dec_ref(v_args_2064_);
return v___x_2065_;
}
}
default: 
{
lean_object* v_fvarId_2068_; lean_object* v_args_2069_; lean_object* v___x_2070_; 
v_fvarId_2068_ = lean_ctor_get(v_e_2040_, 0);
lean_inc(v_fvarId_2068_);
v_args_2069_ = lean_ctor_get(v_e_2040_, 1);
lean_inc_ref(v_args_2069_);
lean_dec_ref_known(v_e_2040_, 2);
v___x_2070_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_fvarId_2068_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2072_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref_known(v___x_2070_, 1);
v___x_2072_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2071_, v_args_2069_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
return v___x_2072_;
}
else
{
lean_dec_ref(v_args_2069_);
return v___x_2070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType___boxed(lean_object* v_e_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(v_e_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
lean_dec(v_a_2078_);
lean_dec_ref(v_a_2077_);
lean_dec(v_a_2076_);
lean_dec_ref(v_a_2075_);
lean_dec_ref(v_a_2074_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType(lean_object* v_e_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2087_ = lean_unsigned_to_nat(32u);
v___x_2088_ = lean_mk_empty_array_with_capacity(v___x_2087_);
lean_dec_ref(v___x_2088_);
v___x_2089_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2090_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_e_2081_, v___x_2089_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType___boxed(lean_object* v_e_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lean_Compiler_LCNF_inferType(v_e_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
lean_dec(v_a_2095_);
lean_dec_ref(v_a_2094_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(lean_object* v_msg_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v___x_2104_; lean_object* v_toApplicative_2105_; lean_object* v_toFunctor_2106_; lean_object* v_toSeq_2107_; lean_object* v_toSeqLeft_2108_; lean_object* v_toSeqRight_2109_; lean_object* v___f_2110_; lean_object* v___f_2111_; lean_object* v___f_2112_; lean_object* v___f_2113_; lean_object* v___x_2114_; lean_object* v___f_2115_; lean_object* v___f_2116_; lean_object* v___f_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___f_2123_; lean_object* v___x_148__overap_2124_; lean_object* v___x_2125_; 
v___x_2104_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_2105_ = lean_ctor_get(v___x_2104_, 0);
v_toFunctor_2106_ = lean_ctor_get(v_toApplicative_2105_, 0);
v_toSeq_2107_ = lean_ctor_get(v_toApplicative_2105_, 2);
v_toSeqLeft_2108_ = lean_ctor_get(v_toApplicative_2105_, 3);
v_toSeqRight_2109_ = lean_ctor_get(v_toApplicative_2105_, 4);
v___f_2110_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_2111_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2106_, 2);
v___f_2112_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2112_, 0, v_toFunctor_2106_);
v___f_2113_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2113_, 0, v_toFunctor_2106_);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___f_2112_);
lean_ctor_set(v___x_2114_, 1, v___f_2113_);
lean_inc(v_toSeqRight_2109_);
v___f_2115_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2115_, 0, v_toSeqRight_2109_);
lean_inc(v_toSeqLeft_2108_);
v___f_2116_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2116_, 0, v_toSeqLeft_2108_);
lean_inc(v_toSeq_2107_);
v___f_2117_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2117_, 0, v_toSeq_2107_);
v___x_2118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2114_);
lean_ctor_set(v___x_2118_, 1, v___f_2110_);
lean_ctor_set(v___x_2118_, 2, v___f_2117_);
lean_ctor_set(v___x_2118_, 3, v___f_2116_);
lean_ctor_set(v___x_2118_, 4, v___f_2115_);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
lean_ctor_set(v___x_2119_, 1, v___f_2111_);
v___x_2120_ = l_StateRefT_x27_instMonad___redArg(v___x_2119_);
v___x_2121_ = l_Lean_instInhabitedExpr;
v___x_2122_ = l_instInhabitedOfMonad___redArg(v___x_2120_, v___x_2121_);
v___f_2123_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2123_, 0, v___x_2122_);
v___x_148__overap_2124_ = lean_panic_fn_borrowed(v___f_2123_, v_msg_2098_);
lean_dec_ref(v___f_2123_);
lean_inc(v___y_2102_);
lean_inc_ref(v___y_2101_);
lean_inc(v___y_2100_);
lean_inc_ref(v___y_2099_);
v___x_2125_ = lean_apply_5(v___x_148__overap_2124_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, lean_box(0));
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0___boxed(lean_object* v_msg_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v_msg_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
return v_res_2132_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inferAppType___closed__2(void){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2135_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2136_ = lean_unsigned_to_nat(15u);
v___x_2137_ = lean_unsigned_to_nat(258u);
v___x_2138_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__0));
v___x_2139_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2140_ = l_mkPanicMessageWithDecl(v___x_2139_, v___x_2138_, v___x_2137_, v___x_2136_, v___x_2135_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType(uint8_t v_pu_2141_, lean_object* v_fnType_2142_, lean_object* v_args_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
if (v_pu_2141_ == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2150_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_fnType_2142_, v_args_2143_, v___x_2149_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_);
return v___x_2150_;
}
else
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
lean_dec_ref(v_args_2143_);
lean_dec_ref(v_fnType_2142_);
v___x_2151_ = lean_obj_once(&l_Lean_Compiler_LCNF_inferAppType___closed__2, &l_Lean_Compiler_LCNF_inferAppType___closed__2_once, _init_l_Lean_Compiler_LCNF_inferAppType___closed__2);
v___x_2152_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2151_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_);
return v___x_2152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType___boxed(lean_object* v_pu_2153_, lean_object* v_fnType_2154_, lean_object* v_args_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
uint8_t v_pu_boxed_2161_; lean_object* v_res_2162_; 
v_pu_boxed_2161_ = lean_unbox(v_pu_2153_);
v_res_2162_ = l_Lean_Compiler_LCNF_inferAppType(v_pu_boxed_2161_, v_fnType_2154_, v_args_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
lean_dec(v_a_2159_);
lean_dec_ref(v_a_2158_);
lean_dec(v_a_2157_);
lean_dec_ref(v_a_2156_);
return v_res_2162_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Arg_inferType___closed__1(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2164_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2165_ = lean_unsigned_to_nat(15u);
v___x_2166_ = lean_unsigned_to_nat(263u);
v___x_2167_ = ((lean_object*)(l_Lean_Compiler_LCNF_Arg_inferType___closed__0));
v___x_2168_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2169_ = l_mkPanicMessageWithDecl(v___x_2168_, v___x_2167_, v___x_2166_, v___x_2165_, v___x_2164_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType(uint8_t v_pu_2170_, lean_object* v_arg_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_){
_start:
{
if (v_pu_2170_ == 0)
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2178_ = l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(v_arg_2171_, v___x_2177_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
return v___x_2178_;
}
else
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
lean_dec(v_arg_2171_);
v___x_2179_ = lean_obj_once(&l_Lean_Compiler_LCNF_Arg_inferType___closed__1, &l_Lean_Compiler_LCNF_Arg_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_Arg_inferType___closed__1);
v___x_2180_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2179_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
return v___x_2180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType___boxed(lean_object* v_pu_2181_, lean_object* v_arg_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_){
_start:
{
uint8_t v_pu_boxed_2188_; lean_object* v_res_2189_; 
v_pu_boxed_2188_ = lean_unbox(v_pu_2181_);
v_res_2189_ = l_Lean_Compiler_LCNF_Arg_inferType(v_pu_boxed_2188_, v_arg_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_);
lean_dec(v_a_2186_);
lean_dec_ref(v_a_2185_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2183_);
return v_res_2189_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LetValue_inferType___closed__1(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2191_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2192_ = lean_unsigned_to_nat(15u);
v___x_2193_ = lean_unsigned_to_nat(268u);
v___x_2194_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_inferType___closed__0));
v___x_2195_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2196_ = l_mkPanicMessageWithDecl(v___x_2195_, v___x_2194_, v___x_2193_, v___x_2192_, v___x_2191_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(uint8_t v_pu_2197_, lean_object* v_e_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
if (v_pu_2197_ == 0)
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2205_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(v_e_2198_, v___x_2204_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
return v___x_2205_;
}
else
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_dec(v_e_2198_);
v___x_2206_ = lean_obj_once(&l_Lean_Compiler_LCNF_LetValue_inferType___closed__1, &l_Lean_Compiler_LCNF_LetValue_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_LetValue_inferType___closed__1);
v___x_2207_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2206_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
return v___x_2207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType___boxed(lean_object* v_pu_2208_, lean_object* v_e_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
uint8_t v_pu_boxed_2215_; lean_object* v_res_2216_; 
v_pu_boxed_2215_ = lean_unbox(v_pu_2208_);
v_res_2216_ = l_Lean_Compiler_LCNF_LetValue_inferType(v_pu_boxed_2215_, v_e_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
lean_dec(v_a_2213_);
lean_dec_ref(v_a_2212_);
lean_dec(v_a_2211_);
lean_dec_ref(v_a_2210_);
return v_res_2216_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_inferType___closed__1(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2218_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2219_ = lean_unsigned_to_nat(15u);
v___x_2220_ = lean_unsigned_to_nat(279u);
v___x_2221_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_inferType___closed__0));
v___x_2222_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2223_ = l_mkPanicMessageWithDecl(v___x_2222_, v___x_2221_, v___x_2220_, v___x_2219_, v___x_2218_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t v_pu_2224_, lean_object* v_code_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_){
_start:
{
if (v_pu_2224_ == 0)
{
switch(lean_obj_tag(v_code_2225_))
{
case 3:
{
lean_object* v_fvarId_2231_; lean_object* v_args_2232_; lean_object* v___x_2233_; 
v_fvarId_2231_ = lean_ctor_get(v_code_2225_, 0);
lean_inc(v_fvarId_2231_);
v_args_2232_ = lean_ctor_get(v_code_2225_, 1);
lean_inc_ref(v_args_2232_);
lean_dec_ref_known(v_code_2225_, 2);
v___x_2233_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2231_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v___x_2233_, 1);
v___x_2235_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2236_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2234_, v_args_2232_, v___x_2235_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
return v___x_2236_;
}
else
{
lean_dec_ref(v_args_2232_);
return v___x_2233_;
}
}
case 4:
{
lean_object* v_cases_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2245_; 
v_cases_2237_ = lean_ctor_get(v_code_2225_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_code_2225_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2239_ = v_code_2225_;
v_isShared_2240_ = v_isSharedCheck_2245_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_cases_2237_);
lean_dec(v_code_2225_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2245_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v_resultType_2241_; lean_object* v___x_2243_; 
v_resultType_2241_ = lean_ctor_get(v_cases_2237_, 1);
lean_inc_ref(v_resultType_2241_);
lean_dec_ref(v_cases_2237_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set_tag(v___x_2239_, 0);
lean_ctor_set(v___x_2239_, 0, v_resultType_2241_);
v___x_2243_ = v___x_2239_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_resultType_2241_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
case 5:
{
lean_object* v_fvarId_2246_; lean_object* v___x_2247_; 
v_fvarId_2246_ = lean_ctor_get(v_code_2225_, 0);
lean_inc(v_fvarId_2246_);
lean_dec_ref_known(v_code_2225_, 1);
v___x_2247_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2246_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
return v___x_2247_;
}
case 6:
{
lean_object* v_type_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
v_type_2248_ = lean_ctor_get(v_code_2225_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v_code_2225_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v_code_2225_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_type_2248_);
lean_dec(v_code_2225_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
lean_ctor_set_tag(v___x_2250_, 0);
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_type_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
default: 
{
lean_object* v_k_2256_; 
v_k_2256_ = lean_ctor_get(v_code_2225_, 1);
lean_inc_ref(v_k_2256_);
lean_dec_ref(v_code_2225_);
v_code_2225_ = v_k_2256_;
goto _start;
}
}
}
else
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
lean_dec_ref(v_code_2225_);
v___x_2258_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_inferType___closed__1, &l_Lean_Compiler_LCNF_Code_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_Code_inferType___closed__1);
v___x_2259_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2258_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
return v___x_2259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType___boxed(lean_object* v_pu_2260_, lean_object* v_code_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_){
_start:
{
uint8_t v_pu_boxed_2267_; lean_object* v_res_2268_; 
v_pu_boxed_2267_ = lean_unbox(v_pu_2260_);
v_res_2268_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_boxed_2267_, v_code_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
lean_dec(v_a_2263_);
lean_dec_ref(v_a_2262_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg(uint8_t v_pu_2269_, lean_object* v_code_2270_, lean_object* v_h__1_2271_, lean_object* v_h__2_2272_){
_start:
{
if (v_pu_2269_ == 0)
{
lean_object* v___x_2273_; 
lean_dec(v_h__2_2272_);
v___x_2273_ = lean_apply_1(v_h__1_2271_, v_code_2270_);
return v___x_2273_;
}
else
{
lean_object* v___x_2274_; 
lean_dec(v_h__1_2271_);
v___x_2274_ = lean_apply_1(v_h__2_2272_, v_code_2270_);
return v___x_2274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg___boxed(lean_object* v_pu_2275_, lean_object* v_code_2276_, lean_object* v_h__1_2277_, lean_object* v_h__2_2278_){
_start:
{
uint8_t v_pu_32__boxed_2279_; lean_object* v_res_2280_; 
v_pu_32__boxed_2279_ = lean_unbox(v_pu_2275_);
v_res_2280_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg(v_pu_32__boxed_2279_, v_code_2276_, v_h__1_2277_, v_h__2_2278_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter(lean_object* v_motive_2281_, uint8_t v_pu_2282_, lean_object* v_code_2283_, lean_object* v_h__1_2284_, lean_object* v_h__2_2285_){
_start:
{
if (v_pu_2282_ == 0)
{
lean_object* v___x_2286_; 
lean_dec(v_h__2_2285_);
v___x_2286_ = lean_apply_1(v_h__1_2284_, v_code_2283_);
return v___x_2286_;
}
else
{
lean_object* v___x_2287_; 
lean_dec(v_h__1_2284_);
v___x_2287_ = lean_apply_1(v_h__2_2285_, v_code_2283_);
return v___x_2287_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___boxed(lean_object* v_motive_2288_, lean_object* v_pu_2289_, lean_object* v_code_2290_, lean_object* v_h__1_2291_, lean_object* v_h__2_2292_){
_start:
{
uint8_t v_pu_39__boxed_2293_; lean_object* v_res_2294_; 
v_pu_39__boxed_2293_ = lean_unbox(v_pu_2289_);
v_res_2294_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter(v_motive_2288_, v_pu_39__boxed_2293_, v_code_2290_, v_h__1_2291_, v_h__2_2292_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__1_splitter___redArg(lean_object* v_code_2295_, lean_object* v_h__1_2296_, lean_object* v_h__2_2297_, lean_object* v_h__3_2298_, lean_object* v_h__4_2299_, lean_object* v_h__5_2300_, lean_object* v_h__6_2301_, lean_object* v_h__7_2302_){
_start:
{
switch(lean_obj_tag(v_code_2295_))
{
case 0:
{
lean_object* v_decl_2303_; lean_object* v_k_2304_; lean_object* v___x_2305_; 
lean_dec(v_h__7_2302_);
lean_dec(v_h__6_2301_);
lean_dec(v_h__5_2300_);
lean_dec(v_h__4_2299_);
lean_dec(v_h__3_2298_);
lean_dec(v_h__2_2297_);
v_decl_2303_ = lean_ctor_get(v_code_2295_, 0);
lean_inc_ref(v_decl_2303_);
v_k_2304_ = lean_ctor_get(v_code_2295_, 1);
lean_inc_ref(v_k_2304_);
lean_dec_ref_known(v_code_2295_, 2);
v___x_2305_ = lean_apply_2(v_h__1_2296_, v_decl_2303_, v_k_2304_);
return v___x_2305_;
}
case 1:
{
lean_object* v_decl_2306_; lean_object* v_k_2307_; lean_object* v___x_2308_; 
lean_dec(v_h__7_2302_);
lean_dec(v_h__6_2301_);
lean_dec(v_h__5_2300_);
lean_dec(v_h__4_2299_);
lean_dec(v_h__3_2298_);
lean_dec(v_h__1_2296_);
v_decl_2306_ = lean_ctor_get(v_code_2295_, 0);
lean_inc_ref(v_decl_2306_);
v_k_2307_ = lean_ctor_get(v_code_2295_, 1);
lean_inc_ref(v_k_2307_);
lean_dec_ref_known(v_code_2295_, 2);
v___x_2308_ = lean_apply_3(v_h__2_2297_, v_decl_2306_, v_k_2307_, lean_box(0));
return v___x_2308_;
}
case 2:
{
lean_object* v_decl_2309_; lean_object* v_k_2310_; lean_object* v___x_2311_; 
lean_dec(v_h__7_2302_);
lean_dec(v_h__6_2301_);
lean_dec(v_h__5_2300_);
lean_dec(v_h__4_2299_);
lean_dec(v_h__2_2297_);
lean_dec(v_h__1_2296_);
v_decl_2309_ = lean_ctor_get(v_code_2295_, 0);
lean_inc_ref(v_decl_2309_);
v_k_2310_ = lean_ctor_get(v_code_2295_, 1);
lean_inc_ref(v_k_2310_);
lean_dec_ref_known(v_code_2295_, 2);
v___x_2311_ = lean_apply_2(v_h__3_2298_, v_decl_2309_, v_k_2310_);
return v___x_2311_;
}
case 3:
{
lean_object* v_fvarId_2312_; lean_object* v_args_2313_; lean_object* v___x_2314_; 
lean_dec(v_h__7_2302_);
lean_dec(v_h__6_2301_);
lean_dec(v_h__4_2299_);
lean_dec(v_h__3_2298_);
lean_dec(v_h__2_2297_);
lean_dec(v_h__1_2296_);
v_fvarId_2312_ = lean_ctor_get(v_code_2295_, 0);
lean_inc(v_fvarId_2312_);
v_args_2313_ = lean_ctor_get(v_code_2295_, 1);
lean_inc_ref(v_args_2313_);
lean_dec_ref_known(v_code_2295_, 2);
v___x_2314_ = lean_apply_2(v_h__5_2300_, v_fvarId_2312_, v_args_2313_);
return v___x_2314_;
}
case 4:
{
lean_object* v_cases_2315_; lean_object* v___x_2316_; 
lean_dec(v_h__6_2301_);
lean_dec(v_h__5_2300_);
lean_dec(v_h__4_2299_);
lean_dec(v_h__3_2298_);
lean_dec(v_h__2_2297_);
lean_dec(v_h__1_2296_);
v_cases_2315_ = lean_ctor_get(v_code_2295_, 0);
lean_inc_ref(v_cases_2315_);
lean_dec_ref_known(v_code_2295_, 1);
v___x_2316_ = lean_apply_1(v_h__7_2302_, v_cases_2315_);
return v___x_2316_;
}
case 5:
{
lean_object* v_fvarId_2317_; lean_object* v___x_2318_; 
lean_dec(v_h__7_2302_);
lean_dec(v_h__6_2301_);
lean_dec(v_h__5_2300_);
lean_dec(v_h__3_2298_);
lean_dec(v_h__2_2297_);
lean_dec(v_h__1_2296_);
v_fvarId_2317_ = lean_ctor_get(v_code_2295_, 0);
lean_inc(v_fvarId_2317_);
lean_dec_ref_known(v_code_2295_, 1);
v___x_2318_ = lean_apply_1(v_h__4_2299_, v_fvarId_2317_);
return v___x_2318_;
}
default: 
{
lean_object* v_type_2319_; lean_object* v___x_2320_; 
lean_dec(v_h__7_2302_);
lean_dec(v_h__5_2300_);
lean_dec(v_h__4_2299_);
lean_dec(v_h__3_2298_);
lean_dec(v_h__2_2297_);
lean_dec(v_h__1_2296_);
v_type_2319_ = lean_ctor_get(v_code_2295_, 0);
lean_inc_ref(v_type_2319_);
lean_dec_ref_known(v_code_2295_, 1);
v___x_2320_ = lean_apply_1(v_h__6_2301_, v_type_2319_);
return v___x_2320_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__1_splitter(lean_object* v_motive_2321_, lean_object* v_code_2322_, lean_object* v_h__1_2323_, lean_object* v_h__2_2324_, lean_object* v_h__3_2325_, lean_object* v_h__4_2326_, lean_object* v_h__5_2327_, lean_object* v_h__6_2328_, lean_object* v_h__7_2329_){
_start:
{
switch(lean_obj_tag(v_code_2322_))
{
case 0:
{
lean_object* v_decl_2330_; lean_object* v_k_2331_; lean_object* v___x_2332_; 
lean_dec(v_h__7_2329_);
lean_dec(v_h__6_2328_);
lean_dec(v_h__5_2327_);
lean_dec(v_h__4_2326_);
lean_dec(v_h__3_2325_);
lean_dec(v_h__2_2324_);
v_decl_2330_ = lean_ctor_get(v_code_2322_, 0);
lean_inc_ref(v_decl_2330_);
v_k_2331_ = lean_ctor_get(v_code_2322_, 1);
lean_inc_ref(v_k_2331_);
lean_dec_ref_known(v_code_2322_, 2);
v___x_2332_ = lean_apply_2(v_h__1_2323_, v_decl_2330_, v_k_2331_);
return v___x_2332_;
}
case 1:
{
lean_object* v_decl_2333_; lean_object* v_k_2334_; lean_object* v___x_2335_; 
lean_dec(v_h__7_2329_);
lean_dec(v_h__6_2328_);
lean_dec(v_h__5_2327_);
lean_dec(v_h__4_2326_);
lean_dec(v_h__3_2325_);
lean_dec(v_h__1_2323_);
v_decl_2333_ = lean_ctor_get(v_code_2322_, 0);
lean_inc_ref(v_decl_2333_);
v_k_2334_ = lean_ctor_get(v_code_2322_, 1);
lean_inc_ref(v_k_2334_);
lean_dec_ref_known(v_code_2322_, 2);
v___x_2335_ = lean_apply_3(v_h__2_2324_, v_decl_2333_, v_k_2334_, lean_box(0));
return v___x_2335_;
}
case 2:
{
lean_object* v_decl_2336_; lean_object* v_k_2337_; lean_object* v___x_2338_; 
lean_dec(v_h__7_2329_);
lean_dec(v_h__6_2328_);
lean_dec(v_h__5_2327_);
lean_dec(v_h__4_2326_);
lean_dec(v_h__2_2324_);
lean_dec(v_h__1_2323_);
v_decl_2336_ = lean_ctor_get(v_code_2322_, 0);
lean_inc_ref(v_decl_2336_);
v_k_2337_ = lean_ctor_get(v_code_2322_, 1);
lean_inc_ref(v_k_2337_);
lean_dec_ref_known(v_code_2322_, 2);
v___x_2338_ = lean_apply_2(v_h__3_2325_, v_decl_2336_, v_k_2337_);
return v___x_2338_;
}
case 3:
{
lean_object* v_fvarId_2339_; lean_object* v_args_2340_; lean_object* v___x_2341_; 
lean_dec(v_h__7_2329_);
lean_dec(v_h__6_2328_);
lean_dec(v_h__4_2326_);
lean_dec(v_h__3_2325_);
lean_dec(v_h__2_2324_);
lean_dec(v_h__1_2323_);
v_fvarId_2339_ = lean_ctor_get(v_code_2322_, 0);
lean_inc(v_fvarId_2339_);
v_args_2340_ = lean_ctor_get(v_code_2322_, 1);
lean_inc_ref(v_args_2340_);
lean_dec_ref_known(v_code_2322_, 2);
v___x_2341_ = lean_apply_2(v_h__5_2327_, v_fvarId_2339_, v_args_2340_);
return v___x_2341_;
}
case 4:
{
lean_object* v_cases_2342_; lean_object* v___x_2343_; 
lean_dec(v_h__6_2328_);
lean_dec(v_h__5_2327_);
lean_dec(v_h__4_2326_);
lean_dec(v_h__3_2325_);
lean_dec(v_h__2_2324_);
lean_dec(v_h__1_2323_);
v_cases_2342_ = lean_ctor_get(v_code_2322_, 0);
lean_inc_ref(v_cases_2342_);
lean_dec_ref_known(v_code_2322_, 1);
v___x_2343_ = lean_apply_1(v_h__7_2329_, v_cases_2342_);
return v___x_2343_;
}
case 5:
{
lean_object* v_fvarId_2344_; lean_object* v___x_2345_; 
lean_dec(v_h__7_2329_);
lean_dec(v_h__6_2328_);
lean_dec(v_h__5_2327_);
lean_dec(v_h__3_2325_);
lean_dec(v_h__2_2324_);
lean_dec(v_h__1_2323_);
v_fvarId_2344_ = lean_ctor_get(v_code_2322_, 0);
lean_inc(v_fvarId_2344_);
lean_dec_ref_known(v_code_2322_, 1);
v___x_2345_ = lean_apply_1(v_h__4_2326_, v_fvarId_2344_);
return v___x_2345_;
}
default: 
{
lean_object* v_type_2346_; lean_object* v___x_2347_; 
lean_dec(v_h__7_2329_);
lean_dec(v_h__5_2327_);
lean_dec(v_h__4_2326_);
lean_dec(v_h__3_2325_);
lean_dec(v_h__2_2324_);
lean_dec(v_h__1_2323_);
v_type_2346_ = lean_ctor_get(v_code_2322_, 0);
lean_inc_ref(v_type_2346_);
lean_dec_ref_known(v_code_2322_, 1);
v___x_2347_ = lean_apply_1(v_h__6_2328_, v_type_2346_);
return v___x_2347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(uint8_t v_pu_2348_, lean_object* v_params_2349_, lean_object* v_code_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2348_, v_code_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; size_t v_sz_2358_; size_t v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_a_2357_);
lean_dec_ref_known(v___x_2356_, 1);
v_sz_2358_ = lean_array_size(v_params_2349_);
v___x_2359_ = ((size_t)0ULL);
v___x_2360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(v_sz_2358_, v___x_2359_, v_params_2349_);
v___x_2361_ = lean_unsigned_to_nat(32u);
v___x_2362_ = lean_mk_empty_array_with_capacity(v___x_2361_);
lean_dec_ref(v___x_2362_);
v___x_2363_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2364_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v___x_2360_, v_a_2357_, v___x_2363_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
lean_dec(v_a_2357_);
lean_dec_ref(v___x_2360_);
return v___x_2364_;
}
else
{
lean_dec_ref(v_params_2349_);
return v___x_2356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType___boxed(lean_object* v_pu_2365_, lean_object* v_params_2366_, lean_object* v_code_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
uint8_t v_pu_boxed_2373_; lean_object* v_res_2374_; 
v_pu_boxed_2373_ = lean_unbox(v_pu_2365_);
v_res_2374_ = l_Lean_Compiler_LCNF_Code_inferParamType(v_pu_boxed_2373_, v_params_2366_, v_code_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v_a_2371_);
lean_dec_ref(v_a_2370_);
lean_dec(v_a_2369_);
lean_dec_ref(v_a_2368_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType(uint8_t v_pu_2375_, lean_object* v_alt_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
switch(lean_obj_tag(v_alt_2376_))
{
case 0:
{
lean_object* v_code_2382_; lean_object* v___x_2383_; 
v_code_2382_ = lean_ctor_get(v_alt_2376_, 2);
lean_inc_ref(v_code_2382_);
lean_dec_ref_known(v_alt_2376_, 3);
v___x_2383_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2375_, v_code_2382_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
return v___x_2383_;
}
case 1:
{
lean_object* v_code_2384_; lean_object* v___x_2385_; 
v_code_2384_ = lean_ctor_get(v_alt_2376_, 1);
lean_inc_ref(v_code_2384_);
lean_dec_ref_known(v_alt_2376_, 2);
v___x_2385_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2375_, v_code_2384_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
return v___x_2385_;
}
default: 
{
lean_object* v_code_2386_; lean_object* v___x_2387_; 
v_code_2386_ = lean_ctor_get(v_alt_2376_, 0);
lean_inc_ref(v_code_2386_);
lean_dec_ref_known(v_alt_2376_, 1);
v___x_2387_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2375_, v_code_2386_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
return v___x_2387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType___boxed(lean_object* v_pu_2388_, lean_object* v_alt_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
uint8_t v_pu_boxed_2395_; lean_object* v_res_2396_; 
v_pu_boxed_2395_ = lean_unbox(v_pu_2388_);
v_res_2396_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_boxed_2395_, v_alt_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
lean_dec(v_a_2393_);
lean_dec_ref(v_a_2392_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t v_pu_2397_, lean_object* v_e_2398_, lean_object* v_prefixName_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_prefixName_2399_, v_a_2401_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2407_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
lean_dec_ref_known(v___x_2405_, 1);
lean_inc(v_e_2398_);
v___x_2407_ = l_Lean_Compiler_LCNF_LetValue_inferType(v_pu_2397_, v_e_2398_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2409_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2407_, 1);
v___x_2409_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2397_, v_a_2406_, v_a_2408_, v_e_2398_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
return v___x_2409_;
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec(v_a_2406_);
lean_dec(v_e_2398_);
v_a_2410_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2407_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2407_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
else
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
lean_dec(v_e_2398_);
v_a_2418_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2405_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2405_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl___boxed(lean_object* v_pu_2426_, lean_object* v_e_2427_, lean_object* v_prefixName_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
uint8_t v_pu_boxed_2434_; lean_object* v_res_2435_; 
v_pu_boxed_2434_ = lean_unbox(v_pu_2426_);
v_res_2435_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v_pu_boxed_2434_, v_e_2427_, v_prefixName_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
lean_dec(v_a_2430_);
lean_dec_ref(v_a_2429_);
return v_res_2435_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkForallParams___closed__1(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2437_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2438_ = lean_unsigned_to_nat(15u);
v___x_2439_ = lean_unsigned_to_nat(295u);
v___x_2440_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkForallParams___closed__0));
v___x_2441_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2442_ = l_mkPanicMessageWithDecl(v___x_2441_, v___x_2440_, v___x_2439_, v___x_2438_, v___x_2437_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams(uint8_t v_pu_2443_, lean_object* v_params_2444_, lean_object* v_type_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
if (v_pu_2443_ == 0)
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(v_params_2444_, v_type_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
return v___x_2451_;
}
else
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
lean_dec_ref(v_params_2444_);
v___x_2452_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkForallParams___closed__1, &l_Lean_Compiler_LCNF_mkForallParams___closed__1_once, _init_l_Lean_Compiler_LCNF_mkForallParams___closed__1);
v___x_2453_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2452_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
return v___x_2453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams___boxed(lean_object* v_pu_2454_, lean_object* v_params_2455_, lean_object* v_type_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
uint8_t v_pu_boxed_2462_; lean_object* v_res_2463_; 
v_pu_boxed_2462_ = lean_unbox(v_pu_2454_);
v_res_2463_ = l_Lean_Compiler_LCNF_mkForallParams(v_pu_boxed_2462_, v_params_2455_, v_type_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_);
lean_dec(v_a_2460_);
lean_dec_ref(v_a_2459_);
lean_dec(v_a_2458_);
lean_dec_ref(v_a_2457_);
lean_dec_ref(v_type_2456_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(uint8_t v_pu_2464_, lean_object* v_params_2465_, lean_object* v_code_2466_, lean_object* v_prefixName_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_){
_start:
{
lean_object* v___x_2473_; 
lean_inc_ref(v_code_2466_);
v___x_2473_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2464_, v_code_2466_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v___x_2475_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2474_);
lean_dec_ref_known(v___x_2473_, 1);
lean_inc_ref(v_params_2465_);
v___x_2475_ = l_Lean_Compiler_LCNF_mkForallParams(v_pu_2464_, v_params_2465_, v_a_2474_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_);
lean_dec(v_a_2474_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v___x_2477_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2476_);
lean_dec_ref_known(v___x_2475_, 1);
v___x_2477_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_prefixName_2467_, v_a_2469_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v___x_2479_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref_known(v___x_2477_, 1);
v___x_2479_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_2464_, v_a_2478_, v_a_2476_, v_params_2465_, v_code_2466_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_);
return v___x_2479_;
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
lean_dec(v_a_2476_);
lean_dec_ref(v_code_2466_);
lean_dec_ref(v_params_2465_);
v_a_2480_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2477_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2477_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
lean_dec(v_prefixName_2467_);
lean_dec_ref(v_code_2466_);
lean_dec_ref(v_params_2465_);
v_a_2488_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_2475_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2475_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_dec(v_prefixName_2467_);
lean_dec_ref(v_code_2466_);
lean_dec_ref(v_params_2465_);
v_a_2496_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2473_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2473_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux___boxed(lean_object* v_pu_2504_, lean_object* v_params_2505_, lean_object* v_code_2506_, lean_object* v_prefixName_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_){
_start:
{
uint8_t v_pu_boxed_2513_; lean_object* v_res_2514_; 
v_pu_boxed_2513_ = lean_unbox(v_pu_2504_);
v_res_2514_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_boxed_2513_, v_params_2505_, v_code_2506_, v_prefixName_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
lean_dec(v_a_2511_);
lean_dec_ref(v_a_2510_);
lean_dec(v_a_2509_);
lean_dec_ref(v_a_2508_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object* v_params_2515_, lean_object* v_code_2516_, lean_object* v_prefixName_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_){
_start:
{
uint8_t v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = 0;
v___x_2524_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v___x_2523_, v_params_2515_, v_code_2516_, v_prefixName_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl___boxed(lean_object* v_params_2525_, lean_object* v_code_2526_, lean_object* v_prefixName_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v_params_2525_, v_code_2526_, v_prefixName_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
lean_dec(v_a_2529_);
lean_dec_ref(v_a_2528_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(uint8_t v_pu_2534_, lean_object* v_params_2535_, lean_object* v_code_2536_, lean_object* v_prefixName_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v___x_2543_; 
v___x_2543_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_2534_, v_params_2535_, v_code_2536_, v_prefixName_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl___boxed(lean_object* v_pu_2544_, lean_object* v_params_2545_, lean_object* v_code_2546_, lean_object* v_prefixName_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
uint8_t v_pu_boxed_2553_; lean_object* v_res_2554_; 
v_pu_boxed_2553_ = lean_unbox(v_pu_2544_);
v_res_2554_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v_pu_boxed_2553_, v_params_2545_, v_code_2546_, v_prefixName_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(uint8_t v_pu_2555_, lean_object* v_param_2556_, lean_object* v_code_2557_, lean_object* v_prefixName_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v_params_2566_; lean_object* v___x_2567_; 
v___x_2564_ = lean_unsigned_to_nat(1u);
v___x_2565_ = lean_mk_empty_array_with_capacity(v___x_2564_);
v_params_2566_ = lean_array_push(v___x_2565_, v_param_2556_);
v___x_2567_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_2555_, v_params_2566_, v_code_2557_, v_prefixName_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___boxed(lean_object* v_pu_2568_, lean_object* v_param_2569_, lean_object* v_code_2570_, lean_object* v_prefixName_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
uint8_t v_pu_boxed_2577_; lean_object* v_res_2578_; 
v_pu_boxed_2577_ = lean_unbox(v_pu_2568_);
v_res_2578_ = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(v_pu_boxed_2577_, v_param_2569_, v_code_2570_, v_prefixName_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(lean_object* v_msg_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v_ref_2585_; lean_object* v___x_2586_; lean_object* v_env_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v_ref_2585_ = lean_ctor_get(v___y_2582_, 2);
v___x_2586_ = lean_st_ref_get(v___y_2583_);
v_env_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc_ref(v_env_2587_);
lean_dec(v___x_2586_);
v___x_2588_ = lean_st_ref_get(v___y_2581_);
v___x_2589_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_2580_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2612_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2592_ = v___x_2589_;
v_isShared_2593_ = v_isSharedCheck_2612_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2612_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v_lctx_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2610_; 
v_lctx_2594_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2610_ == 0)
{
lean_object* v_unused_2611_; 
v_unused_2611_ = lean_ctor_get(v___x_2588_, 1);
lean_dec(v_unused_2611_);
v___x_2596_ = v___x_2588_;
v_isShared_2597_ = v_isSharedCheck_2610_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_lctx_2594_);
lean_dec(v___x_2588_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2610_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
uint8_t v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2604_; 
v___x_2598_ = lean_unbox(v_a_2590_);
lean_dec(v_a_2590_);
v___x_2599_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2594_, v___x_2598_);
lean_dec_ref(v_lctx_2594_);
v___x_2600_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2582_);
v___x_2601_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1);
v___x_2602_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2602_, 0, v_env_2587_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
lean_ctor_set(v___x_2602_, 2, v___x_2599_);
lean_ctor_set(v___x_2602_, 3, v___x_2600_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set_tag(v___x_2596_, 3);
lean_ctor_set(v___x_2596_, 1, v_msg_2579_);
lean_ctor_set(v___x_2596_, 0, v___x_2602_);
v___x_2604_ = v___x_2596_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2602_);
lean_ctor_set(v_reuseFailAlloc_2609_, 1, v_msg_2579_);
v___x_2604_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
lean_object* v___x_2605_; lean_object* v___x_2607_; 
lean_inc(v_ref_2585_);
v___x_2605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2605_, 0, v_ref_2585_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set_tag(v___x_2592_, 1);
lean_ctor_set(v___x_2592_, 0, v___x_2605_);
v___x_2607_ = v___x_2592_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2605_);
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
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec(v___x_2588_);
lean_dec_ref(v_env_2587_);
lean_dec_ref(v_msg_2579_);
v_a_2613_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2589_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2589_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg___boxed(lean_object* v_msg_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v_msg_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1(lean_object* v_00_u03b1_2628_, lean_object* v_msg_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v_msg_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___boxed(lean_object* v_00_u03b1_2636_, lean_object* v_msg_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1(v_00_u03b1_2636_, v_msg_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(uint8_t v_pu_2644_, lean_object* v_a_2645_, lean_object* v_b_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v_array_2652_; lean_object* v_start_2653_; lean_object* v_stop_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2670_; 
v_array_2652_ = lean_ctor_get(v_a_2645_, 0);
v_start_2653_ = lean_ctor_get(v_a_2645_, 1);
v_stop_2654_ = lean_ctor_get(v_a_2645_, 2);
v_isSharedCheck_2670_ = !lean_is_exclusive(v_a_2645_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2656_ = v_a_2645_;
v_isShared_2657_ = v_isSharedCheck_2670_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_stop_2654_);
lean_inc(v_start_2653_);
lean_inc(v_array_2652_);
lean_dec(v_a_2645_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2670_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
uint8_t v___x_2658_; 
v___x_2658_ = lean_nat_dec_lt(v_start_2653_, v_stop_2654_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2659_; 
lean_del_object(v___x_2656_);
lean_dec(v_stop_2654_);
lean_dec(v_start_2653_);
lean_dec_ref(v_array_2652_);
v___x_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2659_, 0, v_b_2646_);
return v___x_2659_;
}
else
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2663_; 
v___x_2660_ = lean_unsigned_to_nat(1u);
v___x_2661_ = lean_nat_add(v_start_2653_, v___x_2660_);
lean_inc_ref(v_array_2652_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 1, v___x_2661_);
v___x_2663_ = v___x_2656_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_array_2652_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2669_, 2, v_stop_2654_);
v___x_2663_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = lean_array_fget(v_array_2652_, v_start_2653_);
lean_dec(v_start_2653_);
lean_dec_ref(v_array_2652_);
v___x_2665_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_2644_, v___x_2664_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v___x_2667_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
lean_dec_ref_known(v___x_2665_, 1);
v___x_2667_ = l_Lean_Compiler_LCNF_joinTypes(v_b_2646_, v_a_2666_);
v_a_2645_ = v___x_2663_;
v_b_2646_ = v___x_2667_;
goto _start;
}
else
{
lean_dec_ref(v___x_2663_);
lean_dec_ref(v_b_2646_);
return v___x_2665_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg___boxed(lean_object* v_pu_2671_, lean_object* v_a_2672_, lean_object* v_b_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
uint8_t v_pu_boxed_2679_; lean_object* v_res_2680_; 
v_pu_boxed_2679_ = lean_unbox(v_pu_2671_);
v_res_2680_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_boxed_2679_, v_a_2672_, v_b_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
return v_res_2680_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__0(void){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
return v___x_2681_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__2(void){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkCasesResultType___closed__1));
v___x_2684_ = l_Lean_stringToMessageData(v___x_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(uint8_t v_pu_2685_, lean_object* v_alts_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_){
_start:
{
lean_object* v___x_2692_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___x_2706_; lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2692_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkCasesResultType___closed__0, &l_Lean_Compiler_LCNF_mkCasesResultType___closed__0_once, _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__0);
v___x_2706_ = lean_array_get_size(v_alts_2686_);
v___x_2707_ = lean_unsigned_to_nat(0u);
v___x_2708_ = lean_nat_dec_eq(v___x_2706_, v___x_2707_);
if (v___x_2708_ == 0)
{
v___y_2694_ = v_a_2687_;
v___y_2695_ = v_a_2688_;
v___y_2696_ = v_a_2689_;
v___y_2697_ = v_a_2690_;
goto v___jp_2693_;
}
else
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec_ref(v_alts_2686_);
v___x_2709_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkCasesResultType___closed__2, &l_Lean_Compiler_LCNF_mkCasesResultType___closed__2_once, _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__2);
v___x_2710_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v___x_2709_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_);
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2710_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2710_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
v___jp_2693_:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2698_ = lean_unsigned_to_nat(0u);
v___x_2699_ = lean_array_get_borrowed(v___x_2692_, v_alts_2686_, v___x_2698_);
lean_inc(v___x_2699_);
v___x_2700_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_2685_, v___x_2699_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v_a_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
lean_inc(v_a_2701_);
lean_dec_ref_known(v___x_2700_, 1);
v___x_2702_ = lean_unsigned_to_nat(1u);
v___x_2703_ = lean_array_get_size(v_alts_2686_);
v___x_2704_ = l_Array_toSubarray___redArg(v_alts_2686_, v___x_2702_, v___x_2703_);
v___x_2705_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_2685_, v___x_2704_, v_a_2701_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
return v___x_2705_;
}
else
{
lean_dec_ref(v_alts_2686_);
return v___x_2700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___boxed(lean_object* v_pu_2719_, lean_object* v_alts_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_){
_start:
{
uint8_t v_pu_boxed_2726_; lean_object* v_res_2727_; 
v_pu_boxed_2726_ = lean_unbox(v_pu_2719_);
v_res_2727_ = l_Lean_Compiler_LCNF_mkCasesResultType(v_pu_boxed_2726_, v_alts_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_);
lean_dec(v_a_2724_);
lean_dec_ref(v_a_2723_);
lean_dec(v_a_2722_);
lean_dec_ref(v_a_2721_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0(uint8_t v_pu_2728_, lean_object* v_inst_2729_, lean_object* v_R_2730_, lean_object* v_a_2731_, lean_object* v_b_2732_, lean_object* v_c_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_2728_, v_a_2731_, v_b_2732_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___boxed(lean_object* v_pu_2740_, lean_object* v_inst_2741_, lean_object* v_R_2742_, lean_object* v_a_2743_, lean_object* v_b_2744_, lean_object* v_c_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
uint8_t v_pu_boxed_2751_; lean_object* v_res_2752_; 
v_pu_boxed_2751_ = lean_unbox(v_pu_2740_);
v_res_2752_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0(v_pu_boxed_2751_, v_inst_2741_, v_R_2742_, v_a_2743_, v_b_2744_, v_c_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(lean_object* v_msg_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v___x_2759_; lean_object* v_toApplicative_2760_; lean_object* v_toFunctor_2761_; lean_object* v_toSeq_2762_; lean_object* v_toSeqLeft_2763_; lean_object* v_toSeqRight_2764_; lean_object* v___f_2765_; lean_object* v___f_2766_; lean_object* v___f_2767_; lean_object* v___f_2768_; lean_object* v___x_2769_; lean_object* v___f_2770_; lean_object* v___f_2771_; lean_object* v___f_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___f_2779_; lean_object* v___x_970__overap_2780_; lean_object* v___x_2781_; 
v___x_2759_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_2760_ = lean_ctor_get(v___x_2759_, 0);
v_toFunctor_2761_ = lean_ctor_get(v_toApplicative_2760_, 0);
v_toSeq_2762_ = lean_ctor_get(v_toApplicative_2760_, 2);
v_toSeqLeft_2763_ = lean_ctor_get(v_toApplicative_2760_, 3);
v_toSeqRight_2764_ = lean_ctor_get(v_toApplicative_2760_, 4);
v___f_2765_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_2766_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2761_, 2);
v___f_2767_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2767_, 0, v_toFunctor_2761_);
v___f_2768_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2768_, 0, v_toFunctor_2761_);
v___x_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___f_2767_);
lean_ctor_set(v___x_2769_, 1, v___f_2768_);
lean_inc(v_toSeqRight_2764_);
v___f_2770_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2770_, 0, v_toSeqRight_2764_);
lean_inc(v_toSeqLeft_2763_);
v___f_2771_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2771_, 0, v_toSeqLeft_2763_);
lean_inc(v_toSeq_2762_);
v___f_2772_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2772_, 0, v_toSeq_2762_);
v___x_2773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2769_);
lean_ctor_set(v___x_2773_, 1, v___f_2765_);
lean_ctor_set(v___x_2773_, 2, v___f_2772_);
lean_ctor_set(v___x_2773_, 3, v___f_2771_);
lean_ctor_set(v___x_2773_, 4, v___f_2770_);
v___x_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
lean_ctor_set(v___x_2774_, 1, v___f_2766_);
v___x_2775_ = l_StateRefT_x27_instMonad___redArg(v___x_2774_);
v___x_2776_ = 0;
v___x_2777_ = lean_box(v___x_2776_);
v___x_2778_ = l_instInhabitedOfMonad___redArg(v___x_2775_, v___x_2777_);
v___f_2779_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2779_, 0, v___x_2778_);
v___x_970__overap_2780_ = lean_panic_fn_borrowed(v___f_2779_, v_msg_2753_);
lean_dec_ref(v___f_2779_);
lean_inc(v___y_2757_);
lean_inc_ref(v___y_2756_);
lean_inc(v___y_2755_);
lean_inc_ref(v___y_2754_);
v___x_2781_ = lean_apply_5(v___x_970__overap_2780_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, lean_box(0));
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0___boxed(lean_object* v_msg_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(v_msg_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
return v_res_2788_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1(void){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2790_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2));
v___x_2791_ = lean_unsigned_to_nat(50u);
v___x_2792_ = lean_unsigned_to_nat(345u);
v___x_2793_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__0));
v___x_2794_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2795_ = l_mkPanicMessageWithDecl(v___x_2794_, v___x_2793_, v___x_2792_, v___x_2791_, v___x_2790_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(lean_object* v_type_2796_, lean_object* v_predVars_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_t_2804_; lean_object* v_b_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v_type_2814_; 
v_type_2814_ = l_Lean_Expr_headBeta(v_type_2796_);
switch(lean_obj_tag(v_type_2814_))
{
case 0:
{
lean_object* v_deBruijnIndex_2815_; uint8_t v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v_deBruijnIndex_2815_ = lean_ctor_get(v_type_2814_, 0);
lean_inc(v_deBruijnIndex_2815_);
lean_dec_ref_known(v_type_2814_, 1);
v___x_2816_ = 0;
v___x_2817_ = lean_array_get_size(v_predVars_2797_);
v___x_2818_ = lean_nat_sub(v___x_2817_, v_deBruijnIndex_2815_);
lean_dec(v_deBruijnIndex_2815_);
v___x_2819_ = lean_unsigned_to_nat(1u);
v___x_2820_ = lean_nat_sub(v___x_2818_, v___x_2819_);
lean_dec(v___x_2818_);
v___x_2821_ = lean_box(v___x_2816_);
v___x_2822_ = lean_array_get(v___x_2821_, v_predVars_2797_, v___x_2820_);
lean_dec(v___x_2820_);
lean_dec_ref(v_predVars_2797_);
lean_dec(v___x_2821_);
v___x_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
return v___x_2823_;
}
case 1:
{
lean_object* v_fvarId_2824_; lean_object* v___x_2825_; 
lean_dec_ref(v_predVars_2797_);
v_fvarId_2824_ = lean_ctor_get(v_type_2814_, 0);
lean_inc(v_fvarId_2824_);
lean_dec_ref_known(v_type_2814_, 1);
v___x_2825_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2824_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2835_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2828_ = v___x_2825_;
v_isShared_2829_ = v_isSharedCheck_2835_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2825_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2835_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
uint8_t v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2833_; 
v___x_2830_ = l_Lean_Compiler_LCNF_isPredicateType(v_a_2826_);
v___x_2831_ = lean_box(v___x_2830_);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 0, v___x_2831_);
v___x_2833_ = v___x_2828_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2831_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
v_a_2836_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2825_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2825_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
}
case 3:
{
uint8_t v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
lean_dec_ref_known(v_type_2814_, 1);
lean_dec_ref(v_predVars_2797_);
v___x_2844_ = 0;
v___x_2845_ = lean_box(v___x_2844_);
v___x_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
return v___x_2846_;
}
case 4:
{
uint8_t v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
lean_dec_ref(v_predVars_2797_);
v___x_2847_ = l_Lean_Expr_isErased(v_type_2814_);
lean_dec_ref_known(v_type_2814_, 2);
v___x_2848_ = lean_box(v___x_2847_);
v___x_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
return v___x_2849_;
}
case 5:
{
lean_object* v_fn_2850_; 
v_fn_2850_ = lean_ctor_get(v_type_2814_, 0);
lean_inc_ref(v_fn_2850_);
lean_dec_ref_known(v_type_2814_, 2);
v_type_2796_ = v_fn_2850_;
goto _start;
}
case 6:
{
lean_object* v_binderType_2852_; lean_object* v_body_2853_; 
v_binderType_2852_ = lean_ctor_get(v_type_2814_, 1);
lean_inc_ref(v_binderType_2852_);
v_body_2853_ = lean_ctor_get(v_type_2814_, 2);
lean_inc_ref(v_body_2853_);
lean_dec_ref_known(v_type_2814_, 3);
v_t_2804_ = v_binderType_2852_;
v_b_2805_ = v_body_2853_;
v___y_2806_ = v_a_2798_;
v___y_2807_ = v_a_2799_;
v___y_2808_ = v_a_2800_;
v___y_2809_ = v_a_2801_;
goto v___jp_2803_;
}
case 7:
{
lean_object* v_binderType_2854_; lean_object* v_body_2855_; 
v_binderType_2854_ = lean_ctor_get(v_type_2814_, 1);
lean_inc_ref(v_binderType_2854_);
v_body_2855_ = lean_ctor_get(v_type_2814_, 2);
lean_inc_ref(v_body_2855_);
lean_dec_ref_known(v_type_2814_, 3);
v_t_2804_ = v_binderType_2854_;
v_b_2805_ = v_body_2855_;
v___y_2806_ = v_a_2798_;
v___y_2807_ = v_a_2799_;
v___y_2808_ = v_a_2800_;
v___y_2809_ = v_a_2801_;
goto v___jp_2803_;
}
case 10:
{
lean_object* v_expr_2856_; 
v_expr_2856_ = lean_ctor_get(v_type_2814_, 1);
lean_inc_ref(v_expr_2856_);
lean_dec_ref_known(v_type_2814_, 2);
v_type_2796_ = v_expr_2856_;
goto _start;
}
default: 
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
lean_dec_ref(v_type_2814_);
lean_dec_ref(v_predVars_2797_);
v___x_2858_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1, &l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1);
v___x_2859_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(v___x_2858_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_);
return v___x_2859_;
}
}
v___jp_2803_:
{
uint8_t v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2810_ = l_Lean_Compiler_LCNF_isPredicateType(v_t_2804_);
v___x_2811_ = lean_box(v___x_2810_);
v___x_2812_ = lean_array_push(v_predVars_2797_, v___x_2811_);
v_type_2796_ = v_b_2805_;
v_predVars_2797_ = v___x_2812_;
v_a_2798_ = v___y_2806_;
v_a_2799_ = v___y_2807_;
v_a_2800_ = v___y_2808_;
v_a_2801_ = v___y_2809_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___boxed(lean_object* v_type_2860_, lean_object* v_predVars_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(v_type_2860_, v_predVars_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_);
lean_dec(v_a_2865_);
lean_dec_ref(v_a_2864_);
lean_dec(v_a_2863_);
lean_dec_ref(v_a_2862_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible(lean_object* v_type_2868_, lean_object* v_predVars_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(v_type_2868_, v_predVars_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible___boxed(lean_object* v_type_2876_, lean_object* v_predVars_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_Lean_Compiler_LCNF_isErasedCompatible(v_type_2876_, v_predVars_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
lean_dec(v_a_2881_);
lean_dec_ref(v_a_2880_);
lean_dec(v_a_2879_);
lean_dec_ref(v_a_2878_);
return v_res_2883_;
}
}
LEAN_EXPORT uint8_t l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(lean_object* v_x_2884_, lean_object* v_x_2885_){
_start:
{
if (lean_obj_tag(v_x_2884_) == 0)
{
if (lean_obj_tag(v_x_2885_) == 0)
{
uint8_t v___x_2886_; 
v___x_2886_ = 1;
return v___x_2886_;
}
else
{
uint8_t v___x_2887_; 
v___x_2887_ = 0;
return v___x_2887_;
}
}
else
{
if (lean_obj_tag(v_x_2885_) == 0)
{
uint8_t v___x_2888_; 
v___x_2888_ = 0;
return v___x_2888_;
}
else
{
lean_object* v_head_2889_; lean_object* v_tail_2890_; lean_object* v_head_2891_; lean_object* v_tail_2892_; uint8_t v___x_2893_; 
v_head_2889_ = lean_ctor_get(v_x_2884_, 0);
v_tail_2890_ = lean_ctor_get(v_x_2884_, 1);
v_head_2891_ = lean_ctor_get(v_x_2885_, 0);
v_tail_2892_ = lean_ctor_get(v_x_2885_, 1);
v___x_2893_ = l_Lean_Level_isEquiv(v_head_2889_, v_head_2891_);
if (v___x_2893_ == 0)
{
return v___x_2893_;
}
else
{
v_x_2884_ = v_tail_2890_;
v_x_2885_ = v_tail_2892_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0___boxed(lean_object* v_x_2895_, lean_object* v_x_2896_){
_start:
{
uint8_t v_res_2897_; lean_object* v_r_2898_; 
v_res_2897_ = l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(v_x_2895_, v_x_2896_);
lean_dec(v_x_2896_);
lean_dec(v_x_2895_);
v_r_2898_ = lean_box(v_res_2897_);
return v_r_2898_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_eqvTypes(lean_object* v_a_2899_, lean_object* v_b_2900_){
_start:
{
uint8_t v___x_2901_; lean_object* v_d_u2081_2903_; lean_object* v_b_u2081_2904_; lean_object* v_d_u2082_2905_; lean_object* v_b_u2082_2906_; uint8_t v___y_2910_; uint8_t v___x_2955_; 
v___x_2901_ = lean_expr_eqv(v_a_2899_, v_b_2900_);
v___x_2955_ = 1;
if (v___x_2901_ == 0)
{
uint8_t v___x_2956_; 
v___x_2956_ = l_Lean_Expr_isErased(v_a_2899_);
if (v___x_2956_ == 0)
{
v___y_2910_ = v___x_2901_;
goto v___jp_2909_;
}
else
{
uint8_t v___x_2957_; 
v___x_2957_ = l_Lean_Expr_isErased(v_b_2900_);
if (v___x_2957_ == 0)
{
v___y_2910_ = v___x_2957_;
goto v___jp_2909_;
}
else
{
lean_dec_ref(v_b_2900_);
lean_dec_ref(v_a_2899_);
return v___x_2955_;
}
}
}
else
{
lean_dec_ref(v_b_2900_);
lean_dec_ref(v_a_2899_);
return v___x_2955_;
}
v___jp_2902_:
{
uint8_t v___x_2907_; 
v___x_2907_ = l_Lean_Compiler_LCNF_eqvTypes(v_d_u2081_2903_, v_d_u2082_2905_);
if (v___x_2907_ == 0)
{
lean_dec_ref(v_b_u2082_2906_);
lean_dec_ref(v_b_u2081_2904_);
return v___x_2901_;
}
else
{
v_a_2899_ = v_b_u2081_2904_;
v_b_2900_ = v_b_u2082_2906_;
goto _start;
}
}
v___jp_2909_:
{
lean_object* v_a_x27_2911_; lean_object* v_b_x27_2912_; uint8_t v___x_2913_; 
lean_inc_ref(v_a_2899_);
v_a_x27_2911_ = l_Lean_Expr_headBeta(v_a_2899_);
lean_inc_ref(v_b_2900_);
v_b_x27_2912_ = l_Lean_Expr_headBeta(v_b_2900_);
v___x_2913_ = lean_expr_eqv(v_a_2899_, v_a_x27_2911_);
if (v___x_2913_ == 0)
{
lean_dec_ref(v_b_2900_);
lean_dec_ref(v_a_2899_);
v_a_2899_ = v_a_x27_2911_;
v_b_2900_ = v_b_x27_2912_;
goto _start;
}
else
{
if (v___y_2910_ == 0)
{
uint8_t v___x_2915_; 
v___x_2915_ = lean_expr_eqv(v_b_2900_, v_b_x27_2912_);
if (v___x_2915_ == 0)
{
lean_dec_ref(v_b_2900_);
lean_dec_ref(v_a_2899_);
v_a_2899_ = v_a_x27_2911_;
v_b_2900_ = v_b_x27_2912_;
goto _start;
}
else
{
lean_dec_ref(v_b_x27_2912_);
lean_dec_ref(v_a_x27_2911_);
switch(lean_obj_tag(v_a_2899_))
{
case 10:
{
lean_object* v_expr_2917_; 
v_expr_2917_ = lean_ctor_get(v_a_2899_, 1);
lean_inc_ref(v_expr_2917_);
lean_dec_ref_known(v_a_2899_, 2);
v_a_2899_ = v_expr_2917_;
goto _start;
}
case 5:
{
switch(lean_obj_tag(v_b_2900_))
{
case 10:
{
lean_object* v_expr_2919_; 
v_expr_2919_ = lean_ctor_get(v_b_2900_, 1);
lean_inc_ref(v_expr_2919_);
lean_dec_ref_known(v_b_2900_, 2);
v_b_2900_ = v_expr_2919_;
goto _start;
}
case 5:
{
lean_object* v_fn_2921_; lean_object* v_arg_2922_; lean_object* v_fn_2923_; lean_object* v_arg_2924_; uint8_t v___x_2925_; 
v_fn_2921_ = lean_ctor_get(v_a_2899_, 0);
lean_inc_ref(v_fn_2921_);
v_arg_2922_ = lean_ctor_get(v_a_2899_, 1);
lean_inc_ref(v_arg_2922_);
lean_dec_ref_known(v_a_2899_, 2);
v_fn_2923_ = lean_ctor_get(v_b_2900_, 0);
lean_inc_ref(v_fn_2923_);
v_arg_2924_ = lean_ctor_get(v_b_2900_, 1);
lean_inc_ref(v_arg_2924_);
lean_dec_ref_known(v_b_2900_, 2);
v___x_2925_ = l_Lean_Compiler_LCNF_eqvTypes(v_fn_2921_, v_fn_2923_);
if (v___x_2925_ == 0)
{
lean_dec_ref(v_arg_2924_);
lean_dec_ref(v_arg_2922_);
return v___x_2901_;
}
else
{
v_a_2899_ = v_arg_2922_;
v_b_2900_ = v_arg_2924_;
goto _start;
}
}
default: 
{
lean_dec_ref_known(v_a_2899_, 2);
lean_dec_ref(v_b_2900_);
return v___y_2910_;
}
}
}
case 7:
{
switch(lean_obj_tag(v_b_2900_))
{
case 10:
{
lean_object* v_expr_2927_; 
v_expr_2927_ = lean_ctor_get(v_b_2900_, 1);
lean_inc_ref(v_expr_2927_);
lean_dec_ref_known(v_b_2900_, 2);
v_b_2900_ = v_expr_2927_;
goto _start;
}
case 7:
{
lean_object* v_binderType_2929_; lean_object* v_body_2930_; lean_object* v_binderType_2931_; lean_object* v_body_2932_; 
v_binderType_2929_ = lean_ctor_get(v_a_2899_, 1);
lean_inc_ref(v_binderType_2929_);
v_body_2930_ = lean_ctor_get(v_a_2899_, 2);
lean_inc_ref(v_body_2930_);
lean_dec_ref_known(v_a_2899_, 3);
v_binderType_2931_ = lean_ctor_get(v_b_2900_, 1);
lean_inc_ref(v_binderType_2931_);
v_body_2932_ = lean_ctor_get(v_b_2900_, 2);
lean_inc_ref(v_body_2932_);
lean_dec_ref_known(v_b_2900_, 3);
v_d_u2081_2903_ = v_binderType_2929_;
v_b_u2081_2904_ = v_body_2930_;
v_d_u2082_2905_ = v_binderType_2931_;
v_b_u2082_2906_ = v_body_2932_;
goto v___jp_2902_;
}
default: 
{
lean_dec_ref_known(v_a_2899_, 3);
lean_dec_ref(v_b_2900_);
return v___y_2910_;
}
}
}
case 6:
{
switch(lean_obj_tag(v_b_2900_))
{
case 10:
{
lean_object* v_expr_2933_; 
v_expr_2933_ = lean_ctor_get(v_b_2900_, 1);
lean_inc_ref(v_expr_2933_);
lean_dec_ref_known(v_b_2900_, 2);
v_b_2900_ = v_expr_2933_;
goto _start;
}
case 6:
{
lean_object* v_binderType_2935_; lean_object* v_body_2936_; lean_object* v_binderType_2937_; lean_object* v_body_2938_; 
v_binderType_2935_ = lean_ctor_get(v_a_2899_, 1);
lean_inc_ref(v_binderType_2935_);
v_body_2936_ = lean_ctor_get(v_a_2899_, 2);
lean_inc_ref(v_body_2936_);
lean_dec_ref_known(v_a_2899_, 3);
v_binderType_2937_ = lean_ctor_get(v_b_2900_, 1);
lean_inc_ref(v_binderType_2937_);
v_body_2938_ = lean_ctor_get(v_b_2900_, 2);
lean_inc_ref(v_body_2938_);
lean_dec_ref_known(v_b_2900_, 3);
v_d_u2081_2903_ = v_binderType_2935_;
v_b_u2081_2904_ = v_body_2936_;
v_d_u2082_2905_ = v_binderType_2937_;
v_b_u2082_2906_ = v_body_2938_;
goto v___jp_2902_;
}
default: 
{
lean_dec_ref_known(v_a_2899_, 3);
lean_dec_ref(v_b_2900_);
return v___y_2910_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_b_2900_))
{
case 10:
{
lean_object* v_expr_2939_; 
v_expr_2939_ = lean_ctor_get(v_b_2900_, 1);
lean_inc_ref(v_expr_2939_);
lean_dec_ref_known(v_b_2900_, 2);
v_b_2900_ = v_expr_2939_;
goto _start;
}
case 3:
{
lean_object* v_u_2941_; lean_object* v_u_2942_; uint8_t v___x_2943_; 
v_u_2941_ = lean_ctor_get(v_a_2899_, 0);
lean_inc(v_u_2941_);
lean_dec_ref_known(v_a_2899_, 1);
v_u_2942_ = lean_ctor_get(v_b_2900_, 0);
lean_inc(v_u_2942_);
lean_dec_ref_known(v_b_2900_, 1);
v___x_2943_ = l_Lean_Level_isEquiv(v_u_2941_, v_u_2942_);
lean_dec(v_u_2942_);
lean_dec(v_u_2941_);
return v___x_2943_;
}
default: 
{
lean_dec_ref_known(v_a_2899_, 1);
lean_dec_ref(v_b_2900_);
return v___y_2910_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_b_2900_))
{
case 10:
{
lean_object* v_expr_2944_; 
v_expr_2944_ = lean_ctor_get(v_b_2900_, 1);
lean_inc_ref(v_expr_2944_);
lean_dec_ref_known(v_b_2900_, 2);
v_b_2900_ = v_expr_2944_;
goto _start;
}
case 4:
{
lean_object* v_declName_2946_; lean_object* v_us_2947_; lean_object* v_declName_2948_; lean_object* v_us_2949_; uint8_t v___x_2950_; 
v_declName_2946_ = lean_ctor_get(v_a_2899_, 0);
lean_inc(v_declName_2946_);
v_us_2947_ = lean_ctor_get(v_a_2899_, 1);
lean_inc(v_us_2947_);
lean_dec_ref_known(v_a_2899_, 2);
v_declName_2948_ = lean_ctor_get(v_b_2900_, 0);
lean_inc(v_declName_2948_);
v_us_2949_ = lean_ctor_get(v_b_2900_, 1);
lean_inc(v_us_2949_);
lean_dec_ref_known(v_b_2900_, 2);
v___x_2950_ = lean_name_eq(v_declName_2946_, v_declName_2948_);
lean_dec(v_declName_2948_);
lean_dec(v_declName_2946_);
if (v___x_2950_ == 0)
{
lean_dec(v_us_2949_);
lean_dec(v_us_2947_);
return v___x_2901_;
}
else
{
uint8_t v___x_2951_; 
v___x_2951_ = l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(v_us_2947_, v_us_2949_);
lean_dec(v_us_2949_);
lean_dec(v_us_2947_);
return v___x_2951_;
}
}
default: 
{
lean_dec_ref_known(v_a_2899_, 2);
lean_dec_ref(v_b_2900_);
return v___y_2910_;
}
}
}
default: 
{
if (lean_obj_tag(v_b_2900_) == 10)
{
lean_object* v_expr_2952_; 
v_expr_2952_ = lean_ctor_get(v_b_2900_, 1);
lean_inc_ref(v_expr_2952_);
lean_dec_ref_known(v_b_2900_, 2);
v_b_2900_ = v_expr_2952_;
goto _start;
}
else
{
lean_dec_ref(v_b_2900_);
lean_dec_ref(v_a_2899_);
return v___y_2910_;
}
}
}
}
}
else
{
lean_dec_ref(v_b_2900_);
lean_dec_ref(v_a_2899_);
v_a_2899_ = v_a_x27_2911_;
v_b_2900_ = v_b_x27_2912_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eqvTypes___boxed(lean_object* v_a_2958_, lean_object* v_b_2959_){
_start:
{
uint8_t v_res_2960_; lean_object* v_r_2961_; 
v_res_2960_ = l_Lean_Compiler_LCNF_eqvTypes(v_a_2958_, v_b_2959_);
v_r_2961_ = lean_box(v_res_2960_);
return v_r_2961_;
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
