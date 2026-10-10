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
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getBinderName(lean_object* v_fvarId_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_){
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_InferType_Pure_getBinderName_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_Lean_Compiler_LCNF_InferType_Pure_getBinderName(v_fvarId_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getBinderName___boxed(lean_object* v_fvarId_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_Compiler_LCNF_InferType_Pure_getBinderName(v_fvarId_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_);
lean_dec(v_a_25_);
lean_dec_ref(v_a_24_);
lean_dec(v_a_23_);
lean_dec_ref(v_a_22_);
lean_dec_ref(v_a_21_);
return v_res_27_;
}
}
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getType(lean_object* v_fvarId_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v___x_35_; 
lean_inc(v_fvarId_28_);
lean_inc_ref(v_a_29_);
v___x_35_ = lean_local_ctx_find(v_a_29_, v_fvarId_28_);
if (lean_obj_tag(v___x_35_) == 0)
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Compiler_LCNF_getType(v_fvarId_28_, v_a_30_, v_a_31_, v_a_32_, v_a_33_);
return v___x_36_;
}
else
{
lean_object* v_val_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_45_; 
lean_dec(v_fvarId_28_);
v_val_37_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_45_ == 0)
{
v___x_39_ = v___x_35_;
v_isShared_40_ = v_isSharedCheck_45_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_val_37_);
lean_dec(v___x_35_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_45_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_41_; lean_object* v___x_43_; 
v___x_41_ = l_Lean_LocalDecl_type(v_val_37_);
lean_dec(v_val_37_);
if (v_isShared_40_ == 0)
{
lean_ctor_set_tag(v___x_39_, 0);
lean_ctor_set(v___x_39_, 0, v___x_41_);
v___x_43_ = v___x_39_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_41_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_InferType_Pure_getType_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_28_ = stack[0].m_obj;
lean_object* v_a_29_ = stack[1].m_obj;
lean_object* v_a_30_ = stack[2].m_obj;
lean_object* v_a_31_ = stack[3].m_obj;
lean_object* v_a_32_ = stack[4].m_obj;
lean_object* v_a_33_ = stack[5].m_obj;
lean_object* v_res_46_;
v_res_46_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_fvarId_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_);
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getType___boxed(lean_object* v_fvarId_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_fvarId_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec_ref(v_a_48_);
return v_res_54_;
}
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(lean_object* v_xs_55_, lean_object* v_i_56_, lean_object* v_a_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v_zero_64_; uint8_t v_isZero_65_; 
v_zero_64_ = lean_unsigned_to_nat(0u);
v_isZero_65_ = lean_nat_dec_eq(v_i_56_, v_zero_64_);
if (v_isZero_65_ == 1)
{
lean_object* v___x_66_; 
lean_dec(v_i_56_);
v___x_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_66_, 0, v_a_57_);
return v___x_66_;
}
else
{
lean_object* v_one_67_; lean_object* v_n_68_; lean_object* v_x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_one_67_ = lean_unsigned_to_nat(1u);
v_n_68_ = lean_nat_sub(v_i_56_, v_one_67_);
lean_dec(v_i_56_);
v_x_69_ = lean_array_fget_borrowed(v_xs_55_, v_n_68_);
v___x_70_ = l_Lean_Expr_fvarId_x21(v_x_69_);
lean_inc(v___x_70_);
v___x_71_ = l_Lean_Compiler_LCNF_InferType_Pure_getBinderName(v___x_70_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; lean_object* v___x_73_; 
v_a_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_a_72_);
lean_dec_ref_known(v___x_71_, 1);
v___x_73_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v___x_70_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_a_74_; lean_object* v___x_75_; uint8_t v___x_76_; lean_object* v___x_77_; 
v_a_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_a_74_);
lean_dec_ref_known(v___x_73_, 1);
v___x_75_ = lean_expr_abstract_range(v_a_74_, v_n_68_, v_xs_55_);
lean_dec(v_a_74_);
v___x_76_ = 0;
v___x_77_ = l_Lean_Expr_forallE___override(v_a_72_, v___x_75_, v_a_57_, v___x_76_);
v_i_56_ = v_n_68_;
v_a_57_ = v___x_77_;
goto _start;
}
else
{
lean_dec(v_a_72_);
lean_dec_ref(v_a_57_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_a_79_; 
v_a_79_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_a_79_);
lean_dec_ref_known(v___x_73_, 1);
v_i_56_ = v_n_68_;
v_a_57_ = v_a_79_;
goto _start;
}
else
{
lean_dec(v_n_68_);
return v___x_73_;
}
}
}
else
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
lean_dec(v___x_70_);
lean_dec(v_n_68_);
lean_dec_ref(v_a_57_);
v_a_81_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_88_ == 0)
{
v___x_83_ = v___x_71_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_71_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_81_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_55_ = stack[0].m_obj;
lean_object* v_i_56_ = stack[1].m_obj;
lean_object* v_a_57_ = stack[2].m_obj;
lean_object* v___y_58_ = stack[3].m_obj;
lean_object* v___y_59_ = stack[4].m_obj;
lean_object* v___y_60_ = stack[5].m_obj;
lean_object* v___y_61_ = stack[6].m_obj;
lean_object* v___y_62_ = stack[7].m_obj;
lean_object* v_res_89_;
v_res_89_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(v_xs_55_, v_i_56_, v_a_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_);
stack->m_obj
 = v_res_89_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg___boxed(lean_object* v_xs_90_, lean_object* v_i_91_, lean_object* v_a_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(v_xs_90_, v_i_91_, v_a_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec_ref(v_xs_90_);
return v_res_99_;
}
}
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(lean_object* v_xs_100_, lean_object* v_type_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v_b_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v_b_108_ = lean_expr_abstract(v_type_101_, v_xs_100_);
v___x_109_ = lean_array_get_size(v_xs_100_);
v___x_110_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(v_xs_100_, v___x_109_, v_b_108_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
return v___x_110_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_100_ = stack[0].m_obj;
lean_object* v_type_101_ = stack[1].m_obj;
lean_object* v_a_102_ = stack[2].m_obj;
lean_object* v_a_103_ = stack[3].m_obj;
lean_object* v_a_104_ = stack[4].m_obj;
lean_object* v_a_105_ = stack[5].m_obj;
lean_object* v_a_106_ = stack[6].m_obj;
lean_object* v_res_111_;
v_res_111_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v_xs_100_, v_type_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
stack->m_obj
 = v_res_111_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars___boxed(lean_object* v_xs_112_, lean_object* v_type_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v_xs_112_, v_type_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec_ref(v_type_113_);
lean_dec_ref(v_xs_112_);
return v_res_120_;
}
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0(lean_object* v_xs_121_, lean_object* v_n_122_, lean_object* v_i_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(v_xs_121_, v_i_123_, v_a_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
return v___x_132_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_121_ = stack[0].m_obj;
lean_object* v_n_122_ = stack[1].m_obj;
lean_object* v_i_123_ = stack[2].m_obj;
lean_object* v_a_125_ = stack[4].m_obj;
lean_object* v___y_126_ = stack[5].m_obj;
lean_object* v___y_127_ = stack[6].m_obj;
lean_object* v___y_128_ = stack[7].m_obj;
lean_object* v___y_129_ = stack[8].m_obj;
lean_object* v___y_130_ = stack[9].m_obj;
lean_object* v_res_133_;
v_res_133_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0(v_xs_121_, v_n_122_, v_i_123_, lean_box(0), v_a_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
stack->m_obj
 = v_res_133_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___boxed(lean_object* v_xs_134_, lean_object* v_n_135_, lean_object* v_i_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0(v_xs_134_, v_n_135_, v_i_136_, v_a_137_, v_a_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v_n_135_);
lean_dec_ref(v_xs_134_);
return v_res_145_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(size_t v_sz_146_, size_t v_i_147_, lean_object* v_bs_148_){
_start:
{
uint8_t v___x_149_; 
v___x_149_ = lean_usize_dec_lt(v_i_147_, v_sz_146_);
if (v___x_149_ == 0)
{
return v_bs_148_;
}
else
{
lean_object* v_v_150_; lean_object* v_fvarId_151_; lean_object* v___x_152_; lean_object* v_bs_x27_153_; lean_object* v___x_154_; size_t v___x_155_; size_t v___x_156_; lean_object* v___x_157_; 
v_v_150_ = lean_array_uget_borrowed(v_bs_148_, v_i_147_);
v_fvarId_151_ = lean_ctor_get(v_v_150_, 0);
lean_inc(v_fvarId_151_);
v___x_152_ = lean_unsigned_to_nat(0u);
v_bs_x27_153_ = lean_array_uset(v_bs_148_, v_i_147_, v___x_152_);
v___x_154_ = l_Lean_Expr_fvar___override(v_fvarId_151_);
v___x_155_ = ((size_t)1ULL);
v___x_156_ = lean_usize_add(v_i_147_, v___x_155_);
v___x_157_ = lean_array_uset(v_bs_x27_153_, v_i_147_, v___x_154_);
v_i_147_ = v___x_156_;
v_bs_148_ = v___x_157_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_146_ = stack[0].m_num;
size_t v_i_147_ = stack[1].m_num;
lean_object* v_bs_148_ = stack[2].m_obj;
lean_object* v_res_159_;
v_res_159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(v_sz_146_, v_i_147_, v_bs_148_);
stack->m_obj
 = v_res_159_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0___boxed(lean_object* v_sz_160_, lean_object* v_i_161_, lean_object* v_bs_162_){
_start:
{
size_t v_sz_boxed_163_; size_t v_i_boxed_164_; lean_object* v_res_165_; 
v_sz_boxed_163_ = lean_unbox_usize(v_sz_160_);
lean_dec(v_sz_160_);
v_i_boxed_164_ = lean_unbox_usize(v_i_161_);
lean_dec(v_i_161_);
v_res_165_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(v_sz_boxed_163_, v_i_boxed_164_, v_bs_162_);
return v_res_165_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0(void){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_166_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0);
v___x_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_unsigned_to_nat(32u);
v___x_170_ = lean_mk_empty_array_with_capacity(v___x_169_);
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3(void){
_start:
{
size_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_172_ = ((size_t)5ULL);
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = lean_unsigned_to_nat(32u);
v___x_175_ = lean_mk_empty_array_with_capacity(v___x_174_);
v___x_176_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2);
v___x_177_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___x_175_);
lean_ctor_set(v___x_177_, 2, v___x_173_);
lean_ctor_set(v___x_177_, 3, v___x_173_);
lean_ctor_set_usize(v___x_177_, 4, v___x_172_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_178_ = lean_box(1);
v___x_179_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3);
v___x_180_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1);
v___x_181_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___x_179_);
lean_ctor_set(v___x_181_, 2, v___x_178_);
return v___x_181_;
}
}
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(lean_object* v_params_182_, lean_object* v_type_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
size_t v_sz_189_; size_t v___x_190_; lean_object* v_xs_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_sz_189_ = lean_array_size(v_params_182_);
v___x_190_ = ((size_t)0ULL);
v_xs_191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(v_sz_189_, v___x_190_, v_params_182_);
v___x_192_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_193_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v_xs_191_, v_type_183_, v___x_192_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
lean_dec_ref(v_xs_191_);
return v___x_193_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_182_ = stack[0].m_obj;
lean_object* v_type_183_ = stack[1].m_obj;
lean_object* v_a_184_ = stack[2].m_obj;
lean_object* v_a_185_ = stack[3].m_obj;
lean_object* v_a_186_ = stack[4].m_obj;
lean_object* v_a_187_ = stack[5].m_obj;
lean_object* v_res_194_;
v_res_194_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(v_params_182_, v_type_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___boxed(lean_object* v_params_195_, lean_object* v_type_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(v_params_195_, v_type_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
lean_dec_ref(v_type_196_);
return v_res_202_;
}
}
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams(lean_object* v_params_203_, lean_object* v_type_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(v_params_203_, v_type_204_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
return v___x_211_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_203_ = stack[0].m_obj;
lean_object* v_type_204_ = stack[1].m_obj;
lean_object* v_a_205_ = stack[2].m_obj;
lean_object* v_a_206_ = stack[3].m_obj;
lean_object* v_a_207_ = stack[4].m_obj;
lean_object* v_a_208_ = stack[5].m_obj;
lean_object* v_a_209_ = stack[6].m_obj;
lean_object* v_res_212_;
v_res_212_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams(v_params_203_, v_type_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
stack->m_obj
 = v_res_212_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___boxed(lean_object* v_params_213_, lean_object* v_type_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams(v_params_213_, v_type_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec_ref(v_type_214_);
return v_res_221_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_instMonadEIO___redArg();
return v___x_222_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0);
v___x_224_ = l_StateRefT_x27_instMonad___redArg(v___x_223_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = l_Lean_Core_instMonadNameGeneratorCoreM;
v___x_232_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__7));
v___x_233_ = l_Lean_monadNameGeneratorLift___redArg(v___x_232_, v___x_231_);
return v___x_233_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9(void){
_start:
{
lean_object* v___x_234_; lean_object* v___f_235_; lean_object* v___x_236_; 
v___x_234_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8);
v___f_235_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__6));
v___x_236_ = l_Lean_monadNameGeneratorLift___redArg(v___f_235_, v___x_234_);
return v___x_236_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10(void){
_start:
{
lean_object* v___x_237_; lean_object* v___f_238_; lean_object* v___x_239_; 
v___x_237_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9);
v___f_238_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__6));
v___x_239_ = l_Lean_monadNameGeneratorLift___redArg(v___f_238_, v___x_237_);
return v___x_239_;
}
}
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg(lean_object* v_binderName_240_, lean_object* v_type_241_, uint8_t v_binderInfo_242_, lean_object* v_k_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v___x_250_; lean_object* v_toApplicative_251_; lean_object* v_toFunctor_252_; lean_object* v_toSeq_253_; lean_object* v_toSeqLeft_254_; lean_object* v_toSeqRight_255_; lean_object* v___f_256_; lean_object* v___f_257_; lean_object* v___f_258_; lean_object* v___f_259_; lean_object* v___x_260_; lean_object* v___f_261_; lean_object* v___f_262_; lean_object* v___f_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v_toApplicative_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_311_; 
v___x_250_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_251_ = lean_ctor_get(v___x_250_, 0);
v_toFunctor_252_ = lean_ctor_get(v_toApplicative_251_, 0);
v_toSeq_253_ = lean_ctor_get(v_toApplicative_251_, 2);
v_toSeqLeft_254_ = lean_ctor_get(v_toApplicative_251_, 3);
v_toSeqRight_255_ = lean_ctor_get(v_toApplicative_251_, 4);
v___f_256_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_257_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_252_, 2);
v___f_258_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_258_, 0, v_toFunctor_252_);
v___f_259_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_259_, 0, v_toFunctor_252_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___f_258_);
lean_ctor_set(v___x_260_, 1, v___f_259_);
lean_inc(v_toSeqRight_255_);
v___f_261_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_261_, 0, v_toSeqRight_255_);
lean_inc(v_toSeqLeft_254_);
v___f_262_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_262_, 0, v_toSeqLeft_254_);
lean_inc(v_toSeq_253_);
v___f_263_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_263_, 0, v_toSeq_253_);
v___x_264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_264_, 0, v___x_260_);
lean_ctor_set(v___x_264_, 1, v___f_256_);
lean_ctor_set(v___x_264_, 2, v___f_263_);
lean_ctor_set(v___x_264_, 3, v___f_262_);
lean_ctor_set(v___x_264_, 4, v___f_261_);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v___f_257_);
v___x_266_ = l_StateRefT_x27_instMonad___redArg(v___x_265_);
v_toApplicative_267_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; 
v_unused_312_ = lean_ctor_get(v___x_266_, 1);
lean_dec(v_unused_312_);
v___x_269_ = v___x_266_;
v_isShared_270_ = v_isSharedCheck_311_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_toApplicative_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_311_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v_toFunctor_271_; lean_object* v_toSeq_272_; lean_object* v_toSeqLeft_273_; lean_object* v_toSeqRight_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_309_; 
v_toFunctor_271_ = lean_ctor_get(v_toApplicative_267_, 0);
v_toSeq_272_ = lean_ctor_get(v_toApplicative_267_, 2);
v_toSeqLeft_273_ = lean_ctor_get(v_toApplicative_267_, 3);
v_toSeqRight_274_ = lean_ctor_get(v_toApplicative_267_, 4);
v_isSharedCheck_309_ = !lean_is_exclusive(v_toApplicative_267_);
if (v_isSharedCheck_309_ == 0)
{
lean_object* v_unused_310_; 
v_unused_310_ = lean_ctor_get(v_toApplicative_267_, 1);
lean_dec(v_unused_310_);
v___x_276_ = v_toApplicative_267_;
v_isShared_277_ = v_isSharedCheck_309_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_toSeqRight_274_);
lean_inc(v_toSeqLeft_273_);
lean_inc(v_toSeq_272_);
lean_inc(v_toFunctor_271_);
lean_dec(v_toApplicative_267_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_309_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___f_278_; lean_object* v___f_279_; lean_object* v___f_280_; lean_object* v___f_281_; lean_object* v___x_282_; lean_object* v___f_283_; lean_object* v___f_284_; lean_object* v___f_285_; lean_object* v___x_287_; 
v___f_278_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__4));
v___f_279_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__5));
lean_inc_ref(v_toFunctor_271_);
v___f_280_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_280_, 0, v_toFunctor_271_);
v___f_281_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_281_, 0, v_toFunctor_271_);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v___f_280_);
lean_ctor_set(v___x_282_, 1, v___f_281_);
v___f_283_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_283_, 0, v_toSeqRight_274_);
v___f_284_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_284_, 0, v_toSeqLeft_273_);
v___f_285_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_285_, 0, v_toSeq_272_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 4, v___f_283_);
lean_ctor_set(v___x_276_, 3, v___f_284_);
lean_ctor_set(v___x_276_, 2, v___f_285_);
lean_ctor_set(v___x_276_, 1, v___f_278_);
lean_ctor_set(v___x_276_, 0, v___x_282_);
v___x_287_ = v___x_276_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v___f_278_);
lean_ctor_set(v_reuseFailAlloc_308_, 2, v___f_285_);
lean_ctor_set(v_reuseFailAlloc_308_, 3, v___f_284_);
lean_ctor_set(v_reuseFailAlloc_308_, 4, v___f_283_);
v___x_287_ = v_reuseFailAlloc_308_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_289_; 
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v___f_279_);
lean_ctor_set(v___x_269_, 0, v___x_287_);
v___x_289_ = v___x_269_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v___f_279_);
v___x_289_ = v_reuseFailAlloc_307_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_198__overap_292_; lean_object* v___x_293_; 
v___x_290_ = l_ReaderT_instMonad___redArg(v___x_289_);
v___x_291_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10);
v___x_198__overap_292_ = l_Lean_mkFreshFVarId___redArg(v___x_290_, v___x_291_);
lean_inc(v_a_248_);
lean_inc_ref(v_a_247_);
lean_inc(v_a_246_);
lean_inc_ref(v_a_245_);
lean_inc_ref(v_a_244_);
v___x_293_ = lean_apply_6(v___x_198__overap_292_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, lean_box(0));
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_295_; uint8_t v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc_n(v_a_294_, 2);
lean_dec_ref_known(v___x_293_, 1);
v___x_295_ = l_Lean_Expr_fvar___override(v_a_294_);
v___x_296_ = 0;
lean_inc_ref(v_a_244_);
v___x_297_ = l_Lean_LocalContext_mkLocalDecl(v_a_244_, v_a_294_, v_binderName_240_, v_type_241_, v_binderInfo_242_, v___x_296_);
lean_inc(v_a_248_);
lean_inc_ref(v_a_247_);
lean_inc(v_a_246_);
lean_inc_ref(v_a_245_);
v___x_298_ = lean_apply_7(v_k_243_, v___x_295_, v___x_297_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, lean_box(0));
return v___x_298_;
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_dec_ref(v_k_243_);
lean_dec_ref(v_type_241_);
lean_dec(v_binderName_240_);
v_a_299_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_293_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_293_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderName_240_ = stack[0].m_obj;
lean_object* v_type_241_ = stack[1].m_obj;
uint8_t v_binderInfo_242_ = stack[2].m_num;
lean_object* v_k_243_ = stack[3].m_obj;
lean_object* v_a_244_ = stack[4].m_obj;
lean_object* v_a_245_ = stack[5].m_obj;
lean_object* v_a_246_ = stack[6].m_obj;
lean_object* v_a_247_ = stack[7].m_obj;
lean_object* v_a_248_ = stack[8].m_obj;
lean_object* v_res_313_;
v_res_313_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg(v_binderName_240_, v_type_241_, v_binderInfo_242_, v_k_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_);
stack->m_obj
 = v_res_313_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___boxed(lean_object* v_binderName_314_, lean_object* v_type_315_, lean_object* v_binderInfo_316_, lean_object* v_k_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
uint8_t v_binderInfo_boxed_324_; lean_object* v_res_325_; 
v_binderInfo_boxed_324_ = lean_unbox(v_binderInfo_316_);
v_res_325_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg(v_binderName_314_, v_type_315_, v_binderInfo_boxed_324_, v_k_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec_ref(v_a_318_);
return v_res_325_;
}
}
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl(lean_object* v_00_u03b1_326_, lean_object* v_binderName_327_, lean_object* v_type_328_, uint8_t v_binderInfo_329_, lean_object* v_k_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___x_337_; lean_object* v_toApplicative_338_; lean_object* v_toFunctor_339_; lean_object* v_toSeq_340_; lean_object* v_toSeqLeft_341_; lean_object* v_toSeqRight_342_; lean_object* v___f_343_; lean_object* v___f_344_; lean_object* v___f_345_; lean_object* v___f_346_; lean_object* v___x_347_; lean_object* v___f_348_; lean_object* v___f_349_; lean_object* v___f_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v_toApplicative_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_398_; 
v___x_337_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_338_ = lean_ctor_get(v___x_337_, 0);
v_toFunctor_339_ = lean_ctor_get(v_toApplicative_338_, 0);
v_toSeq_340_ = lean_ctor_get(v_toApplicative_338_, 2);
v_toSeqLeft_341_ = lean_ctor_get(v_toApplicative_338_, 3);
v_toSeqRight_342_ = lean_ctor_get(v_toApplicative_338_, 4);
v___f_343_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_344_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_339_, 2);
v___f_345_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_345_, 0, v_toFunctor_339_);
v___f_346_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_346_, 0, v_toFunctor_339_);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v___f_345_);
lean_ctor_set(v___x_347_, 1, v___f_346_);
lean_inc(v_toSeqRight_342_);
v___f_348_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_348_, 0, v_toSeqRight_342_);
lean_inc(v_toSeqLeft_341_);
v___f_349_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_349_, 0, v_toSeqLeft_341_);
lean_inc(v_toSeq_340_);
v___f_350_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_350_, 0, v_toSeq_340_);
v___x_351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_351_, 0, v___x_347_);
lean_ctor_set(v___x_351_, 1, v___f_343_);
lean_ctor_set(v___x_351_, 2, v___f_350_);
lean_ctor_set(v___x_351_, 3, v___f_349_);
lean_ctor_set(v___x_351_, 4, v___f_348_);
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
lean_ctor_set(v___x_352_, 1, v___f_344_);
v___x_353_ = l_StateRefT_x27_instMonad___redArg(v___x_352_);
v_toApplicative_354_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_398_ == 0)
{
lean_object* v_unused_399_; 
v_unused_399_ = lean_ctor_get(v___x_353_, 1);
lean_dec(v_unused_399_);
v___x_356_ = v___x_353_;
v_isShared_357_ = v_isSharedCheck_398_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_toApplicative_354_);
lean_dec(v___x_353_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_398_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v_toFunctor_358_; lean_object* v_toSeq_359_; lean_object* v_toSeqLeft_360_; lean_object* v_toSeqRight_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_396_; 
v_toFunctor_358_ = lean_ctor_get(v_toApplicative_354_, 0);
v_toSeq_359_ = lean_ctor_get(v_toApplicative_354_, 2);
v_toSeqLeft_360_ = lean_ctor_get(v_toApplicative_354_, 3);
v_toSeqRight_361_ = lean_ctor_get(v_toApplicative_354_, 4);
v_isSharedCheck_396_ = !lean_is_exclusive(v_toApplicative_354_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; 
v_unused_397_ = lean_ctor_get(v_toApplicative_354_, 1);
lean_dec(v_unused_397_);
v___x_363_ = v_toApplicative_354_;
v_isShared_364_ = v_isSharedCheck_396_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_toSeqRight_361_);
lean_inc(v_toSeqLeft_360_);
lean_inc(v_toSeq_359_);
lean_inc(v_toFunctor_358_);
lean_dec(v_toApplicative_354_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_396_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___f_365_; lean_object* v___f_366_; lean_object* v___f_367_; lean_object* v___f_368_; lean_object* v___x_369_; lean_object* v___f_370_; lean_object* v___f_371_; lean_object* v___f_372_; lean_object* v___x_374_; 
v___f_365_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__4));
v___f_366_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__5));
lean_inc_ref(v_toFunctor_358_);
v___f_367_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_367_, 0, v_toFunctor_358_);
v___f_368_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_368_, 0, v_toFunctor_358_);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v___f_367_);
lean_ctor_set(v___x_369_, 1, v___f_368_);
v___f_370_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_370_, 0, v_toSeqRight_361_);
v___f_371_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_371_, 0, v_toSeqLeft_360_);
v___f_372_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_372_, 0, v_toSeq_359_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 4, v___f_370_);
lean_ctor_set(v___x_363_, 3, v___f_371_);
lean_ctor_set(v___x_363_, 2, v___f_372_);
lean_ctor_set(v___x_363_, 1, v___f_365_);
lean_ctor_set(v___x_363_, 0, v___x_369_);
v___x_374_ = v___x_363_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v___f_365_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v___f_372_);
lean_ctor_set(v_reuseFailAlloc_395_, 3, v___f_371_);
lean_ctor_set(v_reuseFailAlloc_395_, 4, v___f_370_);
v___x_374_ = v_reuseFailAlloc_395_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_376_; 
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 1, v___f_366_);
lean_ctor_set(v___x_356_, 0, v___x_374_);
v___x_376_ = v___x_356_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v___f_366_);
v___x_376_ = v_reuseFailAlloc_394_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_232__overap_379_; lean_object* v___x_380_; 
v___x_377_ = l_ReaderT_instMonad___redArg(v___x_376_);
v___x_378_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10);
v___x_232__overap_379_ = l_Lean_mkFreshFVarId___redArg(v___x_377_, v___x_378_);
lean_inc(v_a_335_);
lean_inc_ref(v_a_334_);
lean_inc(v_a_333_);
lean_inc_ref(v_a_332_);
lean_inc_ref(v_a_331_);
v___x_380_ = lean_apply_6(v___x_232__overap_379_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, lean_box(0));
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_382_; uint8_t v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc_n(v_a_381_, 2);
lean_dec_ref_known(v___x_380_, 1);
v___x_382_ = l_Lean_Expr_fvar___override(v_a_381_);
v___x_383_ = 0;
lean_inc_ref(v_a_331_);
v___x_384_ = l_Lean_LocalContext_mkLocalDecl(v_a_331_, v_a_381_, v_binderName_327_, v_type_328_, v_binderInfo_329_, v___x_383_);
lean_inc(v_a_335_);
lean_inc_ref(v_a_334_);
lean_inc(v_a_333_);
lean_inc_ref(v_a_332_);
v___x_385_ = lean_apply_7(v_k_330_, v___x_382_, v___x_384_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, lean_box(0));
return v___x_385_;
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_dec_ref(v_k_330_);
lean_dec_ref(v_type_328_);
lean_dec(v_binderName_327_);
v_a_386_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_380_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_380_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderName_327_ = stack[1].m_obj;
lean_object* v_type_328_ = stack[2].m_obj;
uint8_t v_binderInfo_329_ = stack[3].m_num;
lean_object* v_k_330_ = stack[4].m_obj;
lean_object* v_a_331_ = stack[5].m_obj;
lean_object* v_a_332_ = stack[6].m_obj;
lean_object* v_a_333_ = stack[7].m_obj;
lean_object* v_a_334_ = stack[8].m_obj;
lean_object* v_a_335_ = stack[9].m_obj;
lean_object* v_res_400_;
v_res_400_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl(lean_box(0), v_binderName_327_, v_type_328_, v_binderInfo_329_, v_k_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
stack->m_obj
 = v_res_400_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___boxed(lean_object* v_00_u03b1_401_, lean_object* v_binderName_402_, lean_object* v_type_403_, lean_object* v_binderInfo_404_, lean_object* v_k_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
uint8_t v_binderInfo_boxed_412_; lean_object* v_res_413_; 
v_binderInfo_boxed_412_ = lean_unbox(v_binderInfo_404_);
v_res_413_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl(v_00_u03b1_401_, v_binderName_402_, v_type_403_, v_binderInfo_boxed_412_, v_k_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec_ref(v_a_406_);
return v_res_413_;
}
}
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(lean_object* v_declName_417_, lean_object* v_us_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__1));
v___x_425_ = lean_name_eq(v_declName_417_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_419_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; uint8_t v___x_428_; lean_object* v___x_429_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v___x_426_, 1);
v___x_428_ = lean_unbox(v_a_427_);
lean_dec(v_a_427_);
lean_inc(v_declName_417_);
v___x_429_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_417_, v___x_428_, v_a_421_, v_a_422_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_440_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_440_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_440_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_440_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
if (lean_obj_tag(v_a_430_) == 1)
{
lean_object* v_val_434_; lean_object* v___x_435_; lean_object* v___x_437_; 
lean_dec(v_declName_417_);
v_val_434_ = lean_ctor_get(v_a_430_, 0);
lean_inc(v_val_434_);
lean_dec_ref_known(v_a_430_, 1);
v___x_435_ = l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg(v_val_434_, v_us_418_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_435_);
v___x_437_ = v___x_432_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
else
{
lean_object* v___x_439_; 
lean_del_object(v___x_432_);
lean_dec(v_a_430_);
v___x_439_ = l_Lean_Compiler_LCNF_getOtherDeclType(v_declName_417_, v_us_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
return v___x_439_;
}
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
lean_dec(v_us_418_);
lean_dec(v_declName_417_);
v_a_441_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_429_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_429_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
lean_dec(v_us_418_);
lean_dec(v_declName_417_);
v_a_449_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_426_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_426_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec(v_us_418_);
lean_dec(v_declName_417_);
v___x_457_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
return v___x_458_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_InferType_Pure_inferConstType_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_417_ = stack[0].m_obj;
lean_object* v_us_418_ = stack[1].m_obj;
lean_object* v_a_419_ = stack[2].m_obj;
lean_object* v_a_420_ = stack[3].m_obj;
lean_object* v_a_421_ = stack[4].m_obj;
lean_object* v_a_422_ = stack[5].m_obj;
lean_object* v_res_459_;
v_res_459_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(v_declName_417_, v_us_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
stack->m_obj
 = v_res_459_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___boxed(lean_object* v_declName_460_, lean_object* v_us_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(v_declName_460_, v_us_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
return v_res_467_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = lean_box(0);
v___x_472_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__1));
v___x_473_ = l_Lean_mkConst(v___x_472_, v___x_471_);
return v___x_473_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = lean_box(0);
v___x_478_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__4));
v___x_479_ = l_Lean_mkConst(v___x_478_, v___x_477_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = lean_box(0);
v___x_484_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__7));
v___x_485_ = l_Lean_mkConst(v___x_484_, v___x_483_);
return v___x_485_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_box(0);
v___x_490_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__10));
v___x_491_ = l_Lean_mkConst(v___x_490_, v___x_489_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = lean_box(0);
v___x_496_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__13));
v___x_497_ = l_Lean_mkConst(v___x_496_, v___x_495_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_box(0);
v___x_502_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__16));
v___x_503_ = l_Lean_mkConst(v___x_502_, v___x_501_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_box(0);
v___x_508_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__19));
v___x_509_ = l_Lean_mkConst(v___x_508_, v___x_507_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType(lean_object* v_value_510_){
_start:
{
switch(lean_obj_tag(v_value_510_))
{
case 0:
{
lean_object* v___x_511_; 
v___x_511_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2);
return v___x_511_;
}
case 1:
{
lean_object* v___x_512_; 
v___x_512_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5);
return v___x_512_;
}
case 2:
{
lean_object* v___x_513_; 
v___x_513_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8);
return v___x_513_;
}
case 3:
{
lean_object* v___x_514_; 
v___x_514_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11);
return v___x_514_;
}
case 4:
{
lean_object* v___x_515_; 
v___x_515_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14);
return v___x_515_;
}
case 5:
{
lean_object* v___x_516_; 
v___x_516_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17);
return v___x_516_;
}
default: 
{
lean_object* v___x_517_; 
v___x_517_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20);
return v___x_517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___boxed(lean_object* v_value_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType(v_value_518_);
lean_dec_ref(v_value_518_);
return v_res_519_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(lean_object* v___y_520_){
_start:
{
lean_object* v___x_522_; lean_object* v_ngen_523_; lean_object* v_namePrefix_524_; lean_object* v_idx_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_555_; 
v___x_522_ = lean_st_ref_get(v___y_520_);
v_ngen_523_ = lean_ctor_get(v___x_522_, 2);
lean_inc_ref(v_ngen_523_);
lean_dec(v___x_522_);
v_namePrefix_524_ = lean_ctor_get(v_ngen_523_, 0);
v_idx_525_ = lean_ctor_get(v_ngen_523_, 1);
v_isSharedCheck_555_ = !lean_is_exclusive(v_ngen_523_);
if (v_isSharedCheck_555_ == 0)
{
v___x_527_ = v_ngen_523_;
v_isShared_528_ = v_isSharedCheck_555_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_idx_525_);
lean_inc(v_namePrefix_524_);
lean_dec(v_ngen_523_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_555_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v_r_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_533_; 
lean_inc(v_idx_525_);
lean_inc(v_namePrefix_524_);
v_r_529_ = l_Lean_Name_num___override(v_namePrefix_524_, v_idx_525_);
v___x_530_ = lean_unsigned_to_nat(1u);
v___x_531_ = lean_nat_add(v_idx_525_, v___x_530_);
lean_dec(v_idx_525_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 1, v___x_531_);
v___x_533_ = v___x_527_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_namePrefix_524_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v___x_531_);
v___x_533_ = v_reuseFailAlloc_554_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; lean_object* v_env_535_; lean_object* v_nextMacroScope_536_; lean_object* v_auxDeclNGen_537_; lean_object* v_traceState_538_; lean_object* v_cache_539_; lean_object* v_recordedDeps_540_; lean_object* v_messages_541_; lean_object* v_infoState_542_; lean_object* v_snapshotTasks_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_552_; 
v___x_534_ = lean_st_ref_take(v___y_520_);
v_env_535_ = lean_ctor_get(v___x_534_, 0);
v_nextMacroScope_536_ = lean_ctor_get(v___x_534_, 1);
v_auxDeclNGen_537_ = lean_ctor_get(v___x_534_, 3);
v_traceState_538_ = lean_ctor_get(v___x_534_, 4);
v_cache_539_ = lean_ctor_get(v___x_534_, 5);
v_recordedDeps_540_ = lean_ctor_get(v___x_534_, 6);
v_messages_541_ = lean_ctor_get(v___x_534_, 7);
v_infoState_542_ = lean_ctor_get(v___x_534_, 8);
v_snapshotTasks_543_ = lean_ctor_get(v___x_534_, 9);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; 
v_unused_553_ = lean_ctor_get(v___x_534_, 2);
lean_dec(v_unused_553_);
v___x_545_ = v___x_534_;
v_isShared_546_ = v_isSharedCheck_552_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_snapshotTasks_543_);
lean_inc(v_infoState_542_);
lean_inc(v_messages_541_);
lean_inc(v_recordedDeps_540_);
lean_inc(v_cache_539_);
lean_inc(v_traceState_538_);
lean_inc(v_auxDeclNGen_537_);
lean_inc(v_nextMacroScope_536_);
lean_inc(v_env_535_);
lean_dec(v___x_534_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_552_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 2, v___x_533_);
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_env_535_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_nextMacroScope_536_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v_auxDeclNGen_537_);
lean_ctor_set(v_reuseFailAlloc_551_, 4, v_traceState_538_);
lean_ctor_set(v_reuseFailAlloc_551_, 5, v_cache_539_);
lean_ctor_set(v_reuseFailAlloc_551_, 6, v_recordedDeps_540_);
lean_ctor_set(v_reuseFailAlloc_551_, 7, v_messages_541_);
lean_ctor_set(v_reuseFailAlloc_551_, 8, v_infoState_542_);
lean_ctor_set(v_reuseFailAlloc_551_, 9, v_snapshotTasks_543_);
v___x_548_ = v_reuseFailAlloc_551_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_st_ref_put(v___y_520_, v___x_548_);
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v_r_529_);
return v___x_550_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_520_ = stack[0].m_obj;
lean_object* v_res_556_;
v_res_556_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(v___y_520_);
stack->m_obj
 = v_res_556_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg___boxed(lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(v___y_557_);
lean_dec(v___y_557_);
return v_res_559_;
}
}
lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___x_566_; lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
v___x_566_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(v___y_564_);
v_a_567_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_566_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_560_ = stack[0].m_obj;
lean_object* v___y_561_ = stack[1].m_obj;
lean_object* v___y_562_ = stack[2].m_obj;
lean_object* v___y_563_ = stack[3].m_obj;
lean_object* v___y_564_ = stack[4].m_obj;
lean_object* v_res_575_;
v_res_575_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
stack->m_obj
 = v_res_575_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0___boxed(lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_582_;
}
}
lean_object* l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(lean_object* v_msg_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v___x_590_; lean_object* v_toApplicative_591_; lean_object* v_toFunctor_592_; lean_object* v_toSeq_593_; lean_object* v_toSeqLeft_594_; lean_object* v_toSeqRight_595_; lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___x_600_; lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___f_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___f_609_; lean_object* v___f_610_; lean_object* v___x_6179__overap_611_; lean_object* v___x_612_; 
v___x_590_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_591_ = lean_ctor_get(v___x_590_, 0);
v_toFunctor_592_ = lean_ctor_get(v_toApplicative_591_, 0);
v_toSeq_593_ = lean_ctor_get(v_toApplicative_591_, 2);
v_toSeqLeft_594_ = lean_ctor_get(v_toApplicative_591_, 3);
v_toSeqRight_595_ = lean_ctor_get(v_toApplicative_591_, 4);
v___f_596_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_597_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_592_, 2);
v___f_598_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_598_, 0, v_toFunctor_592_);
v___f_599_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_599_, 0, v_toFunctor_592_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___f_598_);
lean_ctor_set(v___x_600_, 1, v___f_599_);
lean_inc(v_toSeqRight_595_);
v___f_601_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_601_, 0, v_toSeqRight_595_);
lean_inc(v_toSeqLeft_594_);
v___f_602_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_602_, 0, v_toSeqLeft_594_);
lean_inc(v_toSeq_593_);
v___f_603_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_603_, 0, v_toSeq_593_);
v___x_604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_604_, 0, v___x_600_);
lean_ctor_set(v___x_604_, 1, v___f_596_);
lean_ctor_set(v___x_604_, 2, v___f_603_);
lean_ctor_set(v___x_604_, 3, v___f_602_);
lean_ctor_set(v___x_604_, 4, v___f_601_);
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___f_597_);
v___x_606_ = l_StateRefT_x27_instMonad___redArg(v___x_605_);
v___x_607_ = l_Lean_instInhabitedExpr;
v___x_608_ = l_instInhabitedOfMonad___redArg(v___x_606_, v___x_607_);
v___f_609_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_609_, 0, v___x_608_);
v___f_610_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_610_, 0, v___f_609_);
v___x_6179__overap_611_ = lean_panic_fn_borrowed(v___f_610_, v_msg_583_);
lean_dec_ref(v___f_610_);
lean_inc(v___y_588_);
lean_inc_ref(v___y_587_);
lean_inc(v___y_586_);
lean_inc_ref(v___y_585_);
lean_inc_ref(v___y_584_);
v___x_612_ = lean_apply_6(v___x_6179__overap_611_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, lean_box(0));
return v___x_612_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_583_ = stack[0].m_obj;
lean_object* v___y_584_ = stack[1].m_obj;
lean_object* v___y_585_ = stack[2].m_obj;
lean_object* v___y_586_ = stack[3].m_obj;
lean_object* v___y_587_ = stack[4].m_obj;
lean_object* v___y_588_ = stack[5].m_obj;
lean_object* v_res_613_;
v_res_613_ = l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(v_msg_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
stack->m_obj
 = v_res_613_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2___boxed(lean_object* v_msg_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(v_msg_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec_ref(v___y_615_);
return v_res_621_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(lean_object* v_upperBound_624_, lean_object* v___x_625_, lean_object* v_a_626_, lean_object* v_b_627_){
_start:
{
lean_object* v_a_630_; uint8_t v___x_634_; 
v___x_634_ = lean_nat_dec_lt(v_a_626_, v_upperBound_624_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
lean_dec(v_a_626_);
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v_b_627_);
return v___x_635_;
}
else
{
lean_object* v_snd_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_672_; 
v_snd_636_ = lean_ctor_get(v_b_627_, 1);
v_isSharedCheck_672_ = !lean_is_exclusive(v_b_627_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; 
v_unused_673_ = lean_ctor_get(v_b_627_, 0);
lean_dec(v_unused_673_);
v___x_638_ = v_b_627_;
v_isShared_639_ = v_isSharedCheck_672_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_snd_636_);
lean_dec(v_b_627_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_672_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v_fst_640_; lean_object* v_snd_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_671_; 
v_fst_640_ = lean_ctor_get(v_snd_636_, 0);
v_snd_641_ = lean_ctor_get(v_snd_636_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v_snd_636_);
if (v_isSharedCheck_671_ == 0)
{
v___x_643_ = v_snd_636_;
v_isShared_644_ = v_isSharedCheck_671_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_snd_641_);
lean_inc(v_fst_640_);
lean_dec(v_snd_636_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_671_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_box(0);
v___x_646_ = l_Lean_Expr_headBeta(v_snd_641_);
if (lean_obj_tag(v___x_646_) == 7)
{
lean_object* v_body_647_; lean_object* v___x_649_; 
v_body_647_ = lean_ctor_get(v___x_646_, 2);
lean_inc_ref(v_body_647_);
lean_dec_ref_known(v___x_646_, 3);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 1, v_body_647_);
v___x_649_ = v___x_643_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_fst_640_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_body_647_);
v___x_649_ = v_reuseFailAlloc_653_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_651_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 1, v___x_649_);
lean_ctor_set(v___x_638_, 0, v___x_645_);
v___x_651_ = v___x_638_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
v_a_630_ = v___x_651_;
goto v___jp_629_;
}
}
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_expr_instantiate_rev_range(v___x_646_, v_fst_640_, v_a_626_, v___x_625_);
lean_dec_ref(v___x_646_);
v___x_655_ = l_Lean_Expr_headBeta(v___x_654_);
if (lean_obj_tag(v___x_655_) == 7)
{
lean_object* v_body_656_; lean_object* v___x_658_; 
lean_dec(v_fst_640_);
v_body_656_ = lean_ctor_get(v___x_655_, 2);
lean_inc_ref(v_body_656_);
lean_dec_ref_known(v___x_655_, 3);
lean_inc(v_a_626_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 1, v_body_656_);
lean_ctor_set(v___x_643_, 0, v_a_626_);
v___x_658_ = v___x_643_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_626_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v_body_656_);
v___x_658_ = v_reuseFailAlloc_662_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_660_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 1, v___x_658_);
lean_ctor_set(v___x_638_, 0, v___x_645_);
v___x_660_ = v___x_638_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v___x_658_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
v_a_630_ = v___x_660_;
goto v___jp_629_;
}
}
}
else
{
lean_object* v___x_663_; lean_object* v___x_665_; 
lean_dec(v_a_626_);
v___x_663_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 1, v___x_655_);
v___x_665_ = v___x_643_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_fst_640_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v___x_655_);
v___x_665_ = v_reuseFailAlloc_670_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_667_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 1, v___x_665_);
lean_ctor_set(v___x_638_, 0, v___x_663_);
v___x_667_ = v___x_638_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_665_);
v___x_667_ = v_reuseFailAlloc_669_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_668_; 
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
}
}
}
}
}
}
v___jp_629_:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_unsigned_to_nat(1u);
v___x_632_ = lean_nat_add(v_a_626_, v___x_631_);
lean_dec(v_a_626_);
v_a_626_ = v___x_632_;
v_b_627_ = v_a_630_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_624_ = stack[0].m_obj;
lean_object* v___x_625_ = stack[1].m_obj;
lean_object* v_a_626_ = stack[2].m_obj;
lean_object* v_b_627_ = stack[3].m_obj;
lean_object* v_res_674_;
v_res_674_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v_upperBound_624_, v___x_625_, v_a_626_, v_b_627_);
stack->m_obj
 = v_res_674_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___boxed(lean_object* v_upperBound_675_, lean_object* v___x_676_, lean_object* v_a_677_, lean_object* v_b_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v_upperBound_675_, v___x_676_, v_a_677_, v_b_678_);
lean_dec_ref(v___x_676_);
lean_dec(v_upperBound_675_);
return v_res_680_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0(void){
_start:
{
lean_object* v___x_683_; lean_object* v_dummy_684_; 
v___x_683_ = lean_box(0);
v_dummy_684_ = l_Lean_Expr_sort___override(v___x_683_);
return v_dummy_684_;
}
}
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(lean_object* v_e_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_j_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v_j_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = l_Lean_Expr_getAppFn(v_e_685_);
v___x_694_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v___x_693_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v_dummy_696_; lean_object* v_nargs_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___x_694_, 1);
v_dummy_696_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0);
v_nargs_697_ = l_Lean_Expr_getAppNumArgs(v_e_685_);
lean_inc(v_nargs_697_);
v___x_698_ = lean_mk_array(v_nargs_697_, v_dummy_696_);
v___x_699_ = lean_unsigned_to_nat(1u);
v___x_700_ = lean_nat_sub(v_nargs_697_, v___x_699_);
lean_dec(v_nargs_697_);
v___x_701_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_685_, v___x_698_, v___x_700_);
v___x_702_ = lean_array_get_size(v___x_701_);
v___x_703_ = lean_box(0);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v_j_692_);
lean_ctor_set(v___x_704_, 1, v_a_695_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v___x_702_, v___x_701_, v_j_692_, v___x_705_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_724_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_724_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_724_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_724_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v_fst_711_; 
v_fst_711_ = lean_ctor_get(v_a_707_, 0);
if (lean_obj_tag(v_fst_711_) == 0)
{
lean_object* v_snd_712_; lean_object* v_fst_713_; lean_object* v_snd_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_718_; 
v_snd_712_ = lean_ctor_get(v_a_707_, 1);
lean_inc(v_snd_712_);
lean_dec(v_a_707_);
v_fst_713_ = lean_ctor_get(v_snd_712_, 0);
lean_inc(v_fst_713_);
v_snd_714_ = lean_ctor_get(v_snd_712_, 1);
lean_inc(v_snd_714_);
lean_dec(v_snd_712_);
v___x_715_ = lean_expr_instantiate_rev_range(v_snd_714_, v_fst_713_, v___x_702_, v___x_701_);
lean_dec_ref(v___x_701_);
lean_dec(v_fst_713_);
lean_dec(v_snd_714_);
v___x_716_ = l_Lean_Expr_headBeta(v___x_715_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_716_);
v___x_718_ = v___x_709_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
else
{
lean_object* v_val_720_; lean_object* v___x_722_; 
lean_inc_ref(v_fst_711_);
lean_dec(v_a_707_);
lean_dec_ref(v___x_701_);
v_val_720_ = lean_ctor_get(v_fst_711_, 0);
lean_inc(v_val_720_);
lean_dec_ref_known(v_fst_711_, 1);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v_val_720_);
v___x_722_ = v___x_709_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_val_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec_ref(v___x_701_);
v_a_725_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_706_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_706_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
else
{
lean_dec_ref(v_e_685_);
return v___x_694_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_InferType_Pure_inferAppType_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_685_ = stack[0].m_obj;
lean_object* v_a_686_ = stack[1].m_obj;
lean_object* v_a_687_ = stack[2].m_obj;
lean_object* v_a_688_ = stack[3].m_obj;
lean_object* v_a_689_ = stack[4].m_obj;
lean_object* v_a_690_ = stack[5].m_obj;
lean_object* v_res_733_;
v_res_733_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(v_e_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
stack->m_obj
 = v_res_733_;
}
lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(lean_object* v_e_734_, lean_object* v_fvars_735_, lean_object* v_all_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
switch(lean_obj_tag(v_e_734_))
{
case 6:
{
lean_object* v_binderName_743_; lean_object* v_binderType_744_; lean_object* v_body_745_; uint8_t v_binderInfo_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_binderName_743_ = lean_ctor_get(v_e_734_, 0);
lean_inc(v_binderName_743_);
v_binderType_744_ = lean_ctor_get(v_e_734_, 1);
lean_inc_ref(v_binderType_744_);
v_body_745_ = lean_ctor_get(v_e_734_, 2);
lean_inc_ref(v_body_745_);
v_binderInfo_746_ = lean_ctor_get_uint8(v_e_734_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_734_, 3);
v___x_747_ = lean_expr_instantiate_rev(v_binderType_744_, v_all_736_);
lean_dec_ref(v_binderType_744_);
v___x_748_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_750_; uint8_t v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc_n(v_a_749_, 2);
lean_dec_ref_known(v___x_748_, 1);
v___x_750_ = l_Lean_Expr_fvar___override(v_a_749_);
v___x_751_ = 0;
v___x_752_ = l_Lean_LocalContext_mkLocalDecl(v_a_737_, v_a_749_, v_binderName_743_, v___x_747_, v_binderInfo_746_, v___x_751_);
lean_inc_ref(v___x_750_);
v___x_753_ = lean_array_push(v_fvars_735_, v___x_750_);
v___x_754_ = lean_array_push(v_all_736_, v___x_750_);
v_e_734_ = v_body_745_;
v_fvars_735_ = v___x_753_;
v_all_736_ = v___x_754_;
v_a_737_ = v___x_752_;
goto _start;
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec_ref(v___x_747_);
lean_dec_ref(v_body_745_);
lean_dec(v_binderName_743_);
lean_dec_ref(v_a_737_);
lean_dec_ref(v_all_736_);
lean_dec_ref(v_fvars_735_);
v_a_756_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_748_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_748_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
case 8:
{
lean_object* v_declName_764_; lean_object* v_type_765_; lean_object* v_body_766_; lean_object* v___x_767_; uint8_t v___x_768_; lean_object* v___x_769_; 
v_declName_764_ = lean_ctor_get(v_e_734_, 0);
lean_inc(v_declName_764_);
v_type_765_ = lean_ctor_get(v_e_734_, 1);
lean_inc_ref(v_type_765_);
v_body_766_ = lean_ctor_get(v_e_734_, 3);
lean_inc_ref(v_body_766_);
lean_dec_ref_known(v_e_734_, 4);
v___x_767_ = lean_expr_instantiate_rev(v_type_765_, v_all_736_);
lean_dec_ref(v_type_765_);
v___x_768_ = 0;
v___x_769_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_771_; uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc_n(v_a_770_, 2);
lean_dec_ref_known(v___x_769_, 1);
v___x_771_ = l_Lean_Expr_fvar___override(v_a_770_);
v___x_772_ = 0;
v___x_773_ = l_Lean_LocalContext_mkLocalDecl(v_a_737_, v_a_770_, v_declName_764_, v___x_767_, v___x_768_, v___x_772_);
v___x_774_ = lean_array_push(v_all_736_, v___x_771_);
v_e_734_ = v_body_766_;
v_all_736_ = v___x_774_;
v_a_737_ = v___x_773_;
goto _start;
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec_ref(v___x_767_);
lean_dec_ref(v_body_766_);
lean_dec(v_declName_764_);
lean_dec_ref(v_a_737_);
lean_dec_ref(v_all_736_);
lean_dec_ref(v_fvars_735_);
v_a_776_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_769_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_769_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
default: 
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = lean_expr_instantiate_rev(v_e_734_, v_all_736_);
lean_dec_ref(v_all_736_);
lean_dec_ref(v_e_734_);
v___x_785_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v___x_784_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_787_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
v___x_787_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v_fvars_735_, v_a_786_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_786_);
lean_dec_ref(v_fvars_735_);
return v___x_787_;
}
else
{
lean_dec_ref(v_a_737_);
lean_dec_ref(v_fvars_735_);
return v___x_785_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_734_ = stack[0].m_obj;
lean_object* v_fvars_735_ = stack[1].m_obj;
lean_object* v_all_736_ = stack[2].m_obj;
lean_object* v_a_737_ = stack[3].m_obj;
lean_object* v_a_738_ = stack[4].m_obj;
lean_object* v_a_739_ = stack[5].m_obj;
lean_object* v_a_740_ = stack[6].m_obj;
lean_object* v_a_741_ = stack[7].m_obj;
lean_object* v_res_788_;
v_res_788_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(v_e_734_, v_fvars_735_, v_all_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
stack->m_obj
 = v_res_788_;
}
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(lean_object* v_e_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0));
lean_inc_ref(v_a_790_);
v___x_797_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(v_e_789_, v___x_796_, v___x_796_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
return v___x_797_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_789_ = stack[0].m_obj;
lean_object* v_a_790_ = stack[1].m_obj;
lean_object* v_a_791_ = stack[2].m_obj;
lean_object* v_a_792_ = stack[3].m_obj;
lean_object* v_a_793_ = stack[4].m_obj;
lean_object* v_a_794_ = stack[5].m_obj;
lean_object* v_res_798_;
v_res_798_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(v_e_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
stack->m_obj
 = v_res_798_;
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_802_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2));
v___x_803_ = lean_unsigned_to_nat(73u);
v___x_804_ = lean_unsigned_to_nat(135u);
v___x_805_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__1));
v___x_806_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_807_ = l_mkPanicMessageWithDecl(v___x_806_, v___x_805_, v___x_804_, v___x_803_, v___x_802_);
return v___x_807_;
}
}
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType(lean_object* v_e_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
switch(lean_obj_tag(v_e_808_))
{
case 1:
{
lean_object* v_fvarId_815_; lean_object* v___x_816_; 
v_fvarId_815_ = lean_ctor_get(v_e_808_, 0);
lean_inc(v_fvarId_815_);
lean_dec_ref_known(v_e_808_, 1);
v___x_816_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_fvarId_815_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_816_;
}
case 3:
{
lean_object* v_u_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v_u_817_ = lean_ctor_get(v_e_808_, 0);
lean_inc(v_u_817_);
lean_dec_ref_known(v_e_808_, 1);
v___x_818_ = l_Lean_Level_succ___override(v_u_817_);
v___x_819_ = l_Lean_Expr_sort___override(v___x_818_);
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
return v___x_820_;
}
case 4:
{
lean_object* v_declName_821_; lean_object* v_us_822_; lean_object* v___x_823_; 
v_declName_821_ = lean_ctor_get(v_e_808_, 0);
lean_inc(v_declName_821_);
v_us_822_ = lean_ctor_get(v_e_808_, 1);
lean_inc(v_us_822_);
lean_dec_ref_known(v_e_808_, 2);
v___x_823_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(v_declName_821_, v_us_822_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_823_;
}
case 5:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(v_e_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_824_;
}
case 6:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(v_e_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_825_;
}
case 7:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(v_e_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_826_;
}
default: 
{
lean_object* v___x_827_; lean_object* v___x_828_; 
lean_dec_ref(v_e_808_);
v___x_827_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3, &l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3);
v___x_828_ = l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(v___x_827_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_828_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_InferType_Pure_inferType_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_808_ = stack[0].m_obj;
lean_object* v_a_809_ = stack[1].m_obj;
lean_object* v_a_810_ = stack[2].m_obj;
lean_object* v_a_811_ = stack[3].m_obj;
lean_object* v_a_812_ = stack[4].m_obj;
lean_object* v_a_813_ = stack[5].m_obj;
lean_object* v_res_829_;
v_res_829_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_e_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
stack->m_obj
 = v_res_829_;
}
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(lean_object* v_type_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_type_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_851_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_851_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_851_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_851_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
if (lean_obj_tag(v_a_838_) == 3)
{
lean_object* v_u_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
v_u_842_ = lean_ctor_get(v_a_838_, 0);
lean_inc(v_u_842_);
lean_dec_ref_known(v_a_838_, 1);
v___x_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_843_, 0, v_u_842_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_843_);
v___x_845_ = v___x_840_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
else
{
lean_object* v___x_847_; lean_object* v___x_849_; 
lean_dec(v_a_838_);
v___x_847_ = lean_box(0);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_847_);
v___x_849_ = v___x_840_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
v_a_852_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_837_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_837_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_830_ = stack[0].m_obj;
lean_object* v_a_831_ = stack[1].m_obj;
lean_object* v_a_832_ = stack[2].m_obj;
lean_object* v_a_833_ = stack[3].m_obj;
lean_object* v_a_834_ = stack[4].m_obj;
lean_object* v_a_835_ = stack[5].m_obj;
lean_object* v_res_860_;
v_res_860_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(v_type_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
stack->m_obj
 = v_res_860_;
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
return v___x_862_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(lean_object* v_as_863_, size_t v_sz_864_, size_t v_i_865_, lean_object* v_b_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
uint8_t v___x_873_; 
v___x_873_ = lean_usize_dec_lt(v_i_865_, v_sz_864_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v_b_866_);
return v___x_874_;
}
else
{
lean_object* v_snd_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_920_; 
v_snd_875_ = lean_ctor_get(v_b_866_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_b_866_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; 
v_unused_921_ = lean_ctor_get(v_b_866_, 0);
lean_dec(v_unused_921_);
v___x_877_ = v_b_866_;
v_isShared_878_ = v_isSharedCheck_920_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_snd_875_);
lean_dec(v_b_866_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_920_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v_a_880_; lean_object* v___x_881_; 
v___x_879_ = lean_box(0);
v_a_880_ = lean_array_uget_borrowed(v_as_863_, v_i_865_);
lean_inc(v_a_880_);
v___x_881_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_a_880_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_883_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 1);
v___x_883_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(v_a_882_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_903_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_903_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_903_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_903_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
if (lean_obj_tag(v_a_884_) == 1)
{
lean_object* v_val_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
lean_del_object(v___x_886_);
v_val_888_ = lean_ctor_get(v_a_884_, 0);
lean_inc(v_val_888_);
lean_dec_ref_known(v_a_884_, 1);
v___x_889_ = l_Lean_mkLevelIMax_x27(v_val_888_, v_snd_875_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 1, v___x_889_);
lean_ctor_set(v___x_877_, 0, v___x_879_);
v___x_891_ = v___x_877_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v___x_889_);
v___x_891_ = v_reuseFailAlloc_895_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
size_t v___x_892_; size_t v___x_893_; 
v___x_892_ = ((size_t)1ULL);
v___x_893_ = lean_usize_add(v_i_865_, v___x_892_);
v_i_865_ = v___x_893_;
v_b_866_ = v___x_891_;
goto _start;
}
}
else
{
lean_object* v___x_896_; lean_object* v___x_898_; 
lean_dec(v_a_884_);
v___x_896_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_896_);
v___x_898_ = v___x_877_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_snd_875_);
v___x_898_ = v_reuseFailAlloc_902_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_900_; 
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_898_);
v___x_900_ = v___x_886_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
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
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_del_object(v___x_877_);
lean_dec(v_snd_875_);
v_a_904_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_883_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_883_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_del_object(v___x_877_);
lean_dec(v_snd_875_);
v_a_912_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_881_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_881_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_863_ = stack[0].m_obj;
size_t v_sz_864_ = stack[1].m_num;
size_t v_i_865_ = stack[2].m_num;
lean_object* v_b_866_ = stack[3].m_obj;
lean_object* v___y_867_ = stack[4].m_obj;
lean_object* v___y_868_ = stack[5].m_obj;
lean_object* v___y_869_ = stack[6].m_obj;
lean_object* v___y_870_ = stack[7].m_obj;
lean_object* v___y_871_ = stack[8].m_obj;
lean_object* v_res_922_;
v_res_922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(v_as_863_, v_sz_864_, v_i_865_, v_b_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
stack->m_obj
 = v_res_922_;
}
lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(lean_object* v_e_923_, lean_object* v_fvars_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
if (lean_obj_tag(v_e_923_) == 7)
{
lean_object* v_binderName_931_; lean_object* v_binderType_932_; lean_object* v_body_933_; uint8_t v_binderInfo_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_binderName_931_ = lean_ctor_get(v_e_923_, 0);
lean_inc(v_binderName_931_);
v_binderType_932_ = lean_ctor_get(v_e_923_, 1);
lean_inc_ref(v_binderType_932_);
v_body_933_ = lean_ctor_get(v_e_923_, 2);
lean_inc_ref(v_body_933_);
v_binderInfo_934_ = lean_ctor_get_uint8(v_e_923_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_923_, 3);
v___x_935_ = lean_expr_instantiate_rev(v_binderType_932_, v_fvars_924_);
lean_dec_ref(v_binderType_932_);
v___x_936_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_938_; uint8_t v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc_n(v_a_937_, 2);
lean_dec_ref_known(v___x_936_, 1);
v___x_938_ = l_Lean_Expr_fvar___override(v_a_937_);
v___x_939_ = 0;
v___x_940_ = l_Lean_LocalContext_mkLocalDecl(v_a_925_, v_a_937_, v_binderName_931_, v___x_935_, v_binderInfo_934_, v___x_939_);
v___x_941_ = lean_array_push(v_fvars_924_, v___x_938_);
v_e_923_ = v_body_933_;
v_fvars_924_ = v___x_941_;
v_a_925_ = v___x_940_;
goto _start;
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec_ref(v___x_935_);
lean_dec_ref(v_body_933_);
lean_dec(v_binderName_931_);
lean_dec_ref(v_a_925_);
lean_dec_ref(v_fvars_924_);
v_a_943_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_936_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_936_);
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
else
{
lean_object* v_e_951_; lean_object* v___x_952_; 
v_e_951_ = lean_expr_instantiate_rev(v_e_923_, v_fvars_924_);
lean_dec_ref(v_e_923_);
v___x_952_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(v_e_951_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_992_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_992_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_992_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_992_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
if (lean_obj_tag(v_a_953_) == 1)
{
lean_object* v_val_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; size_t v_sz_961_; size_t v___x_962_; lean_object* v___x_963_; 
lean_del_object(v___x_955_);
v_val_957_ = lean_ctor_get(v_a_953_, 0);
lean_inc(v_val_957_);
lean_dec_ref_known(v_a_953_, 1);
v___x_958_ = l_Array_reverse___redArg(v_fvars_924_);
v___x_959_ = lean_box(0);
v___x_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
lean_ctor_set(v___x_960_, 1, v_val_957_);
v_sz_961_ = lean_array_size(v___x_958_);
v___x_962_ = ((size_t)0ULL);
v___x_963_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(v___x_958_, v_sz_961_, v___x_962_, v___x_960_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
lean_dec_ref(v_a_925_);
lean_dec_ref(v___x_958_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_979_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_979_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_979_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_979_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v_fst_968_; 
v_fst_968_ = lean_ctor_get(v_a_964_, 0);
if (lean_obj_tag(v_fst_968_) == 0)
{
lean_object* v_snd_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v_snd_969_ = lean_ctor_get(v_a_964_, 1);
lean_inc(v_snd_969_);
lean_dec(v_a_964_);
v___x_970_ = l_Lean_Level_normalize(v_snd_969_);
lean_dec(v_snd_969_);
v___x_971_ = l_Lean_Expr_sort___override(v___x_970_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_971_);
v___x_973_ = v___x_966_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
else
{
lean_object* v_val_975_; lean_object* v___x_977_; 
lean_inc_ref(v_fst_968_);
lean_dec(v_a_964_);
v_val_975_ = lean_ctor_get(v_fst_968_, 0);
lean_inc(v_val_975_);
lean_dec_ref_known(v_fst_968_, 1);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v_val_975_);
v___x_977_ = v___x_966_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_val_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
v_a_980_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_963_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_963_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
else
{
lean_object* v___x_988_; lean_object* v___x_990_; 
lean_dec(v_a_953_);
lean_dec_ref(v_a_925_);
lean_dec_ref(v_fvars_924_);
v___x_988_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_988_);
v___x_990_ = v___x_955_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec_ref(v_a_925_);
lean_dec_ref(v_fvars_924_);
v_a_993_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_952_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_952_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_923_ = stack[0].m_obj;
lean_object* v_fvars_924_ = stack[1].m_obj;
lean_object* v_a_925_ = stack[2].m_obj;
lean_object* v_a_926_ = stack[3].m_obj;
lean_object* v_a_927_ = stack[4].m_obj;
lean_object* v_a_928_ = stack[5].m_obj;
lean_object* v_a_929_ = stack[6].m_obj;
lean_object* v_res_1001_;
v_res_1001_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(v_e_923_, v_fvars_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
stack->m_obj
 = v_res_1001_;
}
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(lean_object* v_e_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0));
lean_inc_ref(v_a_1003_);
v___x_1010_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(v_e_1002_, v___x_1009_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
return v___x_1010_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_InferType_Pure_inferForallType_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1002_ = stack[0].m_obj;
lean_object* v_a_1003_ = stack[1].m_obj;
lean_object* v_a_1004_ = stack[2].m_obj;
lean_object* v_a_1005_ = stack[3].m_obj;
lean_object* v_a_1006_ = stack[4].m_obj;
lean_object* v_a_1007_ = stack[5].m_obj;
lean_object* v_res_1011_;
v_res_1011_ = l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(v_e_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
stack->m_obj
 = v_res_1011_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___boxed(lean_object* v_e_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(v_e_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec_ref(v_a_1013_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType___boxed(lean_object* v_e_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(v_e_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec_ref(v_a_1021_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f___boxed(lean_object* v_type_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(v_type_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec_ref(v_a_1029_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType___boxed(lean_object* v_e_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_e_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec_ref(v_a_1037_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___boxed(lean_object* v_as_1044_, lean_object* v_sz_1045_, lean_object* v_i_1046_, lean_object* v_b_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
size_t v_sz_boxed_1054_; size_t v_i_boxed_1055_; lean_object* v_res_1056_; 
v_sz_boxed_1054_ = lean_unbox_usize(v_sz_1045_);
lean_dec(v_sz_1045_);
v_i_boxed_1055_ = lean_unbox_usize(v_i_1046_);
lean_dec(v_i_1046_);
v_res_1056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(v_as_1044_, v_sz_boxed_1054_, v_i_boxed_1055_, v_b_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec_ref(v_as_1044_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___boxed(lean_object* v_e_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(v_e_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec_ref(v_a_1058_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go___boxed(lean_object* v_e_1065_, lean_object* v_fvars_1066_, lean_object* v_all_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(v_e_1065_, v_fvars_1066_, v_all_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go___boxed(lean_object* v_e_1075_, lean_object* v_fvars_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(v_e_1075_, v_fvars_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
return v_res_1083_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3(lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(v___y_1088_);
return v___x_1090_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1084_ = stack[0].m_obj;
lean_object* v___y_1085_ = stack[1].m_obj;
lean_object* v___y_1086_ = stack[2].m_obj;
lean_object* v___y_1087_ = stack[3].m_obj;
lean_object* v___y_1088_ = stack[4].m_obj;
lean_object* v_res_1091_;
v_res_1091_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3(v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
stack->m_obj
 = v_res_1091_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___boxed(lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3(v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1098_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9(lean_object* v_upperBound_1099_, lean_object* v___x_1100_, lean_object* v_inst_1101_, lean_object* v_R_1102_, lean_object* v_a_1103_, lean_object* v_b_1104_, lean_object* v_c_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v_upperBound_1099_, v___x_1100_, v_a_1103_, v_b_1104_);
return v___x_1112_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1099_ = stack[0].m_obj;
lean_object* v___x_1100_ = stack[1].m_obj;
lean_object* v_a_1103_ = stack[4].m_obj;
lean_object* v_b_1104_ = stack[5].m_obj;
lean_object* v___y_1106_ = stack[7].m_obj;
lean_object* v___y_1107_ = stack[8].m_obj;
lean_object* v___y_1108_ = stack[9].m_obj;
lean_object* v___y_1109_ = stack[10].m_obj;
lean_object* v___y_1110_ = stack[11].m_obj;
lean_object* v_res_1113_;
v_res_1113_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9(v_upperBound_1099_, v___x_1100_, lean_box(0), lean_box(0), v_a_1103_, v_b_1104_, lean_box(0), v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
stack->m_obj
 = v_res_1113_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___boxed(lean_object* v_upperBound_1114_, lean_object* v___x_1115_, lean_object* v_inst_1116_, lean_object* v_R_1117_, lean_object* v_a_1118_, lean_object* v_b_1119_, lean_object* v_c_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9(v_upperBound_1114_, v___x_1115_, v_inst_1116_, v_R_1117_, v_a_1118_, v_b_1119_, v_c_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec_ref(v___x_1115_);
lean_dec(v_upperBound_1114_);
return v_res_1127_;
}
}
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(lean_object* v_arg_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
switch(lean_obj_tag(v_arg_1128_))
{
case 0:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
return v___x_1136_;
}
case 1:
{
lean_object* v_fvarId_1137_; lean_object* v___x_1138_; 
v_fvarId_1137_ = lean_ctor_get(v_arg_1128_, 0);
lean_inc(v_fvarId_1137_);
lean_dec_ref_known(v_arg_1128_, 1);
v___x_1138_ = l_Lean_Compiler_LCNF_getType(v_fvarId_1137_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
return v___x_1138_;
}
default: 
{
lean_object* v_expr_1139_; lean_object* v___x_1140_; 
v_expr_1139_ = lean_ctor_get(v_arg_1128_, 0);
lean_inc_ref(v_expr_1139_);
lean_dec_ref_known(v_arg_1128_, 1);
v___x_1140_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_expr_1139_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
return v___x_1140_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_InferType_Pure_inferArgType_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_1128_ = stack[0].m_obj;
lean_object* v_a_1129_ = stack[1].m_obj;
lean_object* v_a_1130_ = stack[2].m_obj;
lean_object* v_a_1131_ = stack[3].m_obj;
lean_object* v_a_1132_ = stack[4].m_obj;
lean_object* v_a_1133_ = stack[5].m_obj;
lean_object* v_res_1141_;
v_res_1141_ = l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(v_arg_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
stack->m_obj
 = v_res_1141_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferArgType___boxed(lean_object* v_arg_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(v_arg_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec_ref(v_a_1143_);
return v_res_1149_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(lean_object* v_upperBound_1150_, lean_object* v_args_1151_, lean_object* v_a_1152_, lean_object* v_b_1153_){
_start:
{
lean_object* v_a_1156_; uint8_t v___x_1160_; 
v___x_1160_ = lean_nat_dec_lt(v_a_1152_, v_upperBound_1150_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
lean_dec(v_a_1152_);
lean_dec_ref(v_args_1151_);
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v_b_1153_);
return v___x_1161_;
}
else
{
lean_object* v_snd_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1198_; 
v_snd_1162_ = lean_ctor_get(v_b_1153_, 1);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_b_1153_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; 
v_unused_1199_ = lean_ctor_get(v_b_1153_, 0);
lean_dec(v_unused_1199_);
v___x_1164_ = v_b_1153_;
v_isShared_1165_ = v_isSharedCheck_1198_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_snd_1162_);
lean_dec(v_b_1153_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1198_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v_fst_1166_; lean_object* v_snd_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1197_; 
v_fst_1166_ = lean_ctor_get(v_snd_1162_, 0);
v_snd_1167_ = lean_ctor_get(v_snd_1162_, 1);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_snd_1162_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1169_ = v_snd_1162_;
v_isShared_1170_ = v_isSharedCheck_1197_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_snd_1167_);
lean_inc(v_fst_1166_);
lean_dec(v_snd_1162_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1197_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = lean_box(0);
v___x_1172_ = l_Lean_Expr_headBeta(v_snd_1167_);
if (lean_obj_tag(v___x_1172_) == 7)
{
lean_object* v_body_1173_; lean_object* v___x_1175_; 
v_body_1173_ = lean_ctor_get(v___x_1172_, 2);
lean_inc_ref(v_body_1173_);
lean_dec_ref_known(v___x_1172_, 3);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v_body_1173_);
v___x_1175_ = v___x_1169_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_fst_1166_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_body_1173_);
v___x_1175_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1177_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v___x_1175_);
lean_ctor_set(v___x_1164_, 0, v___x_1171_);
v___x_1177_ = v___x_1164_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
v_a_1156_ = v___x_1177_;
goto v___jp_1155_;
}
}
}
else
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
lean_inc_ref(v_args_1151_);
v___x_1180_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(v___x_1172_, v_fst_1166_, v_a_1152_, v_args_1151_);
lean_dec_ref(v___x_1172_);
v___x_1181_ = l_Lean_Expr_headBeta(v___x_1180_);
if (lean_obj_tag(v___x_1181_) == 7)
{
lean_object* v_body_1182_; lean_object* v___x_1184_; 
lean_dec(v_fst_1166_);
v_body_1182_ = lean_ctor_get(v___x_1181_, 2);
lean_inc_ref(v_body_1182_);
lean_dec_ref_known(v___x_1181_, 3);
lean_inc(v_a_1152_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v_body_1182_);
lean_ctor_set(v___x_1169_, 0, v_a_1152_);
v___x_1184_ = v___x_1169_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1152_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_body_1182_);
v___x_1184_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1186_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v___x_1184_);
lean_ctor_set(v___x_1164_, 0, v___x_1171_);
v___x_1186_ = v___x_1164_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
v_a_1156_ = v___x_1186_;
goto v___jp_1155_;
}
}
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
lean_dec(v_a_1152_);
lean_dec_ref(v_args_1151_);
v___x_1189_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___x_1181_);
v___x_1191_ = v___x_1169_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_fst_1166_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v___x_1181_);
v___x_1191_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1193_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v___x_1191_);
lean_ctor_set(v___x_1164_, 0, v___x_1189_);
v___x_1193_ = v___x_1164_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
return v___x_1194_;
}
}
}
}
}
}
}
v___jp_1155_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_unsigned_to_nat(1u);
v___x_1158_ = lean_nat_add(v_a_1152_, v___x_1157_);
lean_dec(v_a_1152_);
v_a_1152_ = v___x_1158_;
v_b_1153_ = v_a_1156_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1150_ = stack[0].m_obj;
lean_object* v_args_1151_ = stack[1].m_obj;
lean_object* v_a_1152_ = stack[2].m_obj;
lean_object* v_b_1153_ = stack[3].m_obj;
lean_object* v_res_1200_;
v_res_1200_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v_upperBound_1150_, v_args_1151_, v_a_1152_, v_b_1153_);
stack->m_obj
 = v_res_1200_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg___boxed(lean_object* v_upperBound_1201_, lean_object* v_args_1202_, lean_object* v_a_1203_, lean_object* v_b_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v_upperBound_1201_, v_args_1202_, v_a_1203_, v_b_1204_);
lean_dec(v_upperBound_1201_);
return v_res_1206_;
}
}
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(lean_object* v_fType_1207_, lean_object* v_args_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1215_ = lean_array_get_size(v_args_1208_);
v___x_1216_ = lean_unsigned_to_nat(0u);
v___x_1217_ = lean_box(0);
v___x_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1216_);
lean_ctor_set(v___x_1218_, 1, v_fType_1207_);
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
lean_inc_ref(v_args_1208_);
v___x_1220_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v___x_1215_, v_args_1208_, v___x_1216_, v___x_1219_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1238_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1238_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1238_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v_fst_1225_; 
v_fst_1225_ = lean_ctor_get(v_a_1221_, 0);
if (lean_obj_tag(v_fst_1225_) == 0)
{
lean_object* v_snd_1226_; lean_object* v_fst_1227_; lean_object* v_snd_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1232_; 
v_snd_1226_ = lean_ctor_get(v_a_1221_, 1);
lean_inc(v_snd_1226_);
lean_dec(v_a_1221_);
v_fst_1227_ = lean_ctor_get(v_snd_1226_, 0);
lean_inc(v_fst_1227_);
v_snd_1228_ = lean_ctor_get(v_snd_1226_, 1);
lean_inc(v_snd_1228_);
lean_dec(v_snd_1226_);
v___x_1229_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(v_snd_1228_, v_fst_1227_, v___x_1215_, v_args_1208_);
lean_dec(v_fst_1227_);
lean_dec(v_snd_1228_);
v___x_1230_ = l_Lean_Expr_headBeta(v___x_1229_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1230_);
v___x_1232_ = v___x_1223_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
else
{
lean_object* v_val_1234_; lean_object* v___x_1236_; 
lean_inc_ref(v_fst_1225_);
lean_dec(v_a_1221_);
lean_dec_ref(v_args_1208_);
v_val_1234_ = lean_ctor_get(v_fst_1225_, 0);
lean_inc(v_val_1234_);
lean_dec_ref_known(v_fst_1225_, 1);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v_val_1234_);
v___x_1236_ = v___x_1223_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_val_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_dec_ref(v_args_1208_);
v_a_1239_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1220_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1220_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_fType_1207_ = stack[0].m_obj;
lean_object* v_args_1208_ = stack[1].m_obj;
lean_object* v_a_1209_ = stack[2].m_obj;
lean_object* v_a_1210_ = stack[3].m_obj;
lean_object* v_a_1211_ = stack[4].m_obj;
lean_object* v_a_1212_ = stack[5].m_obj;
lean_object* v_a_1213_ = stack[6].m_obj;
lean_object* v_res_1247_;
v_res_1247_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_fType_1207_, v_args_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
stack->m_obj
 = v_res_1247_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore___boxed(lean_object* v_fType_1248_, lean_object* v_args_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_fType_1248_, v_args_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec(v_a_1252_);
lean_dec_ref(v_a_1251_);
lean_dec_ref(v_a_1250_);
return v_res_1256_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0(lean_object* v_upperBound_1257_, lean_object* v_args_1258_, lean_object* v_inst_1259_, lean_object* v_R_1260_, lean_object* v_a_1261_, lean_object* v_b_1262_, lean_object* v_c_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v_upperBound_1257_, v_args_1258_, v_a_1261_, v_b_1262_);
return v___x_1270_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1257_ = stack[0].m_obj;
lean_object* v_args_1258_ = stack[1].m_obj;
lean_object* v_a_1261_ = stack[4].m_obj;
lean_object* v_b_1262_ = stack[5].m_obj;
lean_object* v___y_1264_ = stack[7].m_obj;
lean_object* v___y_1265_ = stack[8].m_obj;
lean_object* v___y_1266_ = stack[9].m_obj;
lean_object* v___y_1267_ = stack[10].m_obj;
lean_object* v___y_1268_ = stack[11].m_obj;
lean_object* v_res_1271_;
v_res_1271_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0(v_upperBound_1257_, v_args_1258_, lean_box(0), lean_box(0), v_a_1261_, v_b_1262_, lean_box(0), v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
stack->m_obj
 = v_res_1271_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___boxed(lean_object* v_upperBound_1272_, lean_object* v_args_1273_, lean_object* v_inst_1274_, lean_object* v_R_1275_, lean_object* v_a_1276_, lean_object* v_b_1277_, lean_object* v_c_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0(v_upperBound_1272_, v_args_1273_, v_inst_1274_, v_R_1275_, v_a_1276_, v_b_1277_, v_c_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v_upperBound_1272_);
return v_res_1285_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0);
v___x_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
return v___x_1287_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1288_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1289_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0);
v___x_1290_ = lean_unsigned_to_nat(0u);
v___x_1291_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
lean_ctor_set(v___x_1291_, 2, v___x_1290_);
lean_ctor_set(v___x_1291_, 3, v___x_1290_);
lean_ctor_set(v___x_1291_, 4, v___x_1289_);
lean_ctor_set(v___x_1291_, 5, v___x_1289_);
lean_ctor_set(v___x_1291_, 6, v___x_1289_);
lean_ctor_set(v___x_1291_, 7, v___x_1289_);
lean_ctor_set(v___x_1291_, 8, v___x_1289_);
lean_ctor_set(v___x_1291_, 9, v___x_1289_);
lean_ctor_set(v___x_1291_, 10, v___x_1289_);
lean_ctor_set(v___x_1291_, 11, v___x_1288_);
return v___x_1291_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(lean_object* v_msg_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_ref_1298_; lean_object* v___x_1299_; lean_object* v_env_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v_ref_1298_ = lean_ctor_get(v___y_1295_, 2);
v___x_1299_ = lean_st_ref_get(v___y_1296_);
v_env_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc_ref(v_env_1300_);
lean_dec(v___x_1299_);
v___x_1301_ = lean_st_ref_get(v___y_1294_);
v___x_1302_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1293_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1325_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1305_ = v___x_1302_;
v_isShared_1306_ = v_isSharedCheck_1325_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1302_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1325_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v_lctx_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1323_; 
v_lctx_1307_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1323_ == 0)
{
lean_object* v_unused_1324_; 
v_unused_1324_ = lean_ctor_get(v___x_1301_, 1);
lean_dec(v_unused_1324_);
v___x_1309_ = v___x_1301_;
v_isShared_1310_ = v_isSharedCheck_1323_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_lctx_1307_);
lean_dec(v___x_1301_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1323_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
uint8_t v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1311_ = lean_unbox(v_a_1303_);
lean_dec(v_a_1303_);
v___x_1312_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1307_, v___x_1311_);
lean_dec_ref(v_lctx_1307_);
v___x_1313_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1295_);
v___x_1314_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1);
v___x_1315_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1315_, 0, v_env_1300_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
lean_ctor_set(v___x_1315_, 2, v___x_1312_);
lean_ctor_set(v___x_1315_, 3, v___x_1313_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set_tag(v___x_1309_, 3);
lean_ctor_set(v___x_1309_, 1, v_msg_1292_);
lean_ctor_set(v___x_1309_, 0, v___x_1315_);
v___x_1317_ = v___x_1309_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1315_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_msg_1292_);
v___x_1317_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1318_; lean_object* v___x_1320_; 
lean_inc(v_ref_1298_);
v___x_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1318_, 0, v_ref_1298_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set_tag(v___x_1305_, 1);
lean_ctor_set(v___x_1305_, 0, v___x_1318_);
v___x_1320_ = v___x_1305_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec(v___x_1301_);
lean_dec_ref(v_env_1300_);
lean_dec_ref(v_msg_1292_);
v_a_1326_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1302_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1302_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1292_ = stack[0].m_obj;
lean_object* v___y_1293_ = stack[1].m_obj;
lean_object* v___y_1294_ = stack[2].m_obj;
lean_object* v___y_1295_ = stack[3].m_obj;
lean_object* v___y_1296_ = stack[4].m_obj;
lean_object* v_res_1334_;
v_res_1334_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v_msg_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
stack->m_obj
 = v_res_1334_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___boxed(lean_object* v_msg_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v_msg_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
return v_res_1341_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0(lean_object* v_00_u03b1_1342_, lean_object* v_msg_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v_msg_1343_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
return v___x_1350_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1343_ = stack[1].m_obj;
lean_object* v___y_1344_ = stack[2].m_obj;
lean_object* v___y_1345_ = stack[3].m_obj;
lean_object* v___y_1346_ = stack[4].m_obj;
lean_object* v___y_1347_ = stack[5].m_obj;
lean_object* v___y_1348_ = stack[6].m_obj;
lean_object* v_res_1351_;
v_res_1351_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0(lean_box(0), v_msg_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
stack->m_obj
 = v_res_1351_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___boxed(lean_object* v_00_u03b1_1352_, lean_object* v_msg_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0(v_00_u03b1_1352_, v_msg_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec_ref(v___y_1354_);
return v_res_1360_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__0));
v___x_1363_ = l_Lean_stringToMessageData(v___x_1362_);
return v___x_1363_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(lean_object* v_upperBound_1364_, lean_object* v_s_1365_, lean_object* v_structName_1366_, lean_object* v_idx_1367_, lean_object* v_a_1368_, lean_object* v_b_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_a_1377_; uint8_t v___x_1381_; 
v___x_1381_ = lean_nat_dec_lt(v_a_1368_, v_upperBound_1364_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
lean_dec(v_a_1368_);
lean_dec(v_idx_1367_);
lean_dec(v_structName_1366_);
lean_dec(v_s_1365_);
v___x_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1382_, 0, v_b_1369_);
return v___x_1382_;
}
else
{
lean_object* v_snd_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1421_; 
v_snd_1383_ = lean_ctor_get(v_b_1369_, 1);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_b_1369_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; 
v_unused_1422_ = lean_ctor_get(v_b_1369_, 0);
lean_dec(v_unused_1422_);
v___x_1385_ = v_b_1369_;
v_isShared_1386_ = v_isSharedCheck_1421_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_snd_1383_);
lean_dec(v_b_1369_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1421_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; 
v___x_1387_ = lean_box(0);
if (lean_obj_tag(v_snd_1383_) == 7)
{
lean_object* v_body_1388_; uint8_t v___x_1389_; 
v_body_1388_ = lean_ctor_get(v_snd_1383_, 2);
lean_inc_ref(v_body_1388_);
lean_dec_ref_known(v_snd_1383_, 3);
v___x_1389_ = l_Lean_Expr_hasLooseBVars(v_body_1388_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1391_; 
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 1, v_body_1388_);
lean_ctor_set(v___x_1385_, 0, v___x_1387_);
v___x_1391_ = v___x_1385_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_body_1388_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
v_a_1377_ = v___x_1391_;
goto v___jp_1376_;
}
}
else
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1393_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_1394_ = lean_expr_instantiate1(v_body_1388_, v___x_1393_);
lean_dec_ref(v_body_1388_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 1, v___x_1394_);
lean_ctor_set(v___x_1385_, 0, v___x_1387_);
v___x_1396_ = v___x_1385_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
v_a_1377_ = v___x_1396_;
goto v___jp_1376_;
}
}
}
else
{
uint8_t v___x_1398_; 
v___x_1398_ = l_Lean_Expr_isErased(v_snd_1383_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1399_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
lean_inc(v_s_1365_);
v___x_1400_ = l_Lean_mkFVar(v_s_1365_);
lean_inc(v_idx_1367_);
lean_inc(v_structName_1366_);
v___x_1401_ = l_Lean_mkProj(v_structName_1366_, v_idx_1367_, v___x_1400_);
v___x_1402_ = l_Lean_indentExpr(v___x_1401_);
v___x_1403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1399_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
v___x_1404_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_1403_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v___x_1406_; 
lean_dec_ref_known(v___x_1404_, 1);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1387_);
v___x_1406_ = v___x_1385_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_snd_1383_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
v_a_1377_ = v___x_1406_;
goto v___jp_1376_;
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_del_object(v___x_1385_);
lean_dec(v_snd_1383_);
lean_dec(v_a_1368_);
lean_dec(v_idx_1367_);
lean_dec(v_structName_1366_);
lean_dec(v_s_1365_);
v_a_1408_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1404_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1404_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
lean_dec(v_a_1368_);
lean_dec(v_idx_1367_);
lean_dec(v_structName_1366_);
lean_dec(v_s_1365_);
v___x_1416_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1416_);
v___x_1418_ = v___x_1385_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_snd_1383_);
v___x_1418_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
}
}
}
}
v___jp_1376_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_unsigned_to_nat(1u);
v___x_1379_ = lean_nat_add(v_a_1368_, v___x_1378_);
lean_dec(v_a_1368_);
v_a_1368_ = v___x_1379_;
v_b_1369_ = v_a_1377_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1364_ = stack[0].m_obj;
lean_object* v_s_1365_ = stack[1].m_obj;
lean_object* v_structName_1366_ = stack[2].m_obj;
lean_object* v_idx_1367_ = stack[3].m_obj;
lean_object* v_a_1368_ = stack[4].m_obj;
lean_object* v_b_1369_ = stack[5].m_obj;
lean_object* v___y_1370_ = stack[6].m_obj;
lean_object* v___y_1371_ = stack[7].m_obj;
lean_object* v___y_1372_ = stack[8].m_obj;
lean_object* v___y_1373_ = stack[9].m_obj;
lean_object* v___y_1374_ = stack[10].m_obj;
lean_object* v_res_1423_;
v_res_1423_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_1364_, v_s_1365_, v_structName_1366_, v_idx_1367_, v_a_1368_, v_b_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
stack->m_obj
 = v_res_1423_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___boxed(lean_object* v_upperBound_1424_, lean_object* v_s_1425_, lean_object* v_structName_1426_, lean_object* v_idx_1427_, lean_object* v_a_1428_, lean_object* v_b_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_1424_, v_s_1425_, v_structName_1426_, v_idx_1427_, v_a_1428_, v_b_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v_upperBound_1424_);
return v_res_1436_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(lean_object* v_upperBound_1437_, lean_object* v_s_1438_, lean_object* v_structName_1439_, lean_object* v_idx_1440_, lean_object* v_a_1441_, lean_object* v_b_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_a_1450_; uint8_t v___x_1454_; 
v___x_1454_ = lean_nat_dec_lt(v_a_1441_, v_upperBound_1437_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; 
lean_dec(v_idx_1440_);
lean_dec(v_structName_1439_);
lean_dec(v_s_1438_);
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v_b_1442_);
return v___x_1455_;
}
else
{
lean_object* v_snd_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1494_; 
v_snd_1456_ = lean_ctor_get(v_b_1442_, 1);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_b_1442_);
if (v_isSharedCheck_1494_ == 0)
{
lean_object* v_unused_1495_; 
v_unused_1495_ = lean_ctor_get(v_b_1442_, 0);
lean_dec(v_unused_1495_);
v___x_1458_ = v_b_1442_;
v_isShared_1459_ = v_isSharedCheck_1494_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_snd_1456_);
lean_dec(v_b_1442_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1494_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_box(0);
if (lean_obj_tag(v_snd_1456_) == 7)
{
lean_object* v_body_1461_; uint8_t v___x_1462_; 
v_body_1461_ = lean_ctor_get(v_snd_1456_, 2);
lean_inc_ref(v_body_1461_);
lean_dec_ref_known(v_snd_1456_, 3);
v___x_1462_ = l_Lean_Expr_hasLooseBVars(v_body_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1464_; 
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 1, v_body_1461_);
lean_ctor_set(v___x_1458_, 0, v___x_1460_);
v___x_1464_ = v___x_1458_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_body_1461_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
v_a_1450_ = v___x_1464_;
goto v___jp_1449_;
}
}
else
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1469_; 
v___x_1466_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_1467_ = lean_expr_instantiate1(v_body_1461_, v___x_1466_);
lean_dec_ref(v_body_1461_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 1, v___x_1467_);
lean_ctor_set(v___x_1458_, 0, v___x_1460_);
v___x_1469_ = v___x_1458_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v___x_1467_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
v_a_1450_ = v___x_1469_;
goto v___jp_1449_;
}
}
}
else
{
uint8_t v___x_1471_; 
v___x_1471_ = l_Lean_Expr_isErased(v_snd_1456_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1472_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
lean_inc(v_s_1438_);
v___x_1473_ = l_Lean_mkFVar(v_s_1438_);
lean_inc(v_idx_1440_);
lean_inc(v_structName_1439_);
v___x_1474_ = l_Lean_mkProj(v_structName_1439_, v_idx_1440_, v___x_1473_);
v___x_1475_ = l_Lean_indentExpr(v___x_1474_);
v___x_1476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1472_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v___x_1477_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_1476_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v___x_1479_; 
lean_dec_ref_known(v___x_1477_, 1);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v___x_1460_);
v___x_1479_ = v___x_1458_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_snd_1456_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
v_a_1450_ = v___x_1479_;
goto v___jp_1449_;
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_del_object(v___x_1458_);
lean_dec(v_snd_1456_);
lean_dec(v_idx_1440_);
lean_dec(v_structName_1439_);
lean_dec(v_s_1438_);
v_a_1481_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1477_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1477_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1491_; 
lean_dec(v_idx_1440_);
lean_dec(v_structName_1439_);
lean_dec(v_s_1438_);
v___x_1489_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v___x_1489_);
v___x_1491_ = v___x_1458_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_snd_1456_);
v___x_1491_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
return v___x_1492_;
}
}
}
}
}
v___jp_1449_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = lean_unsigned_to_nat(1u);
v___x_1452_ = lean_nat_add(v_a_1441_, v___x_1451_);
v___x_1453_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_1437_, v_s_1438_, v_structName_1439_, v_idx_1440_, v___x_1452_, v_a_1450_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
return v___x_1453_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1437_ = stack[0].m_obj;
lean_object* v_s_1438_ = stack[1].m_obj;
lean_object* v_structName_1439_ = stack[2].m_obj;
lean_object* v_idx_1440_ = stack[3].m_obj;
lean_object* v_a_1441_ = stack[4].m_obj;
lean_object* v_b_1442_ = stack[5].m_obj;
lean_object* v___y_1443_ = stack[6].m_obj;
lean_object* v___y_1444_ = stack[7].m_obj;
lean_object* v___y_1445_ = stack[8].m_obj;
lean_object* v___y_1446_ = stack[9].m_obj;
lean_object* v___y_1447_ = stack[10].m_obj;
lean_object* v_res_1496_;
v_res_1496_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_upperBound_1437_, v_s_1438_, v_structName_1439_, v_idx_1440_, v_a_1441_, v_b_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
stack->m_obj
 = v_res_1496_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg___boxed(lean_object* v_upperBound_1497_, lean_object* v_s_1498_, lean_object* v_structName_1499_, lean_object* v_idx_1500_, lean_object* v_a_1501_, lean_object* v_b_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_upperBound_1497_, v_s_1498_, v_structName_1499_, v_idx_1500_, v_a_1501_, v_b_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v_a_1501_);
lean_dec(v_upperBound_1497_);
return v_res_1509_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_ref_1510_, lean_object* v_msg_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_toCold_1518_; lean_object* v_currRecDepth_1519_; lean_object* v_ref_1520_; uint16_t v_optionFlags_1521_; uint8_t v_suppressElabErrors_1522_; uint8_t v_isRecordingDeps_1523_; lean_object* v_ref_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_toCold_1518_ = lean_ctor_get(v___y_1515_, 0);
v_currRecDepth_1519_ = lean_ctor_get(v___y_1515_, 1);
v_ref_1520_ = lean_ctor_get(v___y_1515_, 2);
v_optionFlags_1521_ = lean_ctor_get_uint16(v___y_1515_, sizeof(void*)*3);
v_suppressElabErrors_1522_ = lean_ctor_get_uint8(v___y_1515_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1523_ = lean_ctor_get_uint8(v___y_1515_, sizeof(void*)*3 + 3);
v_ref_1524_ = l_Lean_replaceRef(v_ref_1510_, v_ref_1520_);
lean_inc(v_currRecDepth_1519_);
lean_inc_ref(v_toCold_1518_);
v___x_1525_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1525_, 0, v_toCold_1518_);
lean_ctor_set(v___x_1525_, 1, v_currRecDepth_1519_);
lean_ctor_set(v___x_1525_, 2, v_ref_1524_);
lean_ctor_set_uint16(v___x_1525_, sizeof(void*)*3, v_optionFlags_1521_);
lean_ctor_set_uint8(v___x_1525_, sizeof(void*)*3 + 2, v_suppressElabErrors_1522_);
lean_ctor_set_uint8(v___x_1525_, sizeof(void*)*3 + 3, v_isRecordingDeps_1523_);
v___x_1526_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v_msg_1511_, v___y_1513_, v___y_1514_, v___x_1525_, v___y_1516_);
lean_dec_ref_known(v___x_1525_, 3);
return v___x_1526_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1510_ = stack[0].m_obj;
lean_object* v_msg_1511_ = stack[1].m_obj;
lean_object* v___y_1512_ = stack[2].m_obj;
lean_object* v___y_1513_ = stack[3].m_obj;
lean_object* v___y_1514_ = stack[4].m_obj;
lean_object* v___y_1515_ = stack[5].m_obj;
lean_object* v___y_1516_ = stack[6].m_obj;
lean_object* v_res_1527_;
v_res_1527_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_1510_, v_msg_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
stack->m_obj
 = v_res_1527_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_ref_1528_, lean_object* v_msg_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_1528_, v_msg_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v_ref_1528_);
return v_res_1536_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1537_ = lean_box(1);
v___x_1538_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3);
v___x_1539_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0);
v___x_1540_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
lean_ctor_set(v___x_1540_, 1, v___x_1538_);
lean_ctor_set(v___x_1540_, 2, v___x_1537_);
return v___x_1540_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__1));
v___x_1543_ = l_Lean_stringToMessageData(v___x_1542_);
return v___x_1543_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__3));
v___x_1546_ = l_Lean_stringToMessageData(v___x_1545_);
return v___x_1546_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__5));
v___x_1549_ = l_Lean_stringToMessageData(v___x_1548_);
return v___x_1549_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__7));
v___x_1552_ = l_Lean_stringToMessageData(v___x_1551_);
return v___x_1552_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__9));
v___x_1555_ = l_Lean_stringToMessageData(v___x_1554_);
return v___x_1555_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__11));
v___x_1558_ = l_Lean_stringToMessageData(v___x_1557_);
return v___x_1558_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14(void){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__13));
v___x_1561_ = l_Lean_stringToMessageData(v___x_1560_);
return v___x_1561_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__16(void){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__15));
v___x_1564_ = l_Lean_stringToMessageData(v___x_1563_);
return v___x_1564_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__18(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__17));
v___x_1567_ = l_Lean_stringToMessageData(v___x_1566_);
return v___x_1567_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__20(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__19));
v___x_1570_ = l_Lean_stringToMessageData(v___x_1569_);
return v___x_1570_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__22(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__21));
v___x_1573_ = l_Lean_stringToMessageData(v___x_1572_);
return v___x_1573_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(lean_object* v_msg_1574_, lean_object* v_declHint_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v_env_1580_; uint8_t v___x_1581_; 
v___x_1578_ = lean_box(0);
v___x_1579_ = lean_st_ref_get(v___y_1576_);
v_env_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc_ref(v_env_1580_);
lean_dec(v___x_1579_);
v___x_1581_ = l_Lean_Name_isAnonymous(v_declHint_1575_);
if (v___x_1581_ == 0)
{
uint8_t v_isExporting_1582_; 
v_isExporting_1582_ = lean_ctor_get_uint8(v_env_1580_, sizeof(void*)*13);
if (v_isExporting_1582_ == 0)
{
lean_object* v___x_1583_; 
lean_dec_ref(v_env_1580_);
lean_dec(v_declHint_1575_);
v___x_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1583_, 0, v_msg_1574_);
return v___x_1583_;
}
else
{
lean_object* v___x_1584_; uint8_t v___x_1585_; 
lean_inc_ref(v_env_1580_);
v___x_1584_ = l_Lean_Environment_setExporting(v_env_1580_, v___x_1581_);
lean_inc(v_declHint_1575_);
lean_inc_ref(v___x_1584_);
v___x_1585_ = l_Lean_Environment_contains(v___x_1584_, v_declHint_1575_, v_isExporting_1582_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; 
lean_dec_ref(v___x_1584_);
lean_dec_ref(v_env_1580_);
lean_dec(v_declHint_1575_);
v___x_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1586_, 0, v_msg_1574_);
return v___x_1586_;
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v_c_1592_; lean_object* v___x_1593_; 
v___x_1587_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1);
v___x_1588_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0);
v___x_1589_ = l_Lean_Options_empty;
v___x_1590_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1584_);
lean_ctor_set(v___x_1590_, 1, v___x_1587_);
lean_ctor_set(v___x_1590_, 2, v___x_1588_);
lean_ctor_set(v___x_1590_, 3, v___x_1589_);
lean_inc(v_declHint_1575_);
v___x_1591_ = l_Lean_MessageData_ofConstName(v_declHint_1575_, v___x_1581_);
v_c_1592_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1592_, 0, v___x_1590_);
lean_ctor_set(v_c_1592_, 1, v___x_1591_);
v___x_1593_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1580_, v_declHint_1575_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
lean_dec_ref(v_env_1580_);
lean_dec(v_declHint_1575_);
v___x_1594_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2);
v___x_1595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
lean_ctor_set(v___x_1595_, 1, v_c_1592_);
v___x_1596_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4);
v___x_1597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = l_Lean_MessageData_note(v___x_1597_);
v___x_1599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1599_, 0, v_msg_1574_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
return v___x_1600_;
}
else
{
lean_object* v_val_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1657_; 
v_val_1601_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1603_ = v___x_1593_;
v_isShared_1604_ = v_isSharedCheck_1657_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_val_1601_);
lean_dec(v___x_1593_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1657_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v_modules_1606_; lean_object* v_moduleNames_1607_; lean_object* v_mod_1608_; uint8_t v___y_1610_; uint8_t v___x_1640_; 
v___x_1605_ = l_Lean_Environment_header(v_env_1580_);
lean_dec_ref(v_env_1580_);
v_modules_1606_ = lean_ctor_get(v___x_1605_, 3);
lean_inc_ref(v_modules_1606_);
v_moduleNames_1607_ = lean_ctor_get(v___x_1605_, 4);
lean_inc_ref(v_moduleNames_1607_);
lean_dec_ref(v___x_1605_);
v_mod_1608_ = lean_array_get(v___x_1578_, v_moduleNames_1607_, v_val_1601_);
lean_dec_ref(v_moduleNames_1607_);
v___x_1640_ = l_Lean_isPrivateName(v_declHint_1575_);
lean_dec(v_declHint_1575_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1641_ = lean_array_get_size(v_modules_1606_);
v___x_1642_ = lean_nat_dec_lt(v_val_1601_, v___x_1641_);
if (v___x_1642_ == 0)
{
lean_dec_ref(v_modules_1606_);
lean_dec(v_val_1601_);
v___y_1610_ = v___x_1640_;
goto v___jp_1609_;
}
else
{
lean_object* v___x_1643_; lean_object* v_toImport_1644_; uint8_t v_isExported_1645_; 
v___x_1643_ = lean_array_fget(v_modules_1606_, v_val_1601_);
lean_dec(v_val_1601_);
lean_dec_ref(v_modules_1606_);
v_toImport_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc_ref(v_toImport_1644_);
lean_dec(v___x_1643_);
v_isExported_1645_ = lean_ctor_get_uint8(v_toImport_1644_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1644_);
v___y_1610_ = v_isExported_1645_;
goto v___jp_1609_;
}
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
lean_dec_ref(v_modules_1606_);
lean_del_object(v___x_1603_);
lean_dec(v_val_1601_);
v___x_1646_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2);
v___x_1647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
lean_ctor_set(v___x_1647_, 1, v_c_1592_);
v___x_1648_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__20);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = l_Lean_MessageData_ofName(v_mod_1608_);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__22);
v___x_1653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = l_Lean_MessageData_note(v___x_1653_);
v___x_1655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1655_, 0, v_msg_1574_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
return v___x_1656_;
}
v___jp_1609_:
{
if (v___y_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; 
v___x_1611_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6);
v___x_1612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
lean_ctor_set(v___x_1612_, 1, v_c_1592_);
v___x_1613_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = l_Lean_MessageData_ofName(v_mod_1608_);
v___x_1616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10);
v___x_1618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1616_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = l_Lean_MessageData_note(v___x_1618_);
v___x_1620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1620_, 0, v_msg_1574_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set_tag(v___x_1603_, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1620_);
v___x_1622_ = v___x_1603_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
else
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1638_; 
v___x_1624_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12);
v___x_1625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
lean_ctor_set(v___x_1625_, 1, v_c_1592_);
v___x_1626_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14);
v___x_1627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1625_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = l_Lean_MessageData_ofName(v_mod_1608_);
lean_inc_ref(v___x_1628_);
v___x_1629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__16);
v___x_1631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
lean_ctor_set(v___x_1632_, 1, v___x_1628_);
v___x_1633_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__18);
v___x_1634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1632_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = l_Lean_MessageData_note(v___x_1634_);
v___x_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1636_, 0, v_msg_1574_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set_tag(v___x_1603_, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1636_);
v___x_1638_ = v___x_1603_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
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
lean_object* v___x_1658_; 
lean_dec_ref(v_env_1580_);
lean_dec(v_declHint_1575_);
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v_msg_1574_);
return v___x_1658_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1574_ = stack[0].m_obj;
lean_object* v_declHint_1575_ = stack[1].m_obj;
lean_object* v___y_1576_ = stack[2].m_obj;
lean_object* v_res_1659_;
v_res_1659_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_1574_, v_declHint_1575_, v___y_1576_);
stack->m_obj
 = v_res_1659_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_msg_1660_, lean_object* v_declHint_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_1660_, v_declHint_1661_, v___y_1662_);
lean_dec(v___y_1662_);
return v_res_1664_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(lean_object* v_msg_1665_, lean_object* v_declHint_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v___x_1673_; lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1683_; 
v___x_1673_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_1665_, v_declHint_1666_, v___y_1671_);
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1676_ = v___x_1673_;
v_isShared_1677_ = v_isSharedCheck_1683_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1683_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1678_ = l_Lean_unknownIdentifierMessageTag;
v___x_1679_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1678_);
lean_ctor_set(v___x_1679_, 1, v_a_1674_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 0, v___x_1679_);
v___x_1681_ = v___x_1676_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1665_ = stack[0].m_obj;
lean_object* v_declHint_1666_ = stack[1].m_obj;
lean_object* v___y_1667_ = stack[2].m_obj;
lean_object* v___y_1668_ = stack[3].m_obj;
lean_object* v___y_1669_ = stack[4].m_obj;
lean_object* v___y_1670_ = stack[5].m_obj;
lean_object* v___y_1671_ = stack[6].m_obj;
lean_object* v_res_1684_;
v_res_1684_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(v_msg_1665_, v_declHint_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
stack->m_obj
 = v_res_1684_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_msg_1685_, lean_object* v_declHint_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(v_msg_1685_, v_declHint_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec_ref(v___y_1687_);
return v_res_1693_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1694_, lean_object* v_msg_1695_, lean_object* v_declHint_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v___x_1703_; lean_object* v_a_1704_; lean_object* v___x_1705_; 
v___x_1703_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(v_msg_1695_, v_declHint_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref(v___x_1703_);
v___x_1705_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_1694_, v_a_1704_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
return v___x_1705_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1694_ = stack[0].m_obj;
lean_object* v_msg_1695_ = stack[1].m_obj;
lean_object* v_declHint_1696_ = stack[2].m_obj;
lean_object* v___y_1697_ = stack[3].m_obj;
lean_object* v___y_1698_ = stack[4].m_obj;
lean_object* v___y_1699_ = stack[5].m_obj;
lean_object* v___y_1700_ = stack[6].m_obj;
lean_object* v___y_1701_ = stack[7].m_obj;
lean_object* v_res_1706_;
v_res_1706_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1694_, v_msg_1695_, v_declHint_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
stack->m_obj
 = v_res_1706_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1707_, lean_object* v_msg_1708_, lean_object* v_declHint_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1707_, v_msg_1708_, v_declHint_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v_ref_1707_);
return v_res_1716_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__0));
v___x_1719_ = l_Lean_stringToMessageData(v___x_1718_);
return v___x_1719_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__2));
v___x_1722_ = l_Lean_stringToMessageData(v___x_1721_);
return v___x_1722_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(lean_object* v_ref_1723_, lean_object* v_constName_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v___x_1731_; uint8_t v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1731_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_1732_ = 0;
lean_inc(v_constName_1724_);
v___x_1733_ = l_Lean_MessageData_ofConstName(v_constName_1724_, v___x_1732_);
v___x_1734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1731_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
v___x_1735_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3);
v___x_1736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1734_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1723_, v___x_1736_, v_constName_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
return v___x_1737_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1723_ = stack[0].m_obj;
lean_object* v_constName_1724_ = stack[1].m_obj;
lean_object* v___y_1725_ = stack[2].m_obj;
lean_object* v___y_1726_ = stack[3].m_obj;
lean_object* v___y_1727_ = stack[4].m_obj;
lean_object* v___y_1728_ = stack[5].m_obj;
lean_object* v___y_1729_ = stack[6].m_obj;
lean_object* v_res_1738_;
v_res_1738_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1723_, v_constName_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
stack->m_obj
 = v_res_1738_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1739_, lean_object* v_constName_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1739_, v_constName_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v_ref_1739_);
return v_res_1747_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(lean_object* v_constName_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_ref_1755_; lean_object* v___x_1756_; 
v_ref_1755_ = lean_ctor_get(v___y_1752_, 2);
v___x_1756_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1755_, v_constName_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
return v___x_1756_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1748_ = stack[0].m_obj;
lean_object* v___y_1749_ = stack[1].m_obj;
lean_object* v___y_1750_ = stack[2].m_obj;
lean_object* v___y_1751_ = stack[3].m_obj;
lean_object* v___y_1752_ = stack[4].m_obj;
lean_object* v___y_1753_ = stack[5].m_obj;
lean_object* v_res_1757_;
v_res_1757_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
stack->m_obj
 = v_res_1757_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_constName_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec_ref(v___y_1759_);
return v_res_1765_;
}
}
lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(lean_object* v_constName_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v___x_1773_; lean_object* v_env_1774_; uint8_t v___x_1775_; lean_object* v___x_1776_; 
v___x_1773_ = lean_st_ref_get(v___y_1771_);
v_env_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc_ref(v_env_1774_);
lean_dec(v___x_1773_);
v___x_1775_ = 0;
lean_inc(v_constName_1766_);
v___x_1776_ = l_Lean_Environment_find_x3f(v_env_1774_, v_constName_1766_, v___x_1775_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v___x_1777_;
}
else
{
lean_object* v_val_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec(v_constName_1766_);
v_val_1778_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1776_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_val_1778_);
lean_dec(v___x_1776_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set_tag(v___x_1780_, 0);
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_val_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1766_ = stack[0].m_obj;
lean_object* v___y_1767_ = stack[1].m_obj;
lean_object* v___y_1768_ = stack[2].m_obj;
lean_object* v___y_1769_ = stack[3].m_obj;
lean_object* v___y_1770_ = stack[4].m_obj;
lean_object* v___y_1771_ = stack[5].m_obj;
lean_object* v_res_1786_;
v_res_1786_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(v_constName_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
stack->m_obj
 = v_res_1786_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1___boxed(lean_object* v_constName_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(v_constName_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec_ref(v___y_1788_);
return v_res_1794_;
}
}
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(lean_object* v_structName_1795_, lean_object* v_idx_1796_, lean_object* v_s_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___x_1816_; 
lean_inc(v_s_1797_);
v___x_1816_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_s_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1912_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1819_ = v___x_1816_;
v_isShared_1820_ = v_isSharedCheck_1912_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1816_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1912_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1821_ = l_Lean_Expr_headBeta(v_a_1817_);
v___x_1822_ = l_Lean_Expr_isErased(v___x_1821_);
if (v___x_1822_ == 0)
{
uint8_t v___x_1823_; 
v___x_1823_ = l_Lean_Expr_isAny(v___x_1821_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; 
lean_del_object(v___x_1819_);
v___x_1824_ = l_Lean_Expr_getAppFn(v___x_1821_);
if (lean_obj_tag(v___x_1824_) == 4)
{
lean_object* v_declName_1825_; lean_object* v_us_1826_; lean_object* v___x_1827_; lean_object* v_env_1828_; lean_object* v___x_1829_; 
v_declName_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_declName_1825_);
v_us_1826_ = lean_ctor_get(v___x_1824_, 1);
lean_inc(v_us_1826_);
lean_dec_ref_known(v___x_1824_, 2);
v___x_1827_ = lean_st_ref_get(v_a_1802_);
v_env_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc_ref(v_env_1828_);
lean_dec(v___x_1827_);
v___x_1829_ = l_Lean_Environment_find_x3f(v_env_1828_, v_declName_1825_, v___x_1823_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_dec(v_us_1826_);
lean_dec_ref(v___x_1821_);
v___y_1805_ = v_a_1798_;
v___y_1806_ = v_a_1799_;
v___y_1807_ = v_a_1800_;
v___y_1808_ = v_a_1801_;
v___y_1809_ = v_a_1802_;
goto v___jp_1804_;
}
else
{
lean_object* v_val_1830_; 
v_val_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_val_1830_);
lean_dec_ref_known(v___x_1829_, 1);
if (lean_obj_tag(v_val_1830_) == 5)
{
lean_object* v_val_1831_; lean_object* v_ctors_1832_; 
v_val_1831_ = lean_ctor_get(v_val_1830_, 0);
lean_inc_ref(v_val_1831_);
lean_dec_ref_known(v_val_1830_, 1);
v_ctors_1832_ = lean_ctor_get(v_val_1831_, 4);
lean_inc(v_ctors_1832_);
if (lean_obj_tag(v_ctors_1832_) == 1)
{
lean_object* v_tail_1833_; 
v_tail_1833_ = lean_ctor_get(v_ctors_1832_, 1);
if (lean_obj_tag(v_tail_1833_) == 0)
{
lean_object* v_numParams_1834_; lean_object* v_numIndices_1835_; lean_object* v_head_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1902_; 
v_numParams_1834_ = lean_ctor_get(v_val_1831_, 1);
lean_inc(v_numParams_1834_);
v_numIndices_1835_ = lean_ctor_get(v_val_1831_, 2);
lean_inc(v_numIndices_1835_);
lean_dec_ref(v_val_1831_);
v_head_1836_ = lean_ctor_get(v_ctors_1832_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_ctors_1832_);
if (v_isSharedCheck_1902_ == 0)
{
lean_object* v_unused_1903_; 
v_unused_1903_ = lean_ctor_get(v_ctors_1832_, 1);
lean_dec(v_unused_1903_);
v___x_1838_ = v_ctors_1832_;
v_isShared_1839_ = v_isSharedCheck_1902_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_head_1836_);
lean_dec(v_ctors_1832_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1902_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(v_head_1836_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref_known(v___x_1840_, 1);
if (lean_obj_tag(v_a_1841_) == 6)
{
lean_object* v_val_1842_; lean_object* v_dummy_1843_; lean_object* v_nargs_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v_val_1842_ = lean_ctor_get(v_a_1841_, 0);
lean_inc_ref(v_val_1842_);
lean_dec_ref_known(v_a_1841_, 1);
v_dummy_1843_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0);
v_nargs_1844_ = l_Lean_Expr_getAppNumArgs(v___x_1821_);
lean_inc(v_nargs_1844_);
v___x_1845_ = lean_mk_array(v_nargs_1844_, v_dummy_1843_);
v___x_1846_ = lean_unsigned_to_nat(1u);
v___x_1847_ = lean_nat_sub(v_nargs_1844_, v___x_1846_);
lean_dec(v_nargs_1844_);
v___x_1848_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1821_, v___x_1845_, v___x_1847_);
v___x_1849_ = lean_nat_add(v_numParams_1834_, v_numIndices_1835_);
lean_dec(v_numIndices_1835_);
v___x_1850_ = lean_array_get_size(v___x_1848_);
v___x_1851_ = lean_nat_dec_eq(v___x_1849_, v___x_1850_);
lean_dec(v___x_1849_);
if (v___x_1851_ == 0)
{
lean_dec_ref(v___x_1848_);
lean_dec_ref(v_val_1842_);
lean_del_object(v___x_1838_);
lean_dec(v_numParams_1834_);
lean_dec(v_us_1826_);
v___y_1805_ = v_a_1798_;
v___y_1806_ = v_a_1799_;
v___y_1807_ = v_a_1800_;
v___y_1808_ = v_a_1801_;
v___y_1809_ = v_a_1802_;
goto v___jp_1804_;
}
else
{
if (v___x_1823_ == 0)
{
lean_object* v_toConstantVal_1852_; lean_object* v_name_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v_toConstantVal_1852_ = lean_ctor_get(v_val_1842_, 0);
lean_inc_ref(v_toConstantVal_1852_);
lean_dec_ref(v_val_1842_);
v_name_1853_ = lean_ctor_get(v_toConstantVal_1852_, 0);
lean_inc(v_name_1853_);
lean_dec_ref(v_toConstantVal_1852_);
v___x_1854_ = l_Lean_mkConst(v_name_1853_, v_us_1826_);
v___x_1855_ = lean_unsigned_to_nat(0u);
v___x_1856_ = l_Array_toSubarray___redArg(v___x_1848_, v___x_1855_, v_numParams_1834_);
v___x_1857_ = l_Subarray_copy___redArg(v___x_1856_);
v___x_1858_ = l_Lean_mkAppN(v___x_1854_, v___x_1857_);
lean_dec_ref(v___x_1857_);
v___x_1859_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(v___x_1858_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref_known(v___x_1859_, 1);
v___x_1861_ = lean_box(0);
if (v_isShared_1839_ == 0)
{
lean_ctor_set_tag(v___x_1838_, 0);
lean_ctor_set(v___x_1838_, 1, v_a_1860_);
lean_ctor_set(v___x_1838_, 0, v___x_1861_);
v___x_1863_ = v___x_1838_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_a_1860_);
v___x_1863_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; 
lean_inc(v_structName_1795_);
lean_inc(v_s_1797_);
lean_inc(v_idx_1796_);
v___x_1864_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_idx_1796_, v_s_1797_, v_structName_1795_, v_idx_1796_, v___x_1855_, v___x_1863_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1884_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1867_ = v___x_1864_;
v_isShared_1868_ = v_isSharedCheck_1884_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1864_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1884_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v_fst_1869_; 
v_fst_1869_ = lean_ctor_get(v_a_1865_, 0);
if (lean_obj_tag(v_fst_1869_) == 0)
{
lean_object* v_snd_1870_; 
v_snd_1870_ = lean_ctor_get(v_a_1865_, 1);
lean_inc(v_snd_1870_);
lean_dec(v_a_1865_);
if (lean_obj_tag(v_snd_1870_) == 7)
{
lean_object* v_binderType_1871_; lean_object* v___x_1873_; 
lean_dec(v_s_1797_);
lean_dec(v_idx_1796_);
lean_dec(v_structName_1795_);
v_binderType_1871_ = lean_ctor_get(v_snd_1870_, 1);
lean_inc_ref(v_binderType_1871_);
lean_dec_ref_known(v_snd_1870_, 3);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v_binderType_1871_);
v___x_1873_ = v___x_1867_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_binderType_1871_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
else
{
uint8_t v___x_1875_; 
v___x_1875_ = l_Lean_Expr_isErased(v_snd_1870_);
lean_dec(v_snd_1870_);
if (v___x_1875_ == 0)
{
lean_del_object(v___x_1867_);
v___y_1805_ = v_a_1798_;
v___y_1806_ = v_a_1799_;
v___y_1807_ = v_a_1800_;
v___y_1808_ = v_a_1801_;
v___y_1809_ = v_a_1802_;
goto v___jp_1804_;
}
else
{
lean_object* v___x_1876_; lean_object* v___x_1878_; 
lean_dec(v_s_1797_);
lean_dec(v_idx_1796_);
lean_dec(v_structName_1795_);
v___x_1876_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v___x_1876_);
v___x_1878_ = v___x_1867_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
else
{
lean_object* v_val_1880_; lean_object* v___x_1882_; 
lean_inc_ref(v_fst_1869_);
lean_dec(v_a_1865_);
lean_dec(v_s_1797_);
lean_dec(v_idx_1796_);
lean_dec(v_structName_1795_);
v_val_1880_ = lean_ctor_get(v_fst_1869_, 0);
lean_inc(v_val_1880_);
lean_dec_ref_known(v_fst_1869_, 1);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v_val_1880_);
v___x_1882_ = v___x_1867_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_val_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v_s_1797_);
lean_dec(v_idx_1796_);
lean_dec(v_structName_1795_);
v_a_1885_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1864_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1864_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
else
{
lean_del_object(v___x_1838_);
lean_dec(v_s_1797_);
lean_dec(v_idx_1796_);
lean_dec(v_structName_1795_);
return v___x_1859_;
}
}
else
{
lean_dec_ref(v___x_1848_);
lean_dec_ref(v_val_1842_);
lean_del_object(v___x_1838_);
lean_dec(v_numParams_1834_);
lean_dec(v_us_1826_);
v___y_1805_ = v_a_1798_;
v___y_1806_ = v_a_1799_;
v___y_1807_ = v_a_1800_;
v___y_1808_ = v_a_1801_;
v___y_1809_ = v_a_1802_;
goto v___jp_1804_;
}
}
}
else
{
lean_dec(v_a_1841_);
lean_del_object(v___x_1838_);
lean_dec(v_numIndices_1835_);
lean_dec(v_numParams_1834_);
lean_dec(v_us_1826_);
lean_dec_ref(v___x_1821_);
v___y_1805_ = v_a_1798_;
v___y_1806_ = v_a_1799_;
v___y_1807_ = v_a_1800_;
v___y_1808_ = v_a_1801_;
v___y_1809_ = v_a_1802_;
goto v___jp_1804_;
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_del_object(v___x_1838_);
lean_dec(v_numIndices_1835_);
lean_dec(v_numParams_1834_);
lean_dec(v_us_1826_);
lean_dec_ref(v___x_1821_);
lean_dec(v_s_1797_);
lean_dec(v_idx_1796_);
lean_dec(v_structName_1795_);
v_a_1894_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1840_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1840_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1832_, 2);
lean_dec_ref(v_val_1831_);
lean_dec(v_us_1826_);
lean_dec_ref(v___x_1821_);
v___y_1805_ = v_a_1798_;
v___y_1806_ = v_a_1799_;
v___y_1807_ = v_a_1800_;
v___y_1808_ = v_a_1801_;
v___y_1809_ = v_a_1802_;
goto v___jp_1804_;
}
}
else
{
lean_dec(v_ctors_1832_);
lean_dec_ref(v_val_1831_);
lean_dec(v_us_1826_);
lean_dec_ref(v___x_1821_);
v___y_1805_ = v_a_1798_;
v___y_1806_ = v_a_1799_;
v___y_1807_ = v_a_1800_;
v___y_1808_ = v_a_1801_;
v___y_1809_ = v_a_1802_;
goto v___jp_1804_;
}
}
else
{
lean_dec(v_val_1830_);
lean_dec(v_us_1826_);
lean_dec_ref(v___x_1821_);
v___y_1805_ = v_a_1798_;
v___y_1806_ = v_a_1799_;
v___y_1807_ = v_a_1800_;
v___y_1808_ = v_a_1801_;
v___y_1809_ = v_a_1802_;
goto v___jp_1804_;
}
}
}
else
{
lean_dec_ref(v___x_1824_);
lean_dec_ref(v___x_1821_);
v___y_1805_ = v_a_1798_;
v___y_1806_ = v_a_1799_;
v___y_1807_ = v_a_1800_;
v___y_1808_ = v_a_1801_;
v___y_1809_ = v_a_1802_;
goto v___jp_1804_;
}
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1906_; 
lean_dec_ref(v___x_1821_);
lean_dec(v_s_1797_);
lean_dec(v_idx_1796_);
lean_dec(v_structName_1795_);
v___x_1904_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1904_);
v___x_1906_ = v___x_1819_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
else
{
lean_object* v___x_1908_; lean_object* v___x_1910_; 
lean_dec_ref(v___x_1821_);
lean_dec(v_s_1797_);
lean_dec(v_idx_1796_);
lean_dec(v_structName_1795_);
v___x_1908_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1908_);
v___x_1910_ = v___x_1819_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
else
{
lean_dec(v_s_1797_);
lean_dec(v_idx_1796_);
lean_dec(v_structName_1795_);
return v___x_1816_;
}
v___jp_1804_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1810_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
v___x_1811_ = l_Lean_mkFVar(v_s_1797_);
v___x_1812_ = l_Lean_mkProj(v_structName_1795_, v_idx_1796_, v___x_1811_);
v___x_1813_ = l_Lean_indentExpr(v___x_1812_);
v___x_1814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1810_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_1814_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
return v___x_1815_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_InferType_Pure_inferProjType_0interp(lean_interpreter_value* stack)
{
lean_object* v_structName_1795_ = stack[0].m_obj;
lean_object* v_idx_1796_ = stack[1].m_obj;
lean_object* v_s_1797_ = stack[2].m_obj;
lean_object* v_a_1798_ = stack[3].m_obj;
lean_object* v_a_1799_ = stack[4].m_obj;
lean_object* v_a_1800_ = stack[5].m_obj;
lean_object* v_a_1801_ = stack[6].m_obj;
lean_object* v_a_1802_ = stack[7].m_obj;
lean_object* v_res_1913_;
v_res_1913_ = l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(v_structName_1795_, v_idx_1796_, v_s_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_);
stack->m_obj
 = v_res_1913_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferProjType___boxed(lean_object* v_structName_1914_, lean_object* v_idx_1915_, lean_object* v_s_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(v_structName_1914_, v_idx_1915_, v_s_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
lean_dec(v_a_1921_);
lean_dec_ref(v_a_1920_);
lean_dec(v_a_1919_);
lean_dec_ref(v_a_1918_);
lean_dec_ref(v_a_1917_);
return v_res_1923_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2(lean_object* v_upperBound_1924_, lean_object* v_s_1925_, lean_object* v_structName_1926_, lean_object* v_idx_1927_, lean_object* v_inst_1928_, lean_object* v_R_1929_, lean_object* v_a_1930_, lean_object* v_b_1931_, lean_object* v_c_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_upperBound_1924_, v_s_1925_, v_structName_1926_, v_idx_1927_, v_a_1930_, v_b_1931_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
return v___x_1939_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1924_ = stack[0].m_obj;
lean_object* v_s_1925_ = stack[1].m_obj;
lean_object* v_structName_1926_ = stack[2].m_obj;
lean_object* v_idx_1927_ = stack[3].m_obj;
lean_object* v_a_1930_ = stack[6].m_obj;
lean_object* v_b_1931_ = stack[7].m_obj;
lean_object* v___y_1933_ = stack[9].m_obj;
lean_object* v___y_1934_ = stack[10].m_obj;
lean_object* v___y_1935_ = stack[11].m_obj;
lean_object* v___y_1936_ = stack[12].m_obj;
lean_object* v___y_1937_ = stack[13].m_obj;
lean_object* v_res_1940_;
v_res_1940_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2(v_upperBound_1924_, v_s_1925_, v_structName_1926_, v_idx_1927_, lean_box(0), lean_box(0), v_a_1930_, v_b_1931_, lean_box(0), v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
stack->m_obj
 = v_res_1940_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___boxed(lean_object* v_upperBound_1941_, lean_object* v_s_1942_, lean_object* v_structName_1943_, lean_object* v_idx_1944_, lean_object* v_inst_1945_, lean_object* v_R_1946_, lean_object* v_a_1947_, lean_object* v_b_1948_, lean_object* v_c_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2(v_upperBound_1941_, v_s_1942_, v_structName_1943_, v_idx_1944_, v_inst_1945_, v_R_1946_, v_a_1947_, v_b_1948_, v_c_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v_a_1947_);
lean_dec(v_upperBound_1941_);
return v_res_1956_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1(lean_object* v_00_u03b1_1957_, lean_object* v_constName_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
return v___x_1965_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1958_ = stack[1].m_obj;
lean_object* v___y_1959_ = stack[2].m_obj;
lean_object* v___y_1960_ = stack[3].m_obj;
lean_object* v___y_1961_ = stack[4].m_obj;
lean_object* v___y_1962_ = stack[5].m_obj;
lean_object* v___y_1963_ = stack[6].m_obj;
lean_object* v_res_1966_;
v_res_1966_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1(lean_box(0), v_constName_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
stack->m_obj
 = v_res_1966_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___boxed(lean_object* v_00_u03b1_1967_, lean_object* v_constName_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1(v_00_u03b1_1967_, v_constName_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___y_1969_);
return v_res_1975_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3(lean_object* v_upperBound_1976_, lean_object* v_s_1977_, lean_object* v_structName_1978_, lean_object* v_idx_1979_, lean_object* v_inst_1980_, lean_object* v_R_1981_, lean_object* v_a_1982_, lean_object* v_b_1983_, lean_object* v_c_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v___x_1991_; 
v___x_1991_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_1976_, v_s_1977_, v_structName_1978_, v_idx_1979_, v_a_1982_, v_b_1983_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
return v___x_1991_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1976_ = stack[0].m_obj;
lean_object* v_s_1977_ = stack[1].m_obj;
lean_object* v_structName_1978_ = stack[2].m_obj;
lean_object* v_idx_1979_ = stack[3].m_obj;
lean_object* v_a_1982_ = stack[6].m_obj;
lean_object* v_b_1983_ = stack[7].m_obj;
lean_object* v___y_1985_ = stack[9].m_obj;
lean_object* v___y_1986_ = stack[10].m_obj;
lean_object* v___y_1987_ = stack[11].m_obj;
lean_object* v___y_1988_ = stack[12].m_obj;
lean_object* v___y_1989_ = stack[13].m_obj;
lean_object* v_res_1992_;
v_res_1992_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3(v_upperBound_1976_, v_s_1977_, v_structName_1978_, v_idx_1979_, lean_box(0), lean_box(0), v_a_1982_, v_b_1983_, lean_box(0), v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
stack->m_obj
 = v_res_1992_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___boxed(lean_object* v_upperBound_1993_, lean_object* v_s_1994_, lean_object* v_structName_1995_, lean_object* v_idx_1996_, lean_object* v_inst_1997_, lean_object* v_R_1998_, lean_object* v_a_1999_, lean_object* v_b_2000_, lean_object* v_c_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3(v_upperBound_1993_, v_s_1994_, v_structName_1995_, v_idx_1996_, v_inst_1997_, v_R_1998_, v_a_1999_, v_b_2000_, v_c_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v_upperBound_1993_);
return v_res_2008_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_2009_, lean_object* v_ref_2010_, lean_object* v_constName_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_2010_, v_constName_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
return v___x_2018_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2010_ = stack[1].m_obj;
lean_object* v_constName_2011_ = stack[2].m_obj;
lean_object* v___y_2012_ = stack[3].m_obj;
lean_object* v___y_2013_ = stack[4].m_obj;
lean_object* v___y_2014_ = stack[5].m_obj;
lean_object* v___y_2015_ = stack[6].m_obj;
lean_object* v___y_2016_ = stack[7].m_obj;
lean_object* v_res_2019_;
v_res_2019_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2(lean_box(0), v_ref_2010_, v_constName_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
stack->m_obj
 = v_res_2019_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2020_, lean_object* v_ref_2021_, lean_object* v_constName_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2(v_00_u03b1_2020_, v_ref_2021_, v_constName_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v_ref_2021_);
return v_res_2029_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_2030_, lean_object* v_ref_2031_, lean_object* v_msg_2032_, lean_object* v_declHint_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_2031_, v_msg_2032_, v_declHint_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
return v___x_2040_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2031_ = stack[1].m_obj;
lean_object* v_msg_2032_ = stack[2].m_obj;
lean_object* v_declHint_2033_ = stack[3].m_obj;
lean_object* v___y_2034_ = stack[4].m_obj;
lean_object* v___y_2035_ = stack[5].m_obj;
lean_object* v___y_2036_ = stack[6].m_obj;
lean_object* v___y_2037_ = stack[7].m_obj;
lean_object* v___y_2038_ = stack[8].m_obj;
lean_object* v_res_2041_;
v_res_2041_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4(lean_box(0), v_ref_2031_, v_msg_2032_, v_declHint_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
stack->m_obj
 = v_res_2041_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2042_, lean_object* v_ref_2043_, lean_object* v_msg_2044_, lean_object* v_declHint_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4(v_00_u03b1_2042_, v_ref_2043_, v_msg_2044_, v_declHint_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v_ref_2043_);
return v_res_2052_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msg_2053_, lean_object* v_declHint_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v___x_2061_; 
v___x_2061_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_2053_, v_declHint_2054_, v___y_2059_);
return v___x_2061_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2053_ = stack[0].m_obj;
lean_object* v_declHint_2054_ = stack[1].m_obj;
lean_object* v___y_2055_ = stack[2].m_obj;
lean_object* v___y_2056_ = stack[3].m_obj;
lean_object* v___y_2057_ = stack[4].m_obj;
lean_object* v___y_2058_ = stack[5].m_obj;
lean_object* v___y_2059_ = stack[6].m_obj;
lean_object* v_res_2062_;
v_res_2062_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_2053_, v_declHint_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
stack->m_obj
 = v_res_2062_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_2063_, lean_object* v_declHint_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_2063_, v_declHint_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec_ref(v___y_2065_);
return v_res_2071_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b1_2072_, lean_object* v_ref_2073_, lean_object* v_msg_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_2073_, v_msg_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
return v___x_2081_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2073_ = stack[1].m_obj;
lean_object* v_msg_2074_ = stack[2].m_obj;
lean_object* v___y_2075_ = stack[3].m_obj;
lean_object* v___y_2076_ = stack[4].m_obj;
lean_object* v___y_2077_ = stack[5].m_obj;
lean_object* v___y_2078_ = stack[6].m_obj;
lean_object* v___y_2079_ = stack[7].m_obj;
lean_object* v_res_2082_;
v_res_2082_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7(lean_box(0), v_ref_2073_, v_msg_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
stack->m_obj
 = v_res_2082_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b1_2083_, lean_object* v_ref_2084_, lean_object* v_msg_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7(v_00_u03b1_2083_, v_ref_2084_, v_msg_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v_ref_2084_);
return v_res_2092_;
}
}
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(lean_object* v_e_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_){
_start:
{
switch(lean_obj_tag(v_e_2093_))
{
case 0:
{
lean_object* v_value_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2108_; 
v_value_2100_ = lean_ctor_get(v_e_2093_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_e_2093_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2102_ = v_e_2093_;
v_isShared_2103_ = v_isSharedCheck_2108_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_value_2100_);
lean_dec(v_e_2093_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2108_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2104_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType(v_value_2100_);
lean_dec_ref(v_value_2100_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2104_);
v___x_2106_ = v___x_2102_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
case 1:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
return v___x_2110_;
}
case 2:
{
lean_object* v_typeName_2111_; lean_object* v_idx_2112_; lean_object* v_struct_2113_; lean_object* v___x_2114_; 
v_typeName_2111_ = lean_ctor_get(v_e_2093_, 0);
lean_inc(v_typeName_2111_);
v_idx_2112_ = lean_ctor_get(v_e_2093_, 1);
lean_inc(v_idx_2112_);
v_struct_2113_ = lean_ctor_get(v_e_2093_, 2);
lean_inc(v_struct_2113_);
lean_dec_ref_known(v_e_2093_, 3);
v___x_2114_ = l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(v_typeName_2111_, v_idx_2112_, v_struct_2113_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_);
return v___x_2114_;
}
case 3:
{
lean_object* v_declName_2115_; lean_object* v_us_2116_; lean_object* v_args_2117_; lean_object* v___x_2118_; 
v_declName_2115_ = lean_ctor_get(v_e_2093_, 0);
lean_inc(v_declName_2115_);
v_us_2116_ = lean_ctor_get(v_e_2093_, 1);
lean_inc(v_us_2116_);
v_args_2117_ = lean_ctor_get(v_e_2093_, 2);
lean_inc_ref(v_args_2117_);
lean_dec_ref_known(v_e_2093_, 3);
v___x_2118_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(v_declName_2115_, v_us_2116_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2120_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2118_, 1);
v___x_2120_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2119_, v_args_2117_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_);
return v___x_2120_;
}
else
{
lean_dec_ref(v_args_2117_);
return v___x_2118_;
}
}
default: 
{
lean_object* v_fvarId_2121_; lean_object* v_args_2122_; lean_object* v___x_2123_; 
v_fvarId_2121_ = lean_ctor_get(v_e_2093_, 0);
lean_inc(v_fvarId_2121_);
v_args_2122_ = lean_ctor_get(v_e_2093_, 1);
lean_inc_ref(v_args_2122_);
lean_dec_ref_known(v_e_2093_, 2);
v___x_2123_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_fvarId_2121_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2125_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2123_, 1);
v___x_2125_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2124_, v_args_2122_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_);
return v___x_2125_;
}
else
{
lean_dec_ref(v_args_2122_);
return v___x_2123_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2093_ = stack[0].m_obj;
lean_object* v_a_2094_ = stack[1].m_obj;
lean_object* v_a_2095_ = stack[2].m_obj;
lean_object* v_a_2096_ = stack[3].m_obj;
lean_object* v_a_2097_ = stack[4].m_obj;
lean_object* v_a_2098_ = stack[5].m_obj;
lean_object* v_res_2126_;
v_res_2126_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(v_e_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_);
stack->m_obj
 = v_res_2126_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType___boxed(lean_object* v_e_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(v_e_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
lean_dec(v_a_2130_);
lean_dec_ref(v_a_2129_);
lean_dec_ref(v_a_2128_);
return v_res_2134_;
}
}
lean_object* l_Lean_Compiler_LCNF_inferType(lean_object* v_e_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2141_ = lean_unsigned_to_nat(32u);
v___x_2142_ = lean_mk_empty_array_with_capacity(v___x_2141_);
lean_dec_ref(v___x_2142_);
v___x_2143_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2144_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_e_2135_, v___x_2143_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_);
return v___x_2144_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_inferType_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2135_ = stack[0].m_obj;
lean_object* v_a_2136_ = stack[1].m_obj;
lean_object* v_a_2137_ = stack[2].m_obj;
lean_object* v_a_2138_ = stack[3].m_obj;
lean_object* v_a_2139_ = stack[4].m_obj;
lean_object* v_res_2145_;
v_res_2145_ = l_Lean_Compiler_LCNF_inferType(v_e_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_);
stack->m_obj
 = v_res_2145_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType___boxed(lean_object* v_e_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Lean_Compiler_LCNF_inferType(v_e_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
return v_res_2152_;
}
}
lean_object* l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(lean_object* v_msg_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v___x_2159_; lean_object* v_toApplicative_2160_; lean_object* v_toFunctor_2161_; lean_object* v_toSeq_2162_; lean_object* v_toSeqLeft_2163_; lean_object* v_toSeqRight_2164_; lean_object* v___f_2165_; lean_object* v___f_2166_; lean_object* v___f_2167_; lean_object* v___f_2168_; lean_object* v___x_2169_; lean_object* v___f_2170_; lean_object* v___f_2171_; lean_object* v___f_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___f_2178_; lean_object* v___x_148__overap_2179_; lean_object* v___x_2180_; 
v___x_2159_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_2160_ = lean_ctor_get(v___x_2159_, 0);
v_toFunctor_2161_ = lean_ctor_get(v_toApplicative_2160_, 0);
v_toSeq_2162_ = lean_ctor_get(v_toApplicative_2160_, 2);
v_toSeqLeft_2163_ = lean_ctor_get(v_toApplicative_2160_, 3);
v_toSeqRight_2164_ = lean_ctor_get(v_toApplicative_2160_, 4);
v___f_2165_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_2166_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2161_, 2);
v___f_2167_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2167_, 0, v_toFunctor_2161_);
v___f_2168_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2168_, 0, v_toFunctor_2161_);
v___x_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___f_2167_);
lean_ctor_set(v___x_2169_, 1, v___f_2168_);
lean_inc(v_toSeqRight_2164_);
v___f_2170_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2170_, 0, v_toSeqRight_2164_);
lean_inc(v_toSeqLeft_2163_);
v___f_2171_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2171_, 0, v_toSeqLeft_2163_);
lean_inc(v_toSeq_2162_);
v___f_2172_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2172_, 0, v_toSeq_2162_);
v___x_2173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2169_);
lean_ctor_set(v___x_2173_, 1, v___f_2165_);
lean_ctor_set(v___x_2173_, 2, v___f_2172_);
lean_ctor_set(v___x_2173_, 3, v___f_2171_);
lean_ctor_set(v___x_2173_, 4, v___f_2170_);
v___x_2174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
lean_ctor_set(v___x_2174_, 1, v___f_2166_);
v___x_2175_ = l_StateRefT_x27_instMonad___redArg(v___x_2174_);
v___x_2176_ = l_Lean_instInhabitedExpr;
v___x_2177_ = l_instInhabitedOfMonad___redArg(v___x_2175_, v___x_2176_);
v___f_2178_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2178_, 0, v___x_2177_);
v___x_148__overap_2179_ = lean_panic_fn_borrowed(v___f_2178_, v_msg_2153_);
lean_dec_ref(v___f_2178_);
lean_inc(v___y_2157_);
lean_inc_ref(v___y_2156_);
lean_inc(v___y_2155_);
lean_inc_ref(v___y_2154_);
v___x_2180_ = lean_apply_5(v___x_148__overap_2179_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, lean_box(0));
return v___x_2180_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2153_ = stack[0].m_obj;
lean_object* v___y_2154_ = stack[1].m_obj;
lean_object* v___y_2155_ = stack[2].m_obj;
lean_object* v___y_2156_ = stack[3].m_obj;
lean_object* v___y_2157_ = stack[4].m_obj;
lean_object* v_res_2181_;
v_res_2181_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v_msg_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
stack->m_obj
 = v_res_2181_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0___boxed(lean_object* v_msg_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v_msg_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
return v_res_2188_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inferAppType___closed__2(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2191_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2192_ = lean_unsigned_to_nat(15u);
v___x_2193_ = lean_unsigned_to_nat(258u);
v___x_2194_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__0));
v___x_2195_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2196_ = l_mkPanicMessageWithDecl(v___x_2195_, v___x_2194_, v___x_2193_, v___x_2192_, v___x_2191_);
return v___x_2196_;
}
}
lean_object* l_Lean_Compiler_LCNF_inferAppType(uint8_t v_pu_2197_, lean_object* v_fnType_2198_, lean_object* v_args_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_){
_start:
{
if (v_pu_2197_ == 0)
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2206_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_fnType_2198_, v_args_2199_, v___x_2205_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_);
return v___x_2206_;
}
else
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_dec_ref(v_args_2199_);
lean_dec_ref(v_fnType_2198_);
v___x_2207_ = lean_obj_once(&l_Lean_Compiler_LCNF_inferAppType___closed__2, &l_Lean_Compiler_LCNF_inferAppType___closed__2_once, _init_l_Lean_Compiler_LCNF_inferAppType___closed__2);
v___x_2208_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2207_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_);
return v___x_2208_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_inferAppType_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2197_ = stack[0].m_num;
lean_object* v_fnType_2198_ = stack[1].m_obj;
lean_object* v_args_2199_ = stack[2].m_obj;
lean_object* v_a_2200_ = stack[3].m_obj;
lean_object* v_a_2201_ = stack[4].m_obj;
lean_object* v_a_2202_ = stack[5].m_obj;
lean_object* v_a_2203_ = stack[6].m_obj;
lean_object* v_res_2209_;
v_res_2209_ = l_Lean_Compiler_LCNF_inferAppType(v_pu_2197_, v_fnType_2198_, v_args_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_);
stack->m_obj
 = v_res_2209_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType___boxed(lean_object* v_pu_2210_, lean_object* v_fnType_2211_, lean_object* v_args_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_){
_start:
{
uint8_t v_pu_boxed_2218_; lean_object* v_res_2219_; 
v_pu_boxed_2218_ = lean_unbox(v_pu_2210_);
v_res_2219_ = l_Lean_Compiler_LCNF_inferAppType(v_pu_boxed_2218_, v_fnType_2211_, v_args_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
return v_res_2219_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Arg_inferType___closed__1(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2221_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2222_ = lean_unsigned_to_nat(15u);
v___x_2223_ = lean_unsigned_to_nat(263u);
v___x_2224_ = ((lean_object*)(l_Lean_Compiler_LCNF_Arg_inferType___closed__0));
v___x_2225_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2226_ = l_mkPanicMessageWithDecl(v___x_2225_, v___x_2224_, v___x_2223_, v___x_2222_, v___x_2221_);
return v___x_2226_;
}
}
lean_object* l_Lean_Compiler_LCNF_Arg_inferType(uint8_t v_pu_2227_, lean_object* v_arg_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
if (v_pu_2227_ == 0)
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2235_ = l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(v_arg_2228_, v___x_2234_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
return v___x_2235_;
}
else
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
lean_dec(v_arg_2228_);
v___x_2236_ = lean_obj_once(&l_Lean_Compiler_LCNF_Arg_inferType___closed__1, &l_Lean_Compiler_LCNF_Arg_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_Arg_inferType___closed__1);
v___x_2237_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2236_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
return v___x_2237_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Arg_inferType_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2227_ = stack[0].m_num;
lean_object* v_arg_2228_ = stack[1].m_obj;
lean_object* v_a_2229_ = stack[2].m_obj;
lean_object* v_a_2230_ = stack[3].m_obj;
lean_object* v_a_2231_ = stack[4].m_obj;
lean_object* v_a_2232_ = stack[5].m_obj;
lean_object* v_res_2238_;
v_res_2238_ = l_Lean_Compiler_LCNF_Arg_inferType(v_pu_2227_, v_arg_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
stack->m_obj
 = v_res_2238_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType___boxed(lean_object* v_pu_2239_, lean_object* v_arg_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
uint8_t v_pu_boxed_2246_; lean_object* v_res_2247_; 
v_pu_boxed_2246_ = lean_unbox(v_pu_2239_);
v_res_2247_ = l_Lean_Compiler_LCNF_Arg_inferType(v_pu_boxed_2246_, v_arg_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
lean_dec(v_a_2244_);
lean_dec_ref(v_a_2243_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
return v_res_2247_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LetValue_inferType___closed__1(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2249_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2250_ = lean_unsigned_to_nat(15u);
v___x_2251_ = lean_unsigned_to_nat(268u);
v___x_2252_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_inferType___closed__0));
v___x_2253_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2254_ = l_mkPanicMessageWithDecl(v___x_2253_, v___x_2252_, v___x_2251_, v___x_2250_, v___x_2249_);
return v___x_2254_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(uint8_t v_pu_2255_, lean_object* v_e_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_){
_start:
{
if (v_pu_2255_ == 0)
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2262_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2263_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(v_e_2256_, v___x_2262_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
return v___x_2263_;
}
else
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
lean_dec(v_e_2256_);
v___x_2264_ = lean_obj_once(&l_Lean_Compiler_LCNF_LetValue_inferType___closed__1, &l_Lean_Compiler_LCNF_LetValue_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_LetValue_inferType___closed__1);
v___x_2265_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2264_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
return v___x_2265_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetValue_inferType_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2255_ = stack[0].m_num;
lean_object* v_e_2256_ = stack[1].m_obj;
lean_object* v_a_2257_ = stack[2].m_obj;
lean_object* v_a_2258_ = stack[3].m_obj;
lean_object* v_a_2259_ = stack[4].m_obj;
lean_object* v_a_2260_ = stack[5].m_obj;
lean_object* v_res_2266_;
v_res_2266_ = l_Lean_Compiler_LCNF_LetValue_inferType(v_pu_2255_, v_e_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
stack->m_obj
 = v_res_2266_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType___boxed(lean_object* v_pu_2267_, lean_object* v_e_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_){
_start:
{
uint8_t v_pu_boxed_2274_; lean_object* v_res_2275_; 
v_pu_boxed_2274_ = lean_unbox(v_pu_2267_);
v_res_2275_ = l_Lean_Compiler_LCNF_LetValue_inferType(v_pu_boxed_2274_, v_e_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
lean_dec(v_a_2272_);
lean_dec_ref(v_a_2271_);
lean_dec(v_a_2270_);
lean_dec_ref(v_a_2269_);
return v_res_2275_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_inferType___closed__1(void){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2277_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2278_ = lean_unsigned_to_nat(15u);
v___x_2279_ = lean_unsigned_to_nat(279u);
v___x_2280_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_inferType___closed__0));
v___x_2281_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2282_ = l_mkPanicMessageWithDecl(v___x_2281_, v___x_2280_, v___x_2279_, v___x_2278_, v___x_2277_);
return v___x_2282_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t v_pu_2283_, lean_object* v_code_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_){
_start:
{
if (v_pu_2283_ == 0)
{
switch(lean_obj_tag(v_code_2284_))
{
case 3:
{
lean_object* v_fvarId_2290_; lean_object* v_args_2291_; lean_object* v___x_2292_; 
v_fvarId_2290_ = lean_ctor_get(v_code_2284_, 0);
lean_inc(v_fvarId_2290_);
v_args_2291_ = lean_ctor_get(v_code_2284_, 1);
lean_inc_ref(v_args_2291_);
lean_dec_ref_known(v_code_2284_, 2);
v___x_2292_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2290_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v___x_2292_, 1);
v___x_2294_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2295_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2293_, v_args_2291_, v___x_2294_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
return v___x_2295_;
}
else
{
lean_dec_ref(v_args_2291_);
return v___x_2292_;
}
}
case 4:
{
lean_object* v_cases_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2304_; 
v_cases_2296_ = lean_ctor_get(v_code_2284_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v_code_2284_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2298_ = v_code_2284_;
v_isShared_2299_ = v_isSharedCheck_2304_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_cases_2296_);
lean_dec(v_code_2284_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2304_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v_resultType_2300_; lean_object* v___x_2302_; 
v_resultType_2300_ = lean_ctor_get(v_cases_2296_, 1);
lean_inc_ref(v_resultType_2300_);
lean_dec_ref(v_cases_2296_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set_tag(v___x_2298_, 0);
lean_ctor_set(v___x_2298_, 0, v_resultType_2300_);
v___x_2302_ = v___x_2298_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_resultType_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
case 5:
{
lean_object* v_fvarId_2305_; lean_object* v___x_2306_; 
v_fvarId_2305_ = lean_ctor_get(v_code_2284_, 0);
lean_inc(v_fvarId_2305_);
lean_dec_ref_known(v_code_2284_, 1);
v___x_2306_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2305_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
return v___x_2306_;
}
case 6:
{
lean_object* v_type_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
v_type_2307_ = lean_ctor_get(v_code_2284_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v_code_2284_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v_code_2284_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_type_2307_);
lean_dec(v_code_2284_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
lean_ctor_set_tag(v___x_2309_, 0);
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_type_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
default: 
{
lean_object* v_k_2315_; 
v_k_2315_ = lean_ctor_get(v_code_2284_, 1);
lean_inc_ref(v_k_2315_);
lean_dec_ref(v_code_2284_);
v_code_2284_ = v_k_2315_;
goto _start;
}
}
}
else
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
lean_dec_ref(v_code_2284_);
v___x_2317_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_inferType___closed__1, &l_Lean_Compiler_LCNF_Code_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_Code_inferType___closed__1);
v___x_2318_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2317_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
return v___x_2318_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_inferType_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2283_ = stack[0].m_num;
lean_object* v_code_2284_ = stack[1].m_obj;
lean_object* v_a_2285_ = stack[2].m_obj;
lean_object* v_a_2286_ = stack[3].m_obj;
lean_object* v_a_2287_ = stack[4].m_obj;
lean_object* v_a_2288_ = stack[5].m_obj;
lean_object* v_res_2319_;
v_res_2319_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2283_, v_code_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
stack->m_obj
 = v_res_2319_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType___boxed(lean_object* v_pu_2320_, lean_object* v_code_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_){
_start:
{
uint8_t v_pu_boxed_2327_; lean_object* v_res_2328_; 
v_pu_boxed_2327_ = lean_unbox(v_pu_2320_);
v_res_2328_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_boxed_2327_, v_code_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
lean_dec(v_a_2325_);
lean_dec_ref(v_a_2324_);
lean_dec(v_a_2323_);
lean_dec_ref(v_a_2322_);
return v_res_2328_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg(uint8_t v_pu_2329_, lean_object* v_code_2330_, lean_object* v_h__1_2331_, lean_object* v_h__2_2332_){
_start:
{
if (v_pu_2329_ == 0)
{
lean_object* v___x_2333_; 
lean_dec(v_h__2_2332_);
v___x_2333_ = lean_apply_1(v_h__1_2331_, v_code_2330_);
return v___x_2333_;
}
else
{
lean_object* v___x_2334_; 
lean_dec(v_h__1_2331_);
v___x_2334_ = lean_apply_1(v_h__2_2332_, v_code_2330_);
return v___x_2334_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2329_ = stack[0].m_num;
lean_object* v_code_2330_ = stack[1].m_obj;
lean_object* v_h__1_2331_ = stack[2].m_obj;
lean_object* v_h__2_2332_ = stack[3].m_obj;
lean_object* v_res_2335_;
v_res_2335_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg(v_pu_2329_, v_code_2330_, v_h__1_2331_, v_h__2_2332_);
stack->m_obj
 = v_res_2335_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg___boxed(lean_object* v_pu_2336_, lean_object* v_code_2337_, lean_object* v_h__1_2338_, lean_object* v_h__2_2339_){
_start:
{
uint8_t v_pu_32__boxed_2340_; lean_object* v_res_2341_; 
v_pu_32__boxed_2340_ = lean_unbox(v_pu_2336_);
v_res_2341_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg(v_pu_32__boxed_2340_, v_code_2337_, v_h__1_2338_, v_h__2_2339_);
return v_res_2341_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter(lean_object* v_motive_2342_, uint8_t v_pu_2343_, lean_object* v_code_2344_, lean_object* v_h__1_2345_, lean_object* v_h__2_2346_){
_start:
{
if (v_pu_2343_ == 0)
{
lean_object* v___x_2347_; 
lean_dec(v_h__2_2346_);
v___x_2347_ = lean_apply_1(v_h__1_2345_, v_code_2344_);
return v___x_2347_;
}
else
{
lean_object* v___x_2348_; 
lean_dec(v_h__1_2345_);
v___x_2348_ = lean_apply_1(v_h__2_2346_, v_code_2344_);
return v___x_2348_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2343_ = stack[1].m_num;
lean_object* v_code_2344_ = stack[2].m_obj;
lean_object* v_h__1_2345_ = stack[3].m_obj;
lean_object* v_h__2_2346_ = stack[4].m_obj;
lean_object* v_res_2349_;
v_res_2349_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter(lean_box(0), v_pu_2343_, v_code_2344_, v_h__1_2345_, v_h__2_2346_);
stack->m_obj
 = v_res_2349_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___boxed(lean_object* v_motive_2350_, lean_object* v_pu_2351_, lean_object* v_code_2352_, lean_object* v_h__1_2353_, lean_object* v_h__2_2354_){
_start:
{
uint8_t v_pu_43__boxed_2355_; lean_object* v_res_2356_; 
v_pu_43__boxed_2355_ = lean_unbox(v_pu_2351_);
v_res_2356_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter(v_motive_2350_, v_pu_43__boxed_2355_, v_code_2352_, v_h__1_2353_, v_h__2_2354_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__1_splitter___redArg(lean_object* v_code_2357_, lean_object* v_h__1_2358_, lean_object* v_h__2_2359_, lean_object* v_h__3_2360_, lean_object* v_h__4_2361_, lean_object* v_h__5_2362_, lean_object* v_h__6_2363_, lean_object* v_h__7_2364_){
_start:
{
switch(lean_obj_tag(v_code_2357_))
{
case 0:
{
lean_object* v_decl_2365_; lean_object* v_k_2366_; lean_object* v___x_2367_; 
lean_dec(v_h__7_2364_);
lean_dec(v_h__6_2363_);
lean_dec(v_h__5_2362_);
lean_dec(v_h__4_2361_);
lean_dec(v_h__3_2360_);
lean_dec(v_h__2_2359_);
v_decl_2365_ = lean_ctor_get(v_code_2357_, 0);
lean_inc_ref(v_decl_2365_);
v_k_2366_ = lean_ctor_get(v_code_2357_, 1);
lean_inc_ref(v_k_2366_);
lean_dec_ref_known(v_code_2357_, 2);
v___x_2367_ = lean_apply_2(v_h__1_2358_, v_decl_2365_, v_k_2366_);
return v___x_2367_;
}
case 1:
{
lean_object* v_decl_2368_; lean_object* v_k_2369_; lean_object* v___x_2370_; 
lean_dec(v_h__7_2364_);
lean_dec(v_h__6_2363_);
lean_dec(v_h__5_2362_);
lean_dec(v_h__4_2361_);
lean_dec(v_h__3_2360_);
lean_dec(v_h__1_2358_);
v_decl_2368_ = lean_ctor_get(v_code_2357_, 0);
lean_inc_ref(v_decl_2368_);
v_k_2369_ = lean_ctor_get(v_code_2357_, 1);
lean_inc_ref(v_k_2369_);
lean_dec_ref_known(v_code_2357_, 2);
v___x_2370_ = lean_apply_3(v_h__2_2359_, v_decl_2368_, v_k_2369_, lean_box(0));
return v___x_2370_;
}
case 2:
{
lean_object* v_decl_2371_; lean_object* v_k_2372_; lean_object* v___x_2373_; 
lean_dec(v_h__7_2364_);
lean_dec(v_h__6_2363_);
lean_dec(v_h__5_2362_);
lean_dec(v_h__4_2361_);
lean_dec(v_h__2_2359_);
lean_dec(v_h__1_2358_);
v_decl_2371_ = lean_ctor_get(v_code_2357_, 0);
lean_inc_ref(v_decl_2371_);
v_k_2372_ = lean_ctor_get(v_code_2357_, 1);
lean_inc_ref(v_k_2372_);
lean_dec_ref_known(v_code_2357_, 2);
v___x_2373_ = lean_apply_2(v_h__3_2360_, v_decl_2371_, v_k_2372_);
return v___x_2373_;
}
case 3:
{
lean_object* v_fvarId_2374_; lean_object* v_args_2375_; lean_object* v___x_2376_; 
lean_dec(v_h__7_2364_);
lean_dec(v_h__6_2363_);
lean_dec(v_h__4_2361_);
lean_dec(v_h__3_2360_);
lean_dec(v_h__2_2359_);
lean_dec(v_h__1_2358_);
v_fvarId_2374_ = lean_ctor_get(v_code_2357_, 0);
lean_inc(v_fvarId_2374_);
v_args_2375_ = lean_ctor_get(v_code_2357_, 1);
lean_inc_ref(v_args_2375_);
lean_dec_ref_known(v_code_2357_, 2);
v___x_2376_ = lean_apply_2(v_h__5_2362_, v_fvarId_2374_, v_args_2375_);
return v___x_2376_;
}
case 4:
{
lean_object* v_cases_2377_; lean_object* v___x_2378_; 
lean_dec(v_h__6_2363_);
lean_dec(v_h__5_2362_);
lean_dec(v_h__4_2361_);
lean_dec(v_h__3_2360_);
lean_dec(v_h__2_2359_);
lean_dec(v_h__1_2358_);
v_cases_2377_ = lean_ctor_get(v_code_2357_, 0);
lean_inc_ref(v_cases_2377_);
lean_dec_ref_known(v_code_2357_, 1);
v___x_2378_ = lean_apply_1(v_h__7_2364_, v_cases_2377_);
return v___x_2378_;
}
case 5:
{
lean_object* v_fvarId_2379_; lean_object* v___x_2380_; 
lean_dec(v_h__7_2364_);
lean_dec(v_h__6_2363_);
lean_dec(v_h__5_2362_);
lean_dec(v_h__3_2360_);
lean_dec(v_h__2_2359_);
lean_dec(v_h__1_2358_);
v_fvarId_2379_ = lean_ctor_get(v_code_2357_, 0);
lean_inc(v_fvarId_2379_);
lean_dec_ref_known(v_code_2357_, 1);
v___x_2380_ = lean_apply_1(v_h__4_2361_, v_fvarId_2379_);
return v___x_2380_;
}
default: 
{
lean_object* v_type_2381_; lean_object* v___x_2382_; 
lean_dec(v_h__7_2364_);
lean_dec(v_h__5_2362_);
lean_dec(v_h__4_2361_);
lean_dec(v_h__3_2360_);
lean_dec(v_h__2_2359_);
lean_dec(v_h__1_2358_);
v_type_2381_ = lean_ctor_get(v_code_2357_, 0);
lean_inc_ref(v_type_2381_);
lean_dec_ref_known(v_code_2357_, 1);
v___x_2382_ = lean_apply_1(v_h__6_2363_, v_type_2381_);
return v___x_2382_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__1_splitter(lean_object* v_motive_2383_, lean_object* v_code_2384_, lean_object* v_h__1_2385_, lean_object* v_h__2_2386_, lean_object* v_h__3_2387_, lean_object* v_h__4_2388_, lean_object* v_h__5_2389_, lean_object* v_h__6_2390_, lean_object* v_h__7_2391_){
_start:
{
switch(lean_obj_tag(v_code_2384_))
{
case 0:
{
lean_object* v_decl_2392_; lean_object* v_k_2393_; lean_object* v___x_2394_; 
lean_dec(v_h__7_2391_);
lean_dec(v_h__6_2390_);
lean_dec(v_h__5_2389_);
lean_dec(v_h__4_2388_);
lean_dec(v_h__3_2387_);
lean_dec(v_h__2_2386_);
v_decl_2392_ = lean_ctor_get(v_code_2384_, 0);
lean_inc_ref(v_decl_2392_);
v_k_2393_ = lean_ctor_get(v_code_2384_, 1);
lean_inc_ref(v_k_2393_);
lean_dec_ref_known(v_code_2384_, 2);
v___x_2394_ = lean_apply_2(v_h__1_2385_, v_decl_2392_, v_k_2393_);
return v___x_2394_;
}
case 1:
{
lean_object* v_decl_2395_; lean_object* v_k_2396_; lean_object* v___x_2397_; 
lean_dec(v_h__7_2391_);
lean_dec(v_h__6_2390_);
lean_dec(v_h__5_2389_);
lean_dec(v_h__4_2388_);
lean_dec(v_h__3_2387_);
lean_dec(v_h__1_2385_);
v_decl_2395_ = lean_ctor_get(v_code_2384_, 0);
lean_inc_ref(v_decl_2395_);
v_k_2396_ = lean_ctor_get(v_code_2384_, 1);
lean_inc_ref(v_k_2396_);
lean_dec_ref_known(v_code_2384_, 2);
v___x_2397_ = lean_apply_3(v_h__2_2386_, v_decl_2395_, v_k_2396_, lean_box(0));
return v___x_2397_;
}
case 2:
{
lean_object* v_decl_2398_; lean_object* v_k_2399_; lean_object* v___x_2400_; 
lean_dec(v_h__7_2391_);
lean_dec(v_h__6_2390_);
lean_dec(v_h__5_2389_);
lean_dec(v_h__4_2388_);
lean_dec(v_h__2_2386_);
lean_dec(v_h__1_2385_);
v_decl_2398_ = lean_ctor_get(v_code_2384_, 0);
lean_inc_ref(v_decl_2398_);
v_k_2399_ = lean_ctor_get(v_code_2384_, 1);
lean_inc_ref(v_k_2399_);
lean_dec_ref_known(v_code_2384_, 2);
v___x_2400_ = lean_apply_2(v_h__3_2387_, v_decl_2398_, v_k_2399_);
return v___x_2400_;
}
case 3:
{
lean_object* v_fvarId_2401_; lean_object* v_args_2402_; lean_object* v___x_2403_; 
lean_dec(v_h__7_2391_);
lean_dec(v_h__6_2390_);
lean_dec(v_h__4_2388_);
lean_dec(v_h__3_2387_);
lean_dec(v_h__2_2386_);
lean_dec(v_h__1_2385_);
v_fvarId_2401_ = lean_ctor_get(v_code_2384_, 0);
lean_inc(v_fvarId_2401_);
v_args_2402_ = lean_ctor_get(v_code_2384_, 1);
lean_inc_ref(v_args_2402_);
lean_dec_ref_known(v_code_2384_, 2);
v___x_2403_ = lean_apply_2(v_h__5_2389_, v_fvarId_2401_, v_args_2402_);
return v___x_2403_;
}
case 4:
{
lean_object* v_cases_2404_; lean_object* v___x_2405_; 
lean_dec(v_h__6_2390_);
lean_dec(v_h__5_2389_);
lean_dec(v_h__4_2388_);
lean_dec(v_h__3_2387_);
lean_dec(v_h__2_2386_);
lean_dec(v_h__1_2385_);
v_cases_2404_ = lean_ctor_get(v_code_2384_, 0);
lean_inc_ref(v_cases_2404_);
lean_dec_ref_known(v_code_2384_, 1);
v___x_2405_ = lean_apply_1(v_h__7_2391_, v_cases_2404_);
return v___x_2405_;
}
case 5:
{
lean_object* v_fvarId_2406_; lean_object* v___x_2407_; 
lean_dec(v_h__7_2391_);
lean_dec(v_h__6_2390_);
lean_dec(v_h__5_2389_);
lean_dec(v_h__3_2387_);
lean_dec(v_h__2_2386_);
lean_dec(v_h__1_2385_);
v_fvarId_2406_ = lean_ctor_get(v_code_2384_, 0);
lean_inc(v_fvarId_2406_);
lean_dec_ref_known(v_code_2384_, 1);
v___x_2407_ = lean_apply_1(v_h__4_2388_, v_fvarId_2406_);
return v___x_2407_;
}
default: 
{
lean_object* v_type_2408_; lean_object* v___x_2409_; 
lean_dec(v_h__7_2391_);
lean_dec(v_h__5_2389_);
lean_dec(v_h__4_2388_);
lean_dec(v_h__3_2387_);
lean_dec(v_h__2_2386_);
lean_dec(v_h__1_2385_);
v_type_2408_ = lean_ctor_get(v_code_2384_, 0);
lean_inc_ref(v_type_2408_);
lean_dec_ref_known(v_code_2384_, 1);
v___x_2409_ = lean_apply_1(v_h__6_2390_, v_type_2408_);
return v___x_2409_;
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(uint8_t v_pu_2410_, lean_object* v_params_2411_, lean_object* v_code_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2410_, v_code_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; size_t v_sz_2420_; size_t v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_a_2419_);
lean_dec_ref_known(v___x_2418_, 1);
v_sz_2420_ = lean_array_size(v_params_2411_);
v___x_2421_ = ((size_t)0ULL);
v___x_2422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(v_sz_2420_, v___x_2421_, v_params_2411_);
v___x_2423_ = lean_unsigned_to_nat(32u);
v___x_2424_ = lean_mk_empty_array_with_capacity(v___x_2423_);
lean_dec_ref(v___x_2424_);
v___x_2425_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2426_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v___x_2422_, v_a_2419_, v___x_2425_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
lean_dec(v_a_2419_);
lean_dec_ref(v___x_2422_);
return v___x_2426_;
}
else
{
lean_dec_ref(v_params_2411_);
return v___x_2418_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_inferParamType_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2410_ = stack[0].m_num;
lean_object* v_params_2411_ = stack[1].m_obj;
lean_object* v_code_2412_ = stack[2].m_obj;
lean_object* v_a_2413_ = stack[3].m_obj;
lean_object* v_a_2414_ = stack[4].m_obj;
lean_object* v_a_2415_ = stack[5].m_obj;
lean_object* v_a_2416_ = stack[6].m_obj;
lean_object* v_res_2427_;
v_res_2427_ = l_Lean_Compiler_LCNF_Code_inferParamType(v_pu_2410_, v_params_2411_, v_code_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
stack->m_obj
 = v_res_2427_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType___boxed(lean_object* v_pu_2428_, lean_object* v_params_2429_, lean_object* v_code_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
uint8_t v_pu_boxed_2436_; lean_object* v_res_2437_; 
v_pu_boxed_2436_ = lean_unbox(v_pu_2428_);
v_res_2437_ = l_Lean_Compiler_LCNF_Code_inferParamType(v_pu_boxed_2436_, v_params_2429_, v_code_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
return v_res_2437_;
}
}
lean_object* l_Lean_Compiler_LCNF_Alt_inferType(uint8_t v_pu_2438_, lean_object* v_alt_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_){
_start:
{
switch(lean_obj_tag(v_alt_2439_))
{
case 0:
{
lean_object* v_code_2445_; lean_object* v___x_2446_; 
v_code_2445_ = lean_ctor_get(v_alt_2439_, 2);
lean_inc_ref(v_code_2445_);
lean_dec_ref_known(v_alt_2439_, 3);
v___x_2446_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2438_, v_code_2445_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
return v___x_2446_;
}
case 1:
{
lean_object* v_code_2447_; lean_object* v___x_2448_; 
v_code_2447_ = lean_ctor_get(v_alt_2439_, 1);
lean_inc_ref(v_code_2447_);
lean_dec_ref_known(v_alt_2439_, 2);
v___x_2448_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2438_, v_code_2447_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
return v___x_2448_;
}
default: 
{
lean_object* v_code_2449_; lean_object* v___x_2450_; 
v_code_2449_ = lean_ctor_get(v_alt_2439_, 0);
lean_inc_ref(v_code_2449_);
lean_dec_ref_known(v_alt_2439_, 1);
v___x_2450_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2438_, v_code_2449_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
return v___x_2450_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Alt_inferType_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2438_ = stack[0].m_num;
lean_object* v_alt_2439_ = stack[1].m_obj;
lean_object* v_a_2440_ = stack[2].m_obj;
lean_object* v_a_2441_ = stack[3].m_obj;
lean_object* v_a_2442_ = stack[4].m_obj;
lean_object* v_a_2443_ = stack[5].m_obj;
lean_object* v_res_2451_;
v_res_2451_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_2438_, v_alt_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
stack->m_obj
 = v_res_2451_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType___boxed(lean_object* v_pu_2452_, lean_object* v_alt_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
uint8_t v_pu_boxed_2459_; lean_object* v_res_2460_; 
v_pu_boxed_2459_ = lean_unbox(v_pu_2452_);
v_res_2460_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_boxed_2459_, v_alt_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
return v_res_2460_;
}
}
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t v_pu_2461_, lean_object* v_e_2462_, lean_object* v_prefixName_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_prefixName_2463_, v_a_2465_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; lean_object* v___x_2471_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2470_);
lean_dec_ref_known(v___x_2469_, 1);
lean_inc(v_e_2462_);
v___x_2471_ = l_Lean_Compiler_LCNF_LetValue_inferType(v_pu_2461_, v_e_2462_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v___x_2473_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2472_);
lean_dec_ref_known(v___x_2471_, 1);
v___x_2473_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2461_, v_a_2470_, v_a_2472_, v_e_2462_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_);
return v___x_2473_;
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec(v_a_2470_);
lean_dec(v_e_2462_);
v_a_2474_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2471_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2471_);
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
lean_dec(v_e_2462_);
v_a_2482_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2469_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2469_);
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_mkAuxLetDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2461_ = stack[0].m_num;
lean_object* v_e_2462_ = stack[1].m_obj;
lean_object* v_prefixName_2463_ = stack[2].m_obj;
lean_object* v_a_2464_ = stack[3].m_obj;
lean_object* v_a_2465_ = stack[4].m_obj;
lean_object* v_a_2466_ = stack[5].m_obj;
lean_object* v_a_2467_ = stack[6].m_obj;
lean_object* v_res_2490_;
v_res_2490_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v_pu_2461_, v_e_2462_, v_prefixName_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_);
stack->m_obj
 = v_res_2490_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl___boxed(lean_object* v_pu_2491_, lean_object* v_e_2492_, lean_object* v_prefixName_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_){
_start:
{
uint8_t v_pu_boxed_2499_; lean_object* v_res_2500_; 
v_pu_boxed_2499_ = lean_unbox(v_pu_2491_);
v_res_2500_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v_pu_boxed_2499_, v_e_2492_, v_prefixName_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
return v_res_2500_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkForallParams___closed__1(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2502_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2503_ = lean_unsigned_to_nat(15u);
v___x_2504_ = lean_unsigned_to_nat(295u);
v___x_2505_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkForallParams___closed__0));
v___x_2506_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2507_ = l_mkPanicMessageWithDecl(v___x_2506_, v___x_2505_, v___x_2504_, v___x_2503_, v___x_2502_);
return v___x_2507_;
}
}
lean_object* l_Lean_Compiler_LCNF_mkForallParams(uint8_t v_pu_2508_, lean_object* v_params_2509_, lean_object* v_type_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_){
_start:
{
if (v_pu_2508_ == 0)
{
lean_object* v___x_2516_; 
v___x_2516_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(v_params_2509_, v_type_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_);
return v___x_2516_;
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
lean_dec_ref(v_params_2509_);
v___x_2517_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkForallParams___closed__1, &l_Lean_Compiler_LCNF_mkForallParams___closed__1_once, _init_l_Lean_Compiler_LCNF_mkForallParams___closed__1);
v___x_2518_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2517_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_);
return v___x_2518_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_mkForallParams_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2508_ = stack[0].m_num;
lean_object* v_params_2509_ = stack[1].m_obj;
lean_object* v_type_2510_ = stack[2].m_obj;
lean_object* v_a_2511_ = stack[3].m_obj;
lean_object* v_a_2512_ = stack[4].m_obj;
lean_object* v_a_2513_ = stack[5].m_obj;
lean_object* v_a_2514_ = stack[6].m_obj;
lean_object* v_res_2519_;
v_res_2519_ = l_Lean_Compiler_LCNF_mkForallParams(v_pu_2508_, v_params_2509_, v_type_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_);
stack->m_obj
 = v_res_2519_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams___boxed(lean_object* v_pu_2520_, lean_object* v_params_2521_, lean_object* v_type_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_){
_start:
{
uint8_t v_pu_boxed_2528_; lean_object* v_res_2529_; 
v_pu_boxed_2528_ = lean_unbox(v_pu_2520_);
v_res_2529_ = l_Lean_Compiler_LCNF_mkForallParams(v_pu_boxed_2528_, v_params_2521_, v_type_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
lean_dec(v_a_2526_);
lean_dec_ref(v_a_2525_);
lean_dec(v_a_2524_);
lean_dec_ref(v_a_2523_);
lean_dec_ref(v_type_2522_);
return v_res_2529_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(uint8_t v_pu_2530_, lean_object* v_params_2531_, lean_object* v_code_2532_, lean_object* v_prefixName_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v___x_2539_; 
lean_inc_ref(v_code_2532_);
v___x_2539_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2530_, v_code_2532_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; lean_object* v___x_2541_; 
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_a_2540_);
lean_dec_ref_known(v___x_2539_, 1);
lean_inc_ref(v_params_2531_);
v___x_2541_ = l_Lean_Compiler_LCNF_mkForallParams(v_pu_2530_, v_params_2531_, v_a_2540_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_);
lean_dec(v_a_2540_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2543_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___x_2541_, 1);
v___x_2543_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_prefixName_2533_, v_a_2535_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2545_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref_known(v___x_2543_, 1);
v___x_2545_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_2530_, v_a_2544_, v_a_2542_, v_params_2531_, v_code_2532_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_);
return v___x_2545_;
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
lean_dec(v_a_2542_);
lean_dec_ref(v_code_2532_);
lean_dec_ref(v_params_2531_);
v_a_2546_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2543_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2543_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_dec(v_prefixName_2533_);
lean_dec_ref(v_code_2532_);
lean_dec_ref(v_params_2531_);
v_a_2554_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2541_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2541_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
lean_dec(v_prefixName_2533_);
lean_dec_ref(v_code_2532_);
lean_dec_ref(v_params_2531_);
v_a_2562_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2539_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2539_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2530_ = stack[0].m_num;
lean_object* v_params_2531_ = stack[1].m_obj;
lean_object* v_code_2532_ = stack[2].m_obj;
lean_object* v_prefixName_2533_ = stack[3].m_obj;
lean_object* v_a_2534_ = stack[4].m_obj;
lean_object* v_a_2535_ = stack[5].m_obj;
lean_object* v_a_2536_ = stack[6].m_obj;
lean_object* v_a_2537_ = stack[7].m_obj;
lean_object* v_res_2570_;
v_res_2570_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_2530_, v_params_2531_, v_code_2532_, v_prefixName_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_);
stack->m_obj
 = v_res_2570_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux___boxed(lean_object* v_pu_2571_, lean_object* v_params_2572_, lean_object* v_code_2573_, lean_object* v_prefixName_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_){
_start:
{
uint8_t v_pu_boxed_2580_; lean_object* v_res_2581_; 
v_pu_boxed_2580_ = lean_unbox(v_pu_2571_);
v_res_2581_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_boxed_2580_, v_params_2572_, v_code_2573_, v_prefixName_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_);
lean_dec(v_a_2578_);
lean_dec_ref(v_a_2577_);
lean_dec(v_a_2576_);
lean_dec_ref(v_a_2575_);
return v_res_2581_;
}
}
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object* v_params_2582_, lean_object* v_code_2583_, lean_object* v_prefixName_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
uint8_t v___x_2590_; lean_object* v___x_2591_; 
v___x_2590_ = 0;
v___x_2591_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v___x_2590_, v_params_2582_, v_code_2583_, v_prefixName_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
return v___x_2591_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_mkAuxFunDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_2582_ = stack[0].m_obj;
lean_object* v_code_2583_ = stack[1].m_obj;
lean_object* v_prefixName_2584_ = stack[2].m_obj;
lean_object* v_a_2585_ = stack[3].m_obj;
lean_object* v_a_2586_ = stack[4].m_obj;
lean_object* v_a_2587_ = stack[5].m_obj;
lean_object* v_a_2588_ = stack[6].m_obj;
lean_object* v_res_2592_;
v_res_2592_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v_params_2582_, v_code_2583_, v_prefixName_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
stack->m_obj
 = v_res_2592_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl___boxed(lean_object* v_params_2593_, lean_object* v_code_2594_, lean_object* v_prefixName_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v_params_2593_, v_code_2594_, v_prefixName_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
return v_res_2601_;
}
}
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(uint8_t v_pu_2602_, lean_object* v_params_2603_, lean_object* v_code_2604_, lean_object* v_prefixName_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_2602_, v_params_2603_, v_code_2604_, v_prefixName_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_);
return v___x_2611_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_mkAuxJpDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2602_ = stack[0].m_num;
lean_object* v_params_2603_ = stack[1].m_obj;
lean_object* v_code_2604_ = stack[2].m_obj;
lean_object* v_prefixName_2605_ = stack[3].m_obj;
lean_object* v_a_2606_ = stack[4].m_obj;
lean_object* v_a_2607_ = stack[5].m_obj;
lean_object* v_a_2608_ = stack[6].m_obj;
lean_object* v_a_2609_ = stack[7].m_obj;
lean_object* v_res_2612_;
v_res_2612_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v_pu_2602_, v_params_2603_, v_code_2604_, v_prefixName_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_);
stack->m_obj
 = v_res_2612_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl___boxed(lean_object* v_pu_2613_, lean_object* v_params_2614_, lean_object* v_code_2615_, lean_object* v_prefixName_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_){
_start:
{
uint8_t v_pu_boxed_2622_; lean_object* v_res_2623_; 
v_pu_boxed_2622_ = lean_unbox(v_pu_2613_);
v_res_2623_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v_pu_boxed_2622_, v_params_2614_, v_code_2615_, v_prefixName_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
lean_dec(v_a_2618_);
lean_dec_ref(v_a_2617_);
return v_res_2623_;
}
}
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(uint8_t v_pu_2624_, lean_object* v_param_2625_, lean_object* v_code_2626_, lean_object* v_prefixName_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v_params_2635_; lean_object* v___x_2636_; 
v___x_2633_ = lean_unsigned_to_nat(1u);
v___x_2634_ = lean_mk_empty_array_with_capacity(v___x_2633_);
v_params_2635_ = lean_array_push(v___x_2634_, v_param_2625_);
v___x_2636_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_2624_, v_params_2635_, v_code_2626_, v_prefixName_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
return v___x_2636_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_mkAuxJpDecl_x27_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2624_ = stack[0].m_num;
lean_object* v_param_2625_ = stack[1].m_obj;
lean_object* v_code_2626_ = stack[2].m_obj;
lean_object* v_prefixName_2627_ = stack[3].m_obj;
lean_object* v_a_2628_ = stack[4].m_obj;
lean_object* v_a_2629_ = stack[5].m_obj;
lean_object* v_a_2630_ = stack[6].m_obj;
lean_object* v_a_2631_ = stack[7].m_obj;
lean_object* v_res_2637_;
v_res_2637_ = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(v_pu_2624_, v_param_2625_, v_code_2626_, v_prefixName_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
stack->m_obj
 = v_res_2637_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___boxed(lean_object* v_pu_2638_, lean_object* v_param_2639_, lean_object* v_code_2640_, lean_object* v_prefixName_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_){
_start:
{
uint8_t v_pu_boxed_2647_; lean_object* v_res_2648_; 
v_pu_boxed_2647_ = lean_unbox(v_pu_2638_);
v_res_2648_ = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(v_pu_boxed_2647_, v_param_2639_, v_code_2640_, v_prefixName_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
return v_res_2648_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(lean_object* v_msg_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v_ref_2655_; lean_object* v___x_2656_; lean_object* v_env_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_ref_2655_ = lean_ctor_get(v___y_2652_, 2);
v___x_2656_ = lean_st_ref_get(v___y_2653_);
v_env_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc_ref(v_env_2657_);
lean_dec(v___x_2656_);
v___x_2658_ = lean_st_ref_get(v___y_2651_);
v___x_2659_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_2650_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2682_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2662_ = v___x_2659_;
v_isShared_2663_ = v_isSharedCheck_2682_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2659_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2682_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v_lctx_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2680_; 
v_lctx_2664_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2680_ == 0)
{
lean_object* v_unused_2681_; 
v_unused_2681_ = lean_ctor_get(v___x_2658_, 1);
lean_dec(v_unused_2681_);
v___x_2666_ = v___x_2658_;
v_isShared_2667_ = v_isSharedCheck_2680_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_lctx_2664_);
lean_dec(v___x_2658_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2680_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
uint8_t v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2674_; 
v___x_2668_ = lean_unbox(v_a_2660_);
lean_dec(v_a_2660_);
v___x_2669_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2664_, v___x_2668_);
lean_dec_ref(v_lctx_2664_);
v___x_2670_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2652_);
v___x_2671_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1);
v___x_2672_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2672_, 0, v_env_2657_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
lean_ctor_set(v___x_2672_, 2, v___x_2669_);
lean_ctor_set(v___x_2672_, 3, v___x_2670_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set_tag(v___x_2666_, 3);
lean_ctor_set(v___x_2666_, 1, v_msg_2649_);
lean_ctor_set(v___x_2666_, 0, v___x_2672_);
v___x_2674_ = v___x_2666_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2672_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_msg_2649_);
v___x_2674_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_object* v___x_2675_; lean_object* v___x_2677_; 
lean_inc(v_ref_2655_);
v___x_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2675_, 0, v_ref_2655_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set_tag(v___x_2662_, 1);
lean_ctor_set(v___x_2662_, 0, v___x_2675_);
v___x_2677_ = v___x_2662_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
lean_dec(v___x_2658_);
lean_dec_ref(v_env_2657_);
lean_dec_ref(v_msg_2649_);
v_a_2683_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2659_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2659_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2683_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2649_ = stack[0].m_obj;
lean_object* v___y_2650_ = stack[1].m_obj;
lean_object* v___y_2651_ = stack[2].m_obj;
lean_object* v___y_2652_ = stack[3].m_obj;
lean_object* v___y_2653_ = stack[4].m_obj;
lean_object* v_res_2691_;
v_res_2691_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v_msg_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
stack->m_obj
 = v_res_2691_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg___boxed(lean_object* v_msg_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v_msg_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
return v_res_2698_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1(lean_object* v_00_u03b1_2699_, lean_object* v_msg_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v___x_2706_; 
v___x_2706_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v_msg_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
return v___x_2706_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2700_ = stack[1].m_obj;
lean_object* v___y_2701_ = stack[2].m_obj;
lean_object* v___y_2702_ = stack[3].m_obj;
lean_object* v___y_2703_ = stack[4].m_obj;
lean_object* v___y_2704_ = stack[5].m_obj;
lean_object* v_res_2707_;
v_res_2707_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1(lean_box(0), v_msg_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
stack->m_obj
 = v_res_2707_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___boxed(lean_object* v_00_u03b1_2708_, lean_object* v_msg_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1(v_00_u03b1_2708_, v_msg_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
return v_res_2715_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(uint8_t v_pu_2716_, lean_object* v_a_2717_, lean_object* v_b_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_array_2724_; lean_object* v_start_2725_; lean_object* v_stop_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2742_; 
v_array_2724_ = lean_ctor_get(v_a_2717_, 0);
v_start_2725_ = lean_ctor_get(v_a_2717_, 1);
v_stop_2726_ = lean_ctor_get(v_a_2717_, 2);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_a_2717_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2728_ = v_a_2717_;
v_isShared_2729_ = v_isSharedCheck_2742_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_stop_2726_);
lean_inc(v_start_2725_);
lean_inc(v_array_2724_);
lean_dec(v_a_2717_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2742_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
uint8_t v___x_2730_; 
v___x_2730_ = lean_nat_dec_lt(v_start_2725_, v_stop_2726_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; 
lean_del_object(v___x_2728_);
lean_dec(v_stop_2726_);
lean_dec(v_start_2725_);
lean_dec_ref(v_array_2724_);
v___x_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2731_, 0, v_b_2718_);
return v___x_2731_;
}
else
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2732_ = lean_unsigned_to_nat(1u);
v___x_2733_ = lean_nat_add(v_start_2725_, v___x_2732_);
lean_inc_ref(v_array_2724_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 1, v___x_2733_);
v___x_2735_ = v___x_2728_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_array_2724_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v___x_2733_);
lean_ctor_set(v_reuseFailAlloc_2741_, 2, v_stop_2726_);
v___x_2735_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = lean_array_fget(v_array_2724_, v_start_2725_);
lean_dec(v_start_2725_);
lean_dec_ref(v_array_2724_);
v___x_2737_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_2716_, v___x_2736_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; lean_object* v___x_2739_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_a_2738_);
lean_dec_ref_known(v___x_2737_, 1);
v___x_2739_ = l_Lean_Compiler_LCNF_joinTypes(v_b_2718_, v_a_2738_);
v_a_2717_ = v___x_2735_;
v_b_2718_ = v___x_2739_;
goto _start;
}
else
{
lean_dec_ref(v___x_2735_);
lean_dec_ref(v_b_2718_);
return v___x_2737_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2716_ = stack[0].m_num;
lean_object* v_a_2717_ = stack[1].m_obj;
lean_object* v_b_2718_ = stack[2].m_obj;
lean_object* v___y_2719_ = stack[3].m_obj;
lean_object* v___y_2720_ = stack[4].m_obj;
lean_object* v___y_2721_ = stack[5].m_obj;
lean_object* v___y_2722_ = stack[6].m_obj;
lean_object* v_res_2743_;
v_res_2743_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_2716_, v_a_2717_, v_b_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
stack->m_obj
 = v_res_2743_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg___boxed(lean_object* v_pu_2744_, lean_object* v_a_2745_, lean_object* v_b_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
uint8_t v_pu_boxed_2752_; lean_object* v_res_2753_; 
v_pu_boxed_2752_ = lean_unbox(v_pu_2744_);
v_res_2753_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_boxed_2752_, v_a_2745_, v_b_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
return v_res_2753_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__0(void){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
return v___x_2754_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__2(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2756_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkCasesResultType___closed__1));
v___x_2757_ = l_Lean_stringToMessageData(v___x_2756_);
return v___x_2757_;
}
}
lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(uint8_t v_pu_2758_, lean_object* v_alts_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v___x_2765_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___x_2779_; lean_object* v___x_2780_; uint8_t v___x_2781_; 
v___x_2765_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkCasesResultType___closed__0, &l_Lean_Compiler_LCNF_mkCasesResultType___closed__0_once, _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__0);
v___x_2779_ = lean_array_get_size(v_alts_2759_);
v___x_2780_ = lean_unsigned_to_nat(0u);
v___x_2781_ = lean_nat_dec_eq(v___x_2779_, v___x_2780_);
if (v___x_2781_ == 0)
{
v___y_2767_ = v_a_2760_;
v___y_2768_ = v_a_2761_;
v___y_2769_ = v_a_2762_;
v___y_2770_ = v_a_2763_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec_ref(v_alts_2759_);
v___x_2782_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkCasesResultType___closed__2, &l_Lean_Compiler_LCNF_mkCasesResultType___closed__2_once, _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__2);
v___x_2783_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v___x_2782_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2783_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2783_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
v___jp_2766_:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2771_ = lean_unsigned_to_nat(0u);
v___x_2772_ = lean_array_get_borrowed(v___x_2765_, v_alts_2759_, v___x_2771_);
lean_inc(v___x_2772_);
v___x_2773_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_2758_, v___x_2772_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2773_, 1);
v___x_2775_ = lean_unsigned_to_nat(1u);
v___x_2776_ = lean_array_get_size(v_alts_2759_);
v___x_2777_ = l_Array_toSubarray___redArg(v_alts_2759_, v___x_2775_, v___x_2776_);
v___x_2778_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_2758_, v___x_2777_, v_a_2774_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
return v___x_2778_;
}
else
{
lean_dec_ref(v_alts_2759_);
return v___x_2773_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_mkCasesResultType_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2758_ = stack[0].m_num;
lean_object* v_alts_2759_ = stack[1].m_obj;
lean_object* v_a_2760_ = stack[2].m_obj;
lean_object* v_a_2761_ = stack[3].m_obj;
lean_object* v_a_2762_ = stack[4].m_obj;
lean_object* v_a_2763_ = stack[5].m_obj;
lean_object* v_res_2792_;
v_res_2792_ = l_Lean_Compiler_LCNF_mkCasesResultType(v_pu_2758_, v_alts_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
stack->m_obj
 = v_res_2792_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___boxed(lean_object* v_pu_2793_, lean_object* v_alts_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
uint8_t v_pu_boxed_2800_; lean_object* v_res_2801_; 
v_pu_boxed_2800_ = lean_unbox(v_pu_2793_);
v_res_2801_ = l_Lean_Compiler_LCNF_mkCasesResultType(v_pu_boxed_2800_, v_alts_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
lean_dec(v_a_2796_);
lean_dec_ref(v_a_2795_);
return v_res_2801_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0(uint8_t v_pu_2802_, lean_object* v_inst_2803_, lean_object* v_R_2804_, lean_object* v_a_2805_, lean_object* v_b_2806_, lean_object* v_c_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_2802_, v_a_2805_, v_b_2806_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
return v___x_2813_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2802_ = stack[0].m_num;
lean_object* v_a_2805_ = stack[3].m_obj;
lean_object* v_b_2806_ = stack[4].m_obj;
lean_object* v___y_2808_ = stack[6].m_obj;
lean_object* v___y_2809_ = stack[7].m_obj;
lean_object* v___y_2810_ = stack[8].m_obj;
lean_object* v___y_2811_ = stack[9].m_obj;
lean_object* v_res_2814_;
v_res_2814_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0(v_pu_2802_, lean_box(0), lean_box(0), v_a_2805_, v_b_2806_, lean_box(0), v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
stack->m_obj
 = v_res_2814_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___boxed(lean_object* v_pu_2815_, lean_object* v_inst_2816_, lean_object* v_R_2817_, lean_object* v_a_2818_, lean_object* v_b_2819_, lean_object* v_c_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
uint8_t v_pu_boxed_2826_; lean_object* v_res_2827_; 
v_pu_boxed_2826_ = lean_unbox(v_pu_2815_);
v_res_2827_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0(v_pu_boxed_2826_, v_inst_2816_, v_R_2817_, v_a_2818_, v_b_2819_, v_c_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
return v_res_2827_;
}
}
lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(lean_object* v_msg_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v___x_2834_; lean_object* v_toApplicative_2835_; lean_object* v_toFunctor_2836_; lean_object* v_toSeq_2837_; lean_object* v_toSeqLeft_2838_; lean_object* v_toSeqRight_2839_; lean_object* v___f_2840_; lean_object* v___f_2841_; lean_object* v___f_2842_; lean_object* v___f_2843_; lean_object* v___x_2844_; lean_object* v___f_2845_; lean_object* v___f_2846_; lean_object* v___f_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___f_2854_; lean_object* v___x_970__overap_2855_; lean_object* v___x_2856_; 
v___x_2834_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_2835_ = lean_ctor_get(v___x_2834_, 0);
v_toFunctor_2836_ = lean_ctor_get(v_toApplicative_2835_, 0);
v_toSeq_2837_ = lean_ctor_get(v_toApplicative_2835_, 2);
v_toSeqLeft_2838_ = lean_ctor_get(v_toApplicative_2835_, 3);
v_toSeqRight_2839_ = lean_ctor_get(v_toApplicative_2835_, 4);
v___f_2840_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_2841_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2836_, 2);
v___f_2842_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2842_, 0, v_toFunctor_2836_);
v___f_2843_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2843_, 0, v_toFunctor_2836_);
v___x_2844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___f_2842_);
lean_ctor_set(v___x_2844_, 1, v___f_2843_);
lean_inc(v_toSeqRight_2839_);
v___f_2845_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2845_, 0, v_toSeqRight_2839_);
lean_inc(v_toSeqLeft_2838_);
v___f_2846_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2846_, 0, v_toSeqLeft_2838_);
lean_inc(v_toSeq_2837_);
v___f_2847_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2847_, 0, v_toSeq_2837_);
v___x_2848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2844_);
lean_ctor_set(v___x_2848_, 1, v___f_2840_);
lean_ctor_set(v___x_2848_, 2, v___f_2847_);
lean_ctor_set(v___x_2848_, 3, v___f_2846_);
lean_ctor_set(v___x_2848_, 4, v___f_2845_);
v___x_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
lean_ctor_set(v___x_2849_, 1, v___f_2841_);
v___x_2850_ = l_StateRefT_x27_instMonad___redArg(v___x_2849_);
v___x_2851_ = 0;
v___x_2852_ = lean_box(v___x_2851_);
v___x_2853_ = l_instInhabitedOfMonad___redArg(v___x_2850_, v___x_2852_);
v___f_2854_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2854_, 0, v___x_2853_);
v___x_970__overap_2855_ = lean_panic_fn_borrowed(v___f_2854_, v_msg_2828_);
lean_dec_ref(v___f_2854_);
lean_inc(v___y_2832_);
lean_inc_ref(v___y_2831_);
lean_inc(v___y_2830_);
lean_inc_ref(v___y_2829_);
v___x_2856_ = lean_apply_5(v___x_970__overap_2855_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, lean_box(0));
return v___x_2856_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2828_ = stack[0].m_obj;
lean_object* v___y_2829_ = stack[1].m_obj;
lean_object* v___y_2830_ = stack[2].m_obj;
lean_object* v___y_2831_ = stack[3].m_obj;
lean_object* v___y_2832_ = stack[4].m_obj;
lean_object* v_res_2857_;
v_res_2857_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(v_msg_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
stack->m_obj
 = v_res_2857_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0___boxed(lean_object* v_msg_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(v_msg_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
return v_res_2864_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1(void){
_start:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2866_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2));
v___x_2867_ = lean_unsigned_to_nat(50u);
v___x_2868_ = lean_unsigned_to_nat(345u);
v___x_2869_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__0));
v___x_2870_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2871_ = l_mkPanicMessageWithDecl(v___x_2870_, v___x_2869_, v___x_2868_, v___x_2867_, v___x_2866_);
return v___x_2871_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(lean_object* v_type_2872_, lean_object* v_predVars_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v_t_2880_; lean_object* v_b_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v_type_2890_; 
v_type_2890_ = l_Lean_Expr_headBeta(v_type_2872_);
switch(lean_obj_tag(v_type_2890_))
{
case 0:
{
lean_object* v_deBruijnIndex_2891_; uint8_t v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v_deBruijnIndex_2891_ = lean_ctor_get(v_type_2890_, 0);
lean_inc(v_deBruijnIndex_2891_);
lean_dec_ref_known(v_type_2890_, 1);
v___x_2892_ = 0;
v___x_2893_ = lean_array_get_size(v_predVars_2873_);
v___x_2894_ = lean_nat_sub(v___x_2893_, v_deBruijnIndex_2891_);
lean_dec(v_deBruijnIndex_2891_);
v___x_2895_ = lean_unsigned_to_nat(1u);
v___x_2896_ = lean_nat_sub(v___x_2894_, v___x_2895_);
lean_dec(v___x_2894_);
v___x_2897_ = lean_box(v___x_2892_);
v___x_2898_ = lean_array_get(v___x_2897_, v_predVars_2873_, v___x_2896_);
lean_dec(v___x_2896_);
lean_dec_ref(v_predVars_2873_);
lean_dec(v___x_2897_);
v___x_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
return v___x_2899_;
}
case 1:
{
lean_object* v_fvarId_2900_; lean_object* v___x_2901_; 
lean_dec_ref(v_predVars_2873_);
v_fvarId_2900_ = lean_ctor_get(v_type_2890_, 0);
lean_inc(v_fvarId_2900_);
lean_dec_ref_known(v_type_2890_, 1);
v___x_2901_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2900_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2911_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2904_ = v___x_2901_;
v_isShared_2905_ = v_isSharedCheck_2911_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2901_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2911_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
uint8_t v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2909_; 
v___x_2906_ = l_Lean_Compiler_LCNF_isPredicateType(v_a_2902_);
v___x_2907_ = lean_box(v___x_2906_);
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 0, v___x_2907_);
v___x_2909_ = v___x_2904_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2907_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
v_a_2912_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2901_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2901_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
case 3:
{
uint8_t v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
lean_dec_ref_known(v_type_2890_, 1);
lean_dec_ref(v_predVars_2873_);
v___x_2920_ = 0;
v___x_2921_ = lean_box(v___x_2920_);
v___x_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
return v___x_2922_;
}
case 4:
{
uint8_t v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
lean_dec_ref(v_predVars_2873_);
v___x_2923_ = l_Lean_Expr_isErased(v_type_2890_);
lean_dec_ref_known(v_type_2890_, 2);
v___x_2924_ = lean_box(v___x_2923_);
v___x_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2924_);
return v___x_2925_;
}
case 5:
{
lean_object* v_fn_2926_; 
v_fn_2926_ = lean_ctor_get(v_type_2890_, 0);
lean_inc_ref(v_fn_2926_);
lean_dec_ref_known(v_type_2890_, 2);
v_type_2872_ = v_fn_2926_;
goto _start;
}
case 6:
{
lean_object* v_binderType_2928_; lean_object* v_body_2929_; 
v_binderType_2928_ = lean_ctor_get(v_type_2890_, 1);
lean_inc_ref(v_binderType_2928_);
v_body_2929_ = lean_ctor_get(v_type_2890_, 2);
lean_inc_ref(v_body_2929_);
lean_dec_ref_known(v_type_2890_, 3);
v_t_2880_ = v_binderType_2928_;
v_b_2881_ = v_body_2929_;
v___y_2882_ = v_a_2874_;
v___y_2883_ = v_a_2875_;
v___y_2884_ = v_a_2876_;
v___y_2885_ = v_a_2877_;
goto v___jp_2879_;
}
case 7:
{
lean_object* v_binderType_2930_; lean_object* v_body_2931_; 
v_binderType_2930_ = lean_ctor_get(v_type_2890_, 1);
lean_inc_ref(v_binderType_2930_);
v_body_2931_ = lean_ctor_get(v_type_2890_, 2);
lean_inc_ref(v_body_2931_);
lean_dec_ref_known(v_type_2890_, 3);
v_t_2880_ = v_binderType_2930_;
v_b_2881_ = v_body_2931_;
v___y_2882_ = v_a_2874_;
v___y_2883_ = v_a_2875_;
v___y_2884_ = v_a_2876_;
v___y_2885_ = v_a_2877_;
goto v___jp_2879_;
}
case 10:
{
lean_object* v_expr_2932_; 
v_expr_2932_ = lean_ctor_get(v_type_2890_, 1);
lean_inc_ref(v_expr_2932_);
lean_dec_ref_known(v_type_2890_, 2);
v_type_2872_ = v_expr_2932_;
goto _start;
}
default: 
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
lean_dec_ref(v_type_2890_);
lean_dec_ref(v_predVars_2873_);
v___x_2934_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1, &l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1);
v___x_2935_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(v___x_2934_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
return v___x_2935_;
}
}
v___jp_2879_:
{
uint8_t v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2886_ = l_Lean_Compiler_LCNF_isPredicateType(v_t_2880_);
v___x_2887_ = lean_box(v___x_2886_);
v___x_2888_ = lean_array_push(v_predVars_2873_, v___x_2887_);
v_type_2872_ = v_b_2881_;
v_predVars_2873_ = v___x_2888_;
v_a_2874_ = v___y_2882_;
v_a_2875_ = v___y_2883_;
v_a_2876_ = v___y_2884_;
v_a_2877_ = v___y_2885_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2872_ = stack[0].m_obj;
lean_object* v_predVars_2873_ = stack[1].m_obj;
lean_object* v_a_2874_ = stack[2].m_obj;
lean_object* v_a_2875_ = stack[3].m_obj;
lean_object* v_a_2876_ = stack[4].m_obj;
lean_object* v_a_2877_ = stack[5].m_obj;
lean_object* v_res_2936_;
v_res_2936_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(v_type_2872_, v_predVars_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
stack->m_obj
 = v_res_2936_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___boxed(lean_object* v_type_2937_, lean_object* v_predVars_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(v_type_2937_, v_predVars_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
return v_res_2944_;
}
}
lean_object* l_Lean_Compiler_LCNF_isErasedCompatible(lean_object* v_type_2945_, lean_object* v_predVars_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(v_type_2945_, v_predVars_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_);
return v___x_2952_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_isErasedCompatible_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2945_ = stack[0].m_obj;
lean_object* v_predVars_2946_ = stack[1].m_obj;
lean_object* v_a_2947_ = stack[2].m_obj;
lean_object* v_a_2948_ = stack[3].m_obj;
lean_object* v_a_2949_ = stack[4].m_obj;
lean_object* v_a_2950_ = stack[5].m_obj;
lean_object* v_res_2953_;
v_res_2953_ = l_Lean_Compiler_LCNF_isErasedCompatible(v_type_2945_, v_predVars_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_);
stack->m_obj
 = v_res_2953_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible___boxed(lean_object* v_type_2954_, lean_object* v_predVars_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Lean_Compiler_LCNF_isErasedCompatible(v_type_2954_, v_predVars_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
lean_dec(v_a_2959_);
lean_dec_ref(v_a_2958_);
lean_dec(v_a_2957_);
lean_dec_ref(v_a_2956_);
return v_res_2961_;
}
}
uint8_t l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(lean_object* v_x_2962_, lean_object* v_x_2963_){
_start:
{
if (lean_obj_tag(v_x_2962_) == 0)
{
if (lean_obj_tag(v_x_2963_) == 0)
{
uint8_t v___x_2964_; 
v___x_2964_ = 1;
return v___x_2964_;
}
else
{
uint8_t v___x_2965_; 
v___x_2965_ = 0;
return v___x_2965_;
}
}
else
{
if (lean_obj_tag(v_x_2963_) == 0)
{
uint8_t v___x_2966_; 
v___x_2966_ = 0;
return v___x_2966_;
}
else
{
lean_object* v_head_2967_; lean_object* v_tail_2968_; lean_object* v_head_2969_; lean_object* v_tail_2970_; uint8_t v___x_2971_; 
v_head_2967_ = lean_ctor_get(v_x_2962_, 0);
v_tail_2968_ = lean_ctor_get(v_x_2962_, 1);
v_head_2969_ = lean_ctor_get(v_x_2963_, 0);
v_tail_2970_ = lean_ctor_get(v_x_2963_, 1);
v___x_2971_ = l_Lean_Level_isEquiv(v_head_2967_, v_head_2969_);
if (v___x_2971_ == 0)
{
return v___x_2971_;
}
else
{
v_x_2962_ = v_tail_2968_;
v_x_2963_ = v_tail_2970_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2962_ = stack[0].m_obj;
lean_object* v_x_2963_ = stack[1].m_obj;
uint8_t v_res_2973_;
v_res_2973_ = l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(v_x_2962_, v_x_2963_);
stack->m_num = v_res_2973_;
}
LEAN_EXPORT lean_object* l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0___boxed(lean_object* v_x_2974_, lean_object* v_x_2975_){
_start:
{
uint8_t v_res_2976_; lean_object* v_r_2977_; 
v_res_2976_ = l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(v_x_2974_, v_x_2975_);
lean_dec(v_x_2975_);
lean_dec(v_x_2974_);
v_r_2977_ = lean_box(v_res_2976_);
return v_r_2977_;
}
}
uint8_t l_Lean_Compiler_LCNF_eqvTypes(lean_object* v_a_2978_, lean_object* v_b_2979_){
_start:
{
uint8_t v___x_2980_; lean_object* v_d_u2081_2982_; lean_object* v_b_u2081_2983_; lean_object* v_d_u2082_2984_; lean_object* v_b_u2082_2985_; uint8_t v___x_2988_; uint8_t v___y_2990_; 
v___x_2980_ = lean_expr_eqv(v_a_2978_, v_b_2979_);
v___x_2988_ = 1;
if (v___x_2980_ == 0)
{
uint8_t v___x_3034_; 
v___x_3034_ = l_Lean_Expr_isErased(v_a_2978_);
if (v___x_3034_ == 0)
{
v___y_2990_ = v___x_2980_;
goto v___jp_2989_;
}
else
{
uint8_t v___x_3035_; 
v___x_3035_ = l_Lean_Expr_isErased(v_b_2979_);
v___y_2990_ = v___x_3035_;
goto v___jp_2989_;
}
}
else
{
lean_dec_ref(v_b_2979_);
lean_dec_ref(v_a_2978_);
return v___x_2988_;
}
v___jp_2981_:
{
uint8_t v___x_2986_; 
v___x_2986_ = l_Lean_Compiler_LCNF_eqvTypes(v_d_u2081_2982_, v_d_u2082_2984_);
if (v___x_2986_ == 0)
{
lean_dec_ref(v_b_u2082_2985_);
lean_dec_ref(v_b_u2081_2983_);
return v___x_2980_;
}
else
{
v_a_2978_ = v_b_u2081_2983_;
v_b_2979_ = v_b_u2082_2985_;
goto _start;
}
}
v___jp_2989_:
{
if (v___y_2990_ == 0)
{
lean_object* v_a_x27_2991_; lean_object* v_b_x27_2992_; uint8_t v___x_2993_; 
lean_inc_ref(v_a_2978_);
v_a_x27_2991_ = l_Lean_Expr_headBeta(v_a_2978_);
lean_inc_ref(v_b_2979_);
v_b_x27_2992_ = l_Lean_Expr_headBeta(v_b_2979_);
v___x_2993_ = lean_expr_eqv(v_a_2978_, v_a_x27_2991_);
if (v___x_2993_ == 0)
{
lean_dec_ref(v_b_2979_);
lean_dec_ref(v_a_2978_);
v_a_2978_ = v_a_x27_2991_;
v_b_2979_ = v_b_x27_2992_;
goto _start;
}
else
{
uint8_t v___x_2995_; 
v___x_2995_ = lean_expr_eqv(v_b_2979_, v_b_x27_2992_);
if (v___x_2995_ == 0)
{
lean_dec_ref(v_b_2979_);
lean_dec_ref(v_a_2978_);
v_a_2978_ = v_a_x27_2991_;
v_b_2979_ = v_b_x27_2992_;
goto _start;
}
else
{
lean_dec_ref(v_b_x27_2992_);
lean_dec_ref(v_a_x27_2991_);
switch(lean_obj_tag(v_a_2978_))
{
case 10:
{
lean_object* v_expr_2997_; 
v_expr_2997_ = lean_ctor_get(v_a_2978_, 1);
lean_inc_ref(v_expr_2997_);
lean_dec_ref_known(v_a_2978_, 2);
v_a_2978_ = v_expr_2997_;
goto _start;
}
case 5:
{
switch(lean_obj_tag(v_b_2979_))
{
case 10:
{
lean_object* v_expr_2999_; 
v_expr_2999_ = lean_ctor_get(v_b_2979_, 1);
lean_inc_ref(v_expr_2999_);
lean_dec_ref_known(v_b_2979_, 2);
v_b_2979_ = v_expr_2999_;
goto _start;
}
case 5:
{
lean_object* v_fn_3001_; lean_object* v_arg_3002_; lean_object* v_fn_3003_; lean_object* v_arg_3004_; uint8_t v___x_3005_; 
v_fn_3001_ = lean_ctor_get(v_a_2978_, 0);
lean_inc_ref(v_fn_3001_);
v_arg_3002_ = lean_ctor_get(v_a_2978_, 1);
lean_inc_ref(v_arg_3002_);
lean_dec_ref_known(v_a_2978_, 2);
v_fn_3003_ = lean_ctor_get(v_b_2979_, 0);
lean_inc_ref(v_fn_3003_);
v_arg_3004_ = lean_ctor_get(v_b_2979_, 1);
lean_inc_ref(v_arg_3004_);
lean_dec_ref_known(v_b_2979_, 2);
v___x_3005_ = l_Lean_Compiler_LCNF_eqvTypes(v_fn_3001_, v_fn_3003_);
if (v___x_3005_ == 0)
{
lean_dec_ref(v_arg_3004_);
lean_dec_ref(v_arg_3002_);
return v___x_2980_;
}
else
{
v_a_2978_ = v_arg_3002_;
v_b_2979_ = v_arg_3004_;
goto _start;
}
}
default: 
{
lean_dec_ref_known(v_a_2978_, 2);
lean_dec_ref(v_b_2979_);
return v___y_2990_;
}
}
}
case 7:
{
switch(lean_obj_tag(v_b_2979_))
{
case 10:
{
lean_object* v_expr_3007_; 
v_expr_3007_ = lean_ctor_get(v_b_2979_, 1);
lean_inc_ref(v_expr_3007_);
lean_dec_ref_known(v_b_2979_, 2);
v_b_2979_ = v_expr_3007_;
goto _start;
}
case 7:
{
lean_object* v_binderType_3009_; lean_object* v_body_3010_; lean_object* v_binderType_3011_; lean_object* v_body_3012_; 
v_binderType_3009_ = lean_ctor_get(v_a_2978_, 1);
lean_inc_ref(v_binderType_3009_);
v_body_3010_ = lean_ctor_get(v_a_2978_, 2);
lean_inc_ref(v_body_3010_);
lean_dec_ref_known(v_a_2978_, 3);
v_binderType_3011_ = lean_ctor_get(v_b_2979_, 1);
lean_inc_ref(v_binderType_3011_);
v_body_3012_ = lean_ctor_get(v_b_2979_, 2);
lean_inc_ref(v_body_3012_);
lean_dec_ref_known(v_b_2979_, 3);
v_d_u2081_2982_ = v_binderType_3009_;
v_b_u2081_2983_ = v_body_3010_;
v_d_u2082_2984_ = v_binderType_3011_;
v_b_u2082_2985_ = v_body_3012_;
goto v___jp_2981_;
}
default: 
{
lean_dec_ref_known(v_a_2978_, 3);
lean_dec_ref(v_b_2979_);
return v___y_2990_;
}
}
}
case 6:
{
switch(lean_obj_tag(v_b_2979_))
{
case 10:
{
lean_object* v_expr_3013_; 
v_expr_3013_ = lean_ctor_get(v_b_2979_, 1);
lean_inc_ref(v_expr_3013_);
lean_dec_ref_known(v_b_2979_, 2);
v_b_2979_ = v_expr_3013_;
goto _start;
}
case 6:
{
lean_object* v_binderType_3015_; lean_object* v_body_3016_; lean_object* v_binderType_3017_; lean_object* v_body_3018_; 
v_binderType_3015_ = lean_ctor_get(v_a_2978_, 1);
lean_inc_ref(v_binderType_3015_);
v_body_3016_ = lean_ctor_get(v_a_2978_, 2);
lean_inc_ref(v_body_3016_);
lean_dec_ref_known(v_a_2978_, 3);
v_binderType_3017_ = lean_ctor_get(v_b_2979_, 1);
lean_inc_ref(v_binderType_3017_);
v_body_3018_ = lean_ctor_get(v_b_2979_, 2);
lean_inc_ref(v_body_3018_);
lean_dec_ref_known(v_b_2979_, 3);
v_d_u2081_2982_ = v_binderType_3015_;
v_b_u2081_2983_ = v_body_3016_;
v_d_u2082_2984_ = v_binderType_3017_;
v_b_u2082_2985_ = v_body_3018_;
goto v___jp_2981_;
}
default: 
{
lean_dec_ref_known(v_a_2978_, 3);
lean_dec_ref(v_b_2979_);
return v___y_2990_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_b_2979_))
{
case 10:
{
lean_object* v_expr_3019_; 
v_expr_3019_ = lean_ctor_get(v_b_2979_, 1);
lean_inc_ref(v_expr_3019_);
lean_dec_ref_known(v_b_2979_, 2);
v_b_2979_ = v_expr_3019_;
goto _start;
}
case 3:
{
lean_object* v_u_3021_; lean_object* v_u_3022_; uint8_t v___x_3023_; 
v_u_3021_ = lean_ctor_get(v_a_2978_, 0);
lean_inc(v_u_3021_);
lean_dec_ref_known(v_a_2978_, 1);
v_u_3022_ = lean_ctor_get(v_b_2979_, 0);
lean_inc(v_u_3022_);
lean_dec_ref_known(v_b_2979_, 1);
v___x_3023_ = l_Lean_Level_isEquiv(v_u_3021_, v_u_3022_);
lean_dec(v_u_3022_);
lean_dec(v_u_3021_);
return v___x_3023_;
}
default: 
{
lean_dec_ref_known(v_a_2978_, 1);
lean_dec_ref(v_b_2979_);
return v___y_2990_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_b_2979_))
{
case 10:
{
lean_object* v_expr_3024_; 
v_expr_3024_ = lean_ctor_get(v_b_2979_, 1);
lean_inc_ref(v_expr_3024_);
lean_dec_ref_known(v_b_2979_, 2);
v_b_2979_ = v_expr_3024_;
goto _start;
}
case 4:
{
lean_object* v_declName_3026_; lean_object* v_us_3027_; lean_object* v_declName_3028_; lean_object* v_us_3029_; uint8_t v___x_3030_; 
v_declName_3026_ = lean_ctor_get(v_a_2978_, 0);
lean_inc(v_declName_3026_);
v_us_3027_ = lean_ctor_get(v_a_2978_, 1);
lean_inc(v_us_3027_);
lean_dec_ref_known(v_a_2978_, 2);
v_declName_3028_ = lean_ctor_get(v_b_2979_, 0);
lean_inc(v_declName_3028_);
v_us_3029_ = lean_ctor_get(v_b_2979_, 1);
lean_inc(v_us_3029_);
lean_dec_ref_known(v_b_2979_, 2);
v___x_3030_ = lean_name_eq(v_declName_3026_, v_declName_3028_);
lean_dec(v_declName_3028_);
lean_dec(v_declName_3026_);
if (v___x_3030_ == 0)
{
lean_dec(v_us_3029_);
lean_dec(v_us_3027_);
return v___x_2980_;
}
else
{
uint8_t v___x_3031_; 
v___x_3031_ = l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(v_us_3027_, v_us_3029_);
lean_dec(v_us_3029_);
lean_dec(v_us_3027_);
return v___x_3031_;
}
}
default: 
{
lean_dec_ref_known(v_a_2978_, 2);
lean_dec_ref(v_b_2979_);
return v___y_2990_;
}
}
}
default: 
{
if (lean_obj_tag(v_b_2979_) == 10)
{
lean_object* v_expr_3032_; 
v_expr_3032_ = lean_ctor_get(v_b_2979_, 1);
lean_inc_ref(v_expr_3032_);
lean_dec_ref_known(v_b_2979_, 2);
v_b_2979_ = v_expr_3032_;
goto _start;
}
else
{
lean_dec_ref(v_b_2979_);
lean_dec_ref(v_a_2978_);
return v___y_2990_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_b_2979_);
lean_dec_ref(v_a_2978_);
return v___x_2988_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_eqvTypes_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2978_ = stack[0].m_obj;
lean_object* v_b_2979_ = stack[1].m_obj;
uint8_t v_res_3036_;
v_res_3036_ = l_Lean_Compiler_LCNF_eqvTypes(v_a_2978_, v_b_2979_);
stack->m_num = v_res_3036_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eqvTypes___boxed(lean_object* v_a_3037_, lean_object* v_b_3038_){
_start:
{
uint8_t v_res_3039_; lean_object* v_r_3040_; 
v_res_3039_ = l_Lean_Compiler_LCNF_eqvTypes(v_a_3037_, v_b_3038_);
v_r_3040_ = lean_box(v_res_3039_);
return v_r_3040_;
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
