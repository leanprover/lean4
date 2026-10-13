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
lean_object* v___x_511_; lean_object* v_ngen_512_; lean_object* v_namePrefix_513_; lean_object* v_idx_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_544_; 
v___x_511_ = lean_st_ref_get(v___y_509_);
v_ngen_512_ = lean_ctor_get(v___x_511_, 2);
lean_inc_ref(v_ngen_512_);
lean_dec(v___x_511_);
v_namePrefix_513_ = lean_ctor_get(v_ngen_512_, 0);
v_idx_514_ = lean_ctor_get(v_ngen_512_, 1);
v_isSharedCheck_544_ = !lean_is_exclusive(v_ngen_512_);
if (v_isSharedCheck_544_ == 0)
{
v___x_516_ = v_ngen_512_;
v_isShared_517_ = v_isSharedCheck_544_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_idx_514_);
lean_inc(v_namePrefix_513_);
lean_dec(v_ngen_512_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_544_;
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
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_namePrefix_513_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v___x_520_);
v___x_522_ = v_reuseFailAlloc_543_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v_env_524_; lean_object* v_nextMacroScope_525_; lean_object* v_auxDeclNGen_526_; lean_object* v_traceState_527_; lean_object* v_cache_528_; lean_object* v_recordedDeps_529_; lean_object* v_messages_530_; lean_object* v_infoState_531_; lean_object* v_snapshotTasks_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_541_; 
v___x_523_ = lean_st_ref_take(v___y_509_);
v_env_524_ = lean_ctor_get(v___x_523_, 0);
v_nextMacroScope_525_ = lean_ctor_get(v___x_523_, 1);
v_auxDeclNGen_526_ = lean_ctor_get(v___x_523_, 3);
v_traceState_527_ = lean_ctor_get(v___x_523_, 4);
v_cache_528_ = lean_ctor_get(v___x_523_, 5);
v_recordedDeps_529_ = lean_ctor_get(v___x_523_, 6);
v_messages_530_ = lean_ctor_get(v___x_523_, 7);
v_infoState_531_ = lean_ctor_get(v___x_523_, 8);
v_snapshotTasks_532_ = lean_ctor_get(v___x_523_, 9);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_541_ == 0)
{
lean_object* v_unused_542_; 
v_unused_542_ = lean_ctor_get(v___x_523_, 2);
lean_dec(v_unused_542_);
v___x_534_ = v___x_523_;
v_isShared_535_ = v_isSharedCheck_541_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_snapshotTasks_532_);
lean_inc(v_infoState_531_);
lean_inc(v_messages_530_);
lean_inc(v_recordedDeps_529_);
lean_inc(v_cache_528_);
lean_inc(v_traceState_527_);
lean_inc(v_auxDeclNGen_526_);
lean_inc(v_nextMacroScope_525_);
lean_inc(v_env_524_);
lean_dec(v___x_523_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_541_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 2, v___x_522_);
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_env_524_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_nextMacroScope_525_);
lean_ctor_set(v_reuseFailAlloc_540_, 2, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_540_, 3, v_auxDeclNGen_526_);
lean_ctor_set(v_reuseFailAlloc_540_, 4, v_traceState_527_);
lean_ctor_set(v_reuseFailAlloc_540_, 5, v_cache_528_);
lean_ctor_set(v_reuseFailAlloc_540_, 6, v_recordedDeps_529_);
lean_ctor_set(v_reuseFailAlloc_540_, 7, v_messages_530_);
lean_ctor_set(v_reuseFailAlloc_540_, 8, v_infoState_531_);
lean_ctor_set(v_reuseFailAlloc_540_, 9, v_snapshotTasks_532_);
v___x_537_ = v_reuseFailAlloc_540_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_st_ref_put(v___y_509_, v___x_537_);
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v_r_518_);
return v___x_539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg___boxed(lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(v___y_545_);
lean_dec(v___y_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_554_; lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
v___x_554_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(v___y_552_);
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0___boxed(lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec_ref(v___y_563_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(lean_object* v_msg_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v___x_577_; lean_object* v_toApplicative_578_; lean_object* v_toFunctor_579_; lean_object* v_toSeq_580_; lean_object* v_toSeqLeft_581_; lean_object* v_toSeqRight_582_; lean_object* v___f_583_; lean_object* v___f_584_; lean_object* v___f_585_; lean_object* v___f_586_; lean_object* v___x_587_; lean_object* v___f_588_; lean_object* v___f_589_; lean_object* v___f_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___x_6179__overap_598_; lean_object* v___x_599_; 
v___x_577_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_578_ = lean_ctor_get(v___x_577_, 0);
v_toFunctor_579_ = lean_ctor_get(v_toApplicative_578_, 0);
v_toSeq_580_ = lean_ctor_get(v_toApplicative_578_, 2);
v_toSeqLeft_581_ = lean_ctor_get(v_toApplicative_578_, 3);
v_toSeqRight_582_ = lean_ctor_get(v_toApplicative_578_, 4);
v___f_583_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_584_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_579_, 2);
v___f_585_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_585_, 0, v_toFunctor_579_);
v___f_586_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_586_, 0, v_toFunctor_579_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v___f_585_);
lean_ctor_set(v___x_587_, 1, v___f_586_);
lean_inc(v_toSeqRight_582_);
v___f_588_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_588_, 0, v_toSeqRight_582_);
lean_inc(v_toSeqLeft_581_);
v___f_589_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_589_, 0, v_toSeqLeft_581_);
lean_inc(v_toSeq_580_);
v___f_590_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_590_, 0, v_toSeq_580_);
v___x_591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_591_, 0, v___x_587_);
lean_ctor_set(v___x_591_, 1, v___f_583_);
lean_ctor_set(v___x_591_, 2, v___f_590_);
lean_ctor_set(v___x_591_, 3, v___f_589_);
lean_ctor_set(v___x_591_, 4, v___f_588_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
lean_ctor_set(v___x_592_, 1, v___f_584_);
v___x_593_ = l_StateRefT_x27_instMonad___redArg(v___x_592_);
v___x_594_ = l_Lean_instInhabitedExpr;
v___x_595_ = l_instInhabitedOfMonad___redArg(v___x_593_, v___x_594_);
v___f_596_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_596_, 0, v___x_595_);
v___f_597_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_597_, 0, v___f_596_);
v___x_6179__overap_598_ = lean_panic_fn_borrowed(v___f_597_, v_msg_570_);
lean_dec_ref(v___f_597_);
lean_inc(v___y_575_);
lean_inc_ref(v___y_574_);
lean_inc(v___y_573_);
lean_inc_ref(v___y_572_);
lean_inc_ref(v___y_571_);
v___x_599_ = lean_apply_6(v___x_6179__overap_598_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, lean_box(0));
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2___boxed(lean_object* v_msg_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(v_msg_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec_ref(v___y_601_);
return v_res_607_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(lean_object* v_upperBound_610_, lean_object* v___x_611_, lean_object* v_a_612_, lean_object* v_b_613_){
_start:
{
lean_object* v_a_616_; uint8_t v___x_620_; 
v___x_620_ = lean_nat_dec_lt(v_a_612_, v_upperBound_610_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
lean_dec(v_a_612_);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v_b_613_);
return v___x_621_;
}
else
{
lean_object* v_snd_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_658_; 
v_snd_622_ = lean_ctor_get(v_b_613_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v_b_613_);
if (v_isSharedCheck_658_ == 0)
{
lean_object* v_unused_659_; 
v_unused_659_ = lean_ctor_get(v_b_613_, 0);
lean_dec(v_unused_659_);
v___x_624_ = v_b_613_;
v_isShared_625_ = v_isSharedCheck_658_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_snd_622_);
lean_dec(v_b_613_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_658_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v_fst_626_; lean_object* v_snd_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_657_; 
v_fst_626_ = lean_ctor_get(v_snd_622_, 0);
v_snd_627_ = lean_ctor_get(v_snd_622_, 1);
v_isSharedCheck_657_ = !lean_is_exclusive(v_snd_622_);
if (v_isSharedCheck_657_ == 0)
{
v___x_629_ = v_snd_622_;
v_isShared_630_ = v_isSharedCheck_657_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_snd_627_);
lean_inc(v_fst_626_);
lean_dec(v_snd_622_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_657_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_box(0);
v___x_632_ = l_Lean_Expr_headBeta(v_snd_627_);
if (lean_obj_tag(v___x_632_) == 7)
{
lean_object* v_body_633_; lean_object* v___x_635_; 
v_body_633_ = lean_ctor_get(v___x_632_, 2);
lean_inc_ref(v_body_633_);
lean_dec_ref_known(v___x_632_, 3);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v_body_633_);
v___x_635_ = v___x_629_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_fst_626_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_body_633_);
v___x_635_ = v_reuseFailAlloc_639_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_637_; 
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 1, v___x_635_);
lean_ctor_set(v___x_624_, 0, v___x_631_);
v___x_637_ = v___x_624_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
v_a_616_ = v___x_637_;
goto v___jp_615_;
}
}
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_expr_instantiate_rev_range(v___x_632_, v_fst_626_, v_a_612_, v___x_611_);
lean_dec_ref(v___x_632_);
v___x_641_ = l_Lean_Expr_headBeta(v___x_640_);
if (lean_obj_tag(v___x_641_) == 7)
{
lean_object* v_body_642_; lean_object* v___x_644_; 
lean_dec(v_fst_626_);
v_body_642_ = lean_ctor_get(v___x_641_, 2);
lean_inc_ref(v_body_642_);
lean_dec_ref_known(v___x_641_, 3);
lean_inc(v_a_612_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v_body_642_);
lean_ctor_set(v___x_629_, 0, v_a_612_);
v___x_644_ = v___x_629_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_612_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_body_642_);
v___x_644_ = v_reuseFailAlloc_648_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_646_; 
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 1, v___x_644_);
lean_ctor_set(v___x_624_, 0, v___x_631_);
v___x_646_ = v___x_624_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
v_a_616_ = v___x_646_;
goto v___jp_615_;
}
}
}
else
{
lean_object* v___x_649_; lean_object* v___x_651_; 
lean_dec(v_a_612_);
v___x_649_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v___x_641_);
v___x_651_ = v___x_629_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_fst_626_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v___x_641_);
v___x_651_ = v_reuseFailAlloc_656_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_653_; 
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 1, v___x_651_);
lean_ctor_set(v___x_624_, 0, v___x_649_);
v___x_653_ = v___x_624_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v___x_651_);
v___x_653_ = v_reuseFailAlloc_655_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_654_; 
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
return v___x_654_;
}
}
}
}
}
}
}
v___jp_615_:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = lean_nat_add(v_a_612_, v___x_617_);
lean_dec(v_a_612_);
v_a_612_ = v___x_618_;
v_b_613_ = v_a_616_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___boxed(lean_object* v_upperBound_660_, lean_object* v___x_661_, lean_object* v_a_662_, lean_object* v_b_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v_upperBound_660_, v___x_661_, v_a_662_, v_b_663_);
lean_dec_ref(v___x_661_);
lean_dec(v_upperBound_660_);
return v_res_665_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0(void){
_start:
{
lean_object* v___x_668_; lean_object* v_dummy_669_; 
v___x_668_ = lean_box(0);
v_dummy_669_ = l_Lean_Expr_sort___override(v___x_668_);
return v_dummy_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(lean_object* v_e_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_j_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_j_677_ = lean_unsigned_to_nat(0u);
v___x_678_ = l_Lean_Expr_getAppFn(v_e_670_);
v___x_679_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v___x_678_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v_dummy_681_; lean_object* v_nargs_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_679_, 1);
v_dummy_681_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0);
v_nargs_682_ = l_Lean_Expr_getAppNumArgs(v_e_670_);
lean_inc(v_nargs_682_);
v___x_683_ = lean_mk_array(v_nargs_682_, v_dummy_681_);
v___x_684_ = lean_unsigned_to_nat(1u);
v___x_685_ = lean_nat_sub(v_nargs_682_, v___x_684_);
lean_dec(v_nargs_682_);
v___x_686_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_670_, v___x_683_, v___x_685_);
v___x_687_ = lean_array_get_size(v___x_686_);
v___x_688_ = lean_box(0);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v_j_677_);
lean_ctor_set(v___x_689_, 1, v_a_680_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_688_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v___x_687_, v___x_686_, v_j_677_, v___x_690_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_709_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_709_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_709_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_709_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_fst_696_; 
v_fst_696_ = lean_ctor_get(v_a_692_, 0);
if (lean_obj_tag(v_fst_696_) == 0)
{
lean_object* v_snd_697_; lean_object* v_fst_698_; lean_object* v_snd_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v_snd_697_ = lean_ctor_get(v_a_692_, 1);
lean_inc(v_snd_697_);
lean_dec(v_a_692_);
v_fst_698_ = lean_ctor_get(v_snd_697_, 0);
lean_inc(v_fst_698_);
v_snd_699_ = lean_ctor_get(v_snd_697_, 1);
lean_inc(v_snd_699_);
lean_dec(v_snd_697_);
v___x_700_ = lean_expr_instantiate_rev_range(v_snd_699_, v_fst_698_, v___x_687_, v___x_686_);
lean_dec_ref(v___x_686_);
lean_dec(v_fst_698_);
lean_dec(v_snd_699_);
v___x_701_ = l_Lean_Expr_headBeta(v___x_700_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_701_);
v___x_703_ = v___x_694_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
else
{
lean_object* v_val_705_; lean_object* v___x_707_; 
lean_inc_ref(v_fst_696_);
lean_dec(v_a_692_);
lean_dec_ref(v___x_686_);
v_val_705_ = lean_ctor_get(v_fst_696_, 0);
lean_inc(v_val_705_);
lean_dec_ref_known(v_fst_696_, 1);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v_val_705_);
v___x_707_ = v___x_694_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_val_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec_ref(v___x_686_);
v_a_710_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_691_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_691_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
else
{
lean_dec_ref(v_e_670_);
return v___x_679_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(lean_object* v_e_718_, lean_object* v_fvars_719_, lean_object* v_all_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
switch(lean_obj_tag(v_e_718_))
{
case 6:
{
lean_object* v_binderName_727_; lean_object* v_binderType_728_; lean_object* v_body_729_; uint8_t v_binderInfo_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_binderName_727_ = lean_ctor_get(v_e_718_, 0);
lean_inc(v_binderName_727_);
v_binderType_728_ = lean_ctor_get(v_e_718_, 1);
lean_inc_ref(v_binderType_728_);
v_body_729_ = lean_ctor_get(v_e_718_, 2);
lean_inc_ref(v_body_729_);
v_binderInfo_730_ = lean_ctor_get_uint8(v_e_718_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_718_, 3);
v___x_731_ = lean_expr_instantiate_rev(v_binderType_728_, v_all_720_);
lean_dec_ref(v_binderType_728_);
v___x_732_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; uint8_t v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc_n(v_a_733_, 2);
lean_dec_ref_known(v___x_732_, 1);
v___x_734_ = l_Lean_Expr_fvar___override(v_a_733_);
v___x_735_ = 0;
v___x_736_ = l_Lean_LocalContext_mkLocalDecl(v_a_721_, v_a_733_, v_binderName_727_, v___x_731_, v_binderInfo_730_, v___x_735_);
lean_inc_ref(v___x_734_);
v___x_737_ = lean_array_push(v_fvars_719_, v___x_734_);
v___x_738_ = lean_array_push(v_all_720_, v___x_734_);
v_e_718_ = v_body_729_;
v_fvars_719_ = v___x_737_;
v_all_720_ = v___x_738_;
v_a_721_ = v___x_736_;
goto _start;
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec_ref(v___x_731_);
lean_dec_ref(v_body_729_);
lean_dec(v_binderName_727_);
lean_dec_ref(v_a_721_);
lean_dec_ref(v_all_720_);
lean_dec_ref(v_fvars_719_);
v_a_740_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_732_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_732_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
case 8:
{
lean_object* v_declName_748_; lean_object* v_type_749_; lean_object* v_body_750_; lean_object* v___x_751_; uint8_t v___x_752_; lean_object* v___x_753_; 
v_declName_748_ = lean_ctor_get(v_e_718_, 0);
lean_inc(v_declName_748_);
v_type_749_ = lean_ctor_get(v_e_718_, 1);
lean_inc_ref(v_type_749_);
v_body_750_ = lean_ctor_get(v_e_718_, 3);
lean_inc_ref(v_body_750_);
lean_dec_ref_known(v_e_718_, 4);
v___x_751_ = lean_expr_instantiate_rev(v_type_749_, v_all_720_);
lean_dec_ref(v_type_749_);
v___x_752_ = 0;
v___x_753_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v___x_755_; uint8_t v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc_n(v_a_754_, 2);
lean_dec_ref_known(v___x_753_, 1);
v___x_755_ = l_Lean_Expr_fvar___override(v_a_754_);
v___x_756_ = 0;
v___x_757_ = l_Lean_LocalContext_mkLocalDecl(v_a_721_, v_a_754_, v_declName_748_, v___x_751_, v___x_752_, v___x_756_);
v___x_758_ = lean_array_push(v_all_720_, v___x_755_);
v_e_718_ = v_body_750_;
v_all_720_ = v___x_758_;
v_a_721_ = v___x_757_;
goto _start;
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec_ref(v___x_751_);
lean_dec_ref(v_body_750_);
lean_dec(v_declName_748_);
lean_dec_ref(v_a_721_);
lean_dec_ref(v_all_720_);
lean_dec_ref(v_fvars_719_);
v_a_760_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_753_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_753_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
default: 
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_expr_instantiate_rev(v_e_718_, v_all_720_);
lean_dec_ref(v_all_720_);
lean_dec_ref(v_e_718_);
v___x_769_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v___x_768_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_771_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref_known(v___x_769_, 1);
v___x_771_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v_fvars_719_, v_a_770_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_770_);
lean_dec_ref(v_fvars_719_);
return v___x_771_;
}
else
{
lean_dec_ref(v_a_721_);
lean_dec_ref(v_fvars_719_);
return v___x_769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(lean_object* v_e_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0));
lean_inc_ref(v_a_773_);
v___x_780_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(v_e_772_, v___x_779_, v___x_779_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
return v___x_780_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_784_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2));
v___x_785_ = lean_unsigned_to_nat(73u);
v___x_786_ = lean_unsigned_to_nat(135u);
v___x_787_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__1));
v___x_788_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_789_ = l_mkPanicMessageWithDecl(v___x_788_, v___x_787_, v___x_786_, v___x_785_, v___x_784_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType(lean_object* v_e_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
switch(lean_obj_tag(v_e_790_))
{
case 1:
{
lean_object* v_fvarId_797_; lean_object* v___x_798_; 
v_fvarId_797_ = lean_ctor_get(v_e_790_, 0);
lean_inc(v_fvarId_797_);
lean_dec_ref_known(v_e_790_, 1);
v___x_798_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_fvarId_797_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
return v___x_798_;
}
case 3:
{
lean_object* v_u_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_u_799_ = lean_ctor_get(v_e_790_, 0);
lean_inc(v_u_799_);
lean_dec_ref_known(v_e_790_, 1);
v___x_800_ = l_Lean_Level_succ___override(v_u_799_);
v___x_801_ = l_Lean_Expr_sort___override(v___x_800_);
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
case 4:
{
lean_object* v_declName_803_; lean_object* v_us_804_; lean_object* v___x_805_; 
v_declName_803_ = lean_ctor_get(v_e_790_, 0);
lean_inc(v_declName_803_);
v_us_804_ = lean_ctor_get(v_e_790_, 1);
lean_inc(v_us_804_);
lean_dec_ref_known(v_e_790_, 2);
v___x_805_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(v_declName_803_, v_us_804_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
return v___x_805_;
}
case 5:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(v_e_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
return v___x_806_;
}
case 6:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(v_e_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
return v___x_807_;
}
case 7:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(v_e_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
return v___x_808_;
}
default: 
{
lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec_ref(v_e_790_);
v___x_809_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3, &l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3);
v___x_810_ = l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(v___x_809_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
return v___x_810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(lean_object* v_type_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_type_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_832_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_832_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_832_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_832_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
if (lean_obj_tag(v_a_819_) == 3)
{
lean_object* v_u_823_; lean_object* v___x_824_; lean_object* v___x_826_; 
v_u_823_ = lean_ctor_get(v_a_819_, 0);
lean_inc(v_u_823_);
lean_dec_ref_known(v_a_819_, 1);
v___x_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_824_, 0, v_u_823_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_824_);
v___x_826_ = v___x_821_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
else
{
lean_object* v___x_828_; lean_object* v___x_830_; 
lean_dec(v_a_819_);
v___x_828_ = lean_box(0);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_828_);
v___x_830_ = v___x_821_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
v_a_833_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_818_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_818_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(lean_object* v_as_843_, size_t v_sz_844_, size_t v_i_845_, lean_object* v_b_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
uint8_t v___x_853_; 
v___x_853_ = lean_usize_dec_lt(v_i_845_, v_sz_844_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; 
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v_b_846_);
return v___x_854_;
}
else
{
lean_object* v_snd_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_900_; 
v_snd_855_ = lean_ctor_get(v_b_846_, 1);
v_isSharedCheck_900_ = !lean_is_exclusive(v_b_846_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; 
v_unused_901_ = lean_ctor_get(v_b_846_, 0);
lean_dec(v_unused_901_);
v___x_857_ = v_b_846_;
v_isShared_858_ = v_isSharedCheck_900_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_snd_855_);
lean_dec(v_b_846_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_900_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v_a_860_; lean_object* v___x_861_; 
v___x_859_ = lean_box(0);
v_a_860_ = lean_array_uget_borrowed(v_as_843_, v_i_845_);
lean_inc(v_a_860_);
v___x_861_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_a_860_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_863_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref_known(v___x_861_, 1);
v___x_863_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(v_a_862_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_883_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_883_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_883_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_883_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
if (lean_obj_tag(v_a_864_) == 1)
{
lean_object* v_val_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
lean_del_object(v___x_866_);
v_val_868_ = lean_ctor_get(v_a_864_, 0);
lean_inc(v_val_868_);
lean_dec_ref_known(v_a_864_, 1);
v___x_869_ = l_Lean_mkLevelIMax_x27(v_val_868_, v_snd_855_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 1, v___x_869_);
lean_ctor_set(v___x_857_, 0, v___x_859_);
v___x_871_ = v___x_857_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_869_);
v___x_871_ = v_reuseFailAlloc_875_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
size_t v___x_872_; size_t v___x_873_; 
v___x_872_ = ((size_t)1ULL);
v___x_873_ = lean_usize_add(v_i_845_, v___x_872_);
v_i_845_ = v___x_873_;
v_b_846_ = v___x_871_;
goto _start;
}
}
else
{
lean_object* v___x_876_; lean_object* v___x_878_; 
lean_dec(v_a_864_);
v___x_876_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_876_);
v___x_878_ = v___x_857_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_snd_855_);
v___x_878_ = v_reuseFailAlloc_882_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_880_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_878_);
v___x_880_ = v___x_866_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_del_object(v___x_857_);
lean_dec(v_snd_855_);
v_a_884_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_863_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_863_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_del_object(v___x_857_);
lean_dec(v_snd_855_);
v_a_892_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_861_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_861_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(lean_object* v_e_902_, lean_object* v_fvars_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
if (lean_obj_tag(v_e_902_) == 7)
{
lean_object* v_binderName_910_; lean_object* v_binderType_911_; lean_object* v_body_912_; uint8_t v_binderInfo_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_binderName_910_ = lean_ctor_get(v_e_902_, 0);
lean_inc(v_binderName_910_);
v_binderType_911_ = lean_ctor_get(v_e_902_, 1);
lean_inc_ref(v_binderType_911_);
v_body_912_ = lean_ctor_get(v_e_902_, 2);
lean_inc_ref(v_body_912_);
v_binderInfo_913_ = lean_ctor_get_uint8(v_e_902_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_902_, 3);
v___x_914_ = lean_expr_instantiate_rev(v_binderType_911_, v_fvars_903_);
lean_dec_ref(v_binderType_911_);
v___x_915_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_917_; uint8_t v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc_n(v_a_916_, 2);
lean_dec_ref_known(v___x_915_, 1);
v___x_917_ = l_Lean_Expr_fvar___override(v_a_916_);
v___x_918_ = 0;
v___x_919_ = l_Lean_LocalContext_mkLocalDecl(v_a_904_, v_a_916_, v_binderName_910_, v___x_914_, v_binderInfo_913_, v___x_918_);
v___x_920_ = lean_array_push(v_fvars_903_, v___x_917_);
v_e_902_ = v_body_912_;
v_fvars_903_ = v___x_920_;
v_a_904_ = v___x_919_;
goto _start;
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec_ref(v___x_914_);
lean_dec_ref(v_body_912_);
lean_dec(v_binderName_910_);
lean_dec_ref(v_a_904_);
lean_dec_ref(v_fvars_903_);
v_a_922_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_915_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_915_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v_e_930_; lean_object* v___x_931_; 
v_e_930_ = lean_expr_instantiate_rev(v_e_902_, v_fvars_903_);
lean_dec_ref(v_e_902_);
v___x_931_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(v_e_930_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_971_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_971_ == 0)
{
v___x_934_ = v___x_931_;
v_isShared_935_ = v_isSharedCheck_971_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_931_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_971_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
if (lean_obj_tag(v_a_932_) == 1)
{
lean_object* v_val_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; size_t v_sz_940_; size_t v___x_941_; lean_object* v___x_942_; 
lean_del_object(v___x_934_);
v_val_936_ = lean_ctor_get(v_a_932_, 0);
lean_inc(v_val_936_);
lean_dec_ref_known(v_a_932_, 1);
v___x_937_ = l_Array_reverse___redArg(v_fvars_903_);
v___x_938_ = lean_box(0);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v_val_936_);
v_sz_940_ = lean_array_size(v___x_937_);
v___x_941_ = ((size_t)0ULL);
v___x_942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(v___x_937_, v_sz_940_, v___x_941_, v___x_939_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
lean_dec_ref(v_a_904_);
lean_dec_ref(v___x_937_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_958_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_958_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_958_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_958_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v_fst_947_; 
v_fst_947_ = lean_ctor_get(v_a_943_, 0);
if (lean_obj_tag(v_fst_947_) == 0)
{
lean_object* v_snd_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
v_snd_948_ = lean_ctor_get(v_a_943_, 1);
lean_inc(v_snd_948_);
lean_dec(v_a_943_);
v___x_949_ = l_Lean_Level_normalize(v_snd_948_);
lean_dec(v_snd_948_);
v___x_950_ = l_Lean_Expr_sort___override(v___x_949_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_950_);
v___x_952_ = v___x_945_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
else
{
lean_object* v_val_954_; lean_object* v___x_956_; 
lean_inc_ref(v_fst_947_);
lean_dec(v_a_943_);
v_val_954_ = lean_ctor_get(v_fst_947_, 0);
lean_inc(v_val_954_);
lean_dec_ref_known(v_fst_947_, 1);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v_val_954_);
v___x_956_ = v___x_945_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_val_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
v_a_959_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_942_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_942_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
else
{
lean_object* v___x_967_; lean_object* v___x_969_; 
lean_dec(v_a_932_);
lean_dec_ref(v_a_904_);
lean_dec_ref(v_fvars_903_);
v___x_967_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_967_);
v___x_969_ = v___x_934_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
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
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_dec_ref(v_a_904_);
lean_dec_ref(v_fvars_903_);
v_a_972_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_931_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_931_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(lean_object* v_e_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0));
lean_inc_ref(v_a_981_);
v___x_988_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(v_e_980_, v___x_987_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___boxed(lean_object* v_e_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(v_e_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec_ref(v_a_990_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType___boxed(lean_object* v_e_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(v_e_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
lean_dec(v_a_1002_);
lean_dec_ref(v_a_1001_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec_ref(v_a_998_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f___boxed(lean_object* v_type_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(v_type_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec_ref(v_a_1006_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType___boxed(lean_object* v_e_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_e_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec_ref(v_a_1014_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___boxed(lean_object* v_as_1021_, lean_object* v_sz_1022_, lean_object* v_i_1023_, lean_object* v_b_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
size_t v_sz_boxed_1031_; size_t v_i_boxed_1032_; lean_object* v_res_1033_; 
v_sz_boxed_1031_ = lean_unbox_usize(v_sz_1022_);
lean_dec(v_sz_1022_);
v_i_boxed_1032_ = lean_unbox_usize(v_i_1023_);
lean_dec(v_i_1023_);
v_res_1033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(v_as_1021_, v_sz_boxed_1031_, v_i_boxed_1032_, v_b_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec_ref(v_as_1021_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___boxed(lean_object* v_e_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(v_e_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec_ref(v_a_1035_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go___boxed(lean_object* v_e_1042_, lean_object* v_fvars_1043_, lean_object* v_all_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(v_e_1042_, v_fvars_1043_, v_all_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go___boxed(lean_object* v_e_1052_, lean_object* v_fvars_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(v_e_1052_, v_fvars_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3(lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(v___y_1065_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___boxed(lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3(v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec_ref(v___y_1068_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9(lean_object* v_upperBound_1075_, lean_object* v___x_1076_, lean_object* v_inst_1077_, lean_object* v_R_1078_, lean_object* v_a_1079_, lean_object* v_b_1080_, lean_object* v_c_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v_upperBound_1075_, v___x_1076_, v_a_1079_, v_b_1080_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___boxed(lean_object* v_upperBound_1089_, lean_object* v___x_1090_, lean_object* v_inst_1091_, lean_object* v_R_1092_, lean_object* v_a_1093_, lean_object* v_b_1094_, lean_object* v_c_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9(v_upperBound_1089_, v___x_1090_, v_inst_1091_, v_R_1092_, v_a_1093_, v_b_1094_, v_c_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec_ref(v___x_1090_);
lean_dec(v_upperBound_1089_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(lean_object* v_arg_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
switch(lean_obj_tag(v_arg_1103_))
{
case 0:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
return v___x_1111_;
}
case 1:
{
lean_object* v_fvarId_1112_; lean_object* v___x_1113_; 
v_fvarId_1112_ = lean_ctor_get(v_arg_1103_, 0);
lean_inc(v_fvarId_1112_);
lean_dec_ref_known(v_arg_1103_, 1);
v___x_1113_ = l_Lean_Compiler_LCNF_getType(v_fvarId_1112_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
return v___x_1113_;
}
default: 
{
lean_object* v_expr_1114_; lean_object* v___x_1115_; 
v_expr_1114_ = lean_ctor_get(v_arg_1103_, 0);
lean_inc_ref(v_expr_1114_);
lean_dec_ref_known(v_arg_1103_, 1);
v___x_1115_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_expr_1114_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
return v___x_1115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferArgType___boxed(lean_object* v_arg_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(v_arg_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec_ref(v_a_1117_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(lean_object* v_upperBound_1124_, lean_object* v_args_1125_, lean_object* v_a_1126_, lean_object* v_b_1127_){
_start:
{
lean_object* v_a_1130_; uint8_t v___x_1134_; 
v___x_1134_ = lean_nat_dec_lt(v_a_1126_, v_upperBound_1124_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; 
lean_dec(v_a_1126_);
lean_dec_ref(v_args_1125_);
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v_b_1127_);
return v___x_1135_;
}
else
{
lean_object* v_snd_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1172_; 
v_snd_1136_ = lean_ctor_get(v_b_1127_, 1);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_b_1127_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; 
v_unused_1173_ = lean_ctor_get(v_b_1127_, 0);
lean_dec(v_unused_1173_);
v___x_1138_ = v_b_1127_;
v_isShared_1139_ = v_isSharedCheck_1172_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_snd_1136_);
lean_dec(v_b_1127_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1172_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v_fst_1140_; lean_object* v_snd_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1171_; 
v_fst_1140_ = lean_ctor_get(v_snd_1136_, 0);
v_snd_1141_ = lean_ctor_get(v_snd_1136_, 1);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_snd_1136_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1143_ = v_snd_1136_;
v_isShared_1144_ = v_isSharedCheck_1171_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_snd_1141_);
lean_inc(v_fst_1140_);
lean_dec(v_snd_1136_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1171_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_box(0);
v___x_1146_ = l_Lean_Expr_headBeta(v_snd_1141_);
if (lean_obj_tag(v___x_1146_) == 7)
{
lean_object* v_body_1147_; lean_object* v___x_1149_; 
v_body_1147_ = lean_ctor_get(v___x_1146_, 2);
lean_inc_ref(v_body_1147_);
lean_dec_ref_known(v___x_1146_, 3);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v_body_1147_);
v___x_1149_ = v___x_1143_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_fst_1140_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_body_1147_);
v___x_1149_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1151_; 
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v___x_1149_);
lean_ctor_set(v___x_1138_, 0, v___x_1145_);
v___x_1151_ = v___x_1138_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
v_a_1130_ = v___x_1151_;
goto v___jp_1129_;
}
}
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_inc_ref(v_args_1125_);
v___x_1154_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(v___x_1146_, v_fst_1140_, v_a_1126_, v_args_1125_);
lean_dec_ref(v___x_1146_);
v___x_1155_ = l_Lean_Expr_headBeta(v___x_1154_);
if (lean_obj_tag(v___x_1155_) == 7)
{
lean_object* v_body_1156_; lean_object* v___x_1158_; 
lean_dec(v_fst_1140_);
v_body_1156_ = lean_ctor_get(v___x_1155_, 2);
lean_inc_ref(v_body_1156_);
lean_dec_ref_known(v___x_1155_, 3);
lean_inc(v_a_1126_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v_body_1156_);
lean_ctor_set(v___x_1143_, 0, v_a_1126_);
v___x_1158_ = v___x_1143_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1126_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_body_1156_);
v___x_1158_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1160_; 
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v___x_1158_);
lean_ctor_set(v___x_1138_, 0, v___x_1145_);
v___x_1160_ = v___x_1138_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
v_a_1130_ = v___x_1160_;
goto v___jp_1129_;
}
}
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1165_; 
lean_dec(v_a_1126_);
lean_dec_ref(v_args_1125_);
v___x_1163_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v___x_1155_);
v___x_1165_ = v___x_1143_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_fst_1140_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v___x_1155_);
v___x_1165_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1167_; 
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v___x_1165_);
lean_ctor_set(v___x_1138_, 0, v___x_1163_);
v___x_1167_ = v___x_1138_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1163_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
}
}
}
}
}
}
v___jp_1129_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_unsigned_to_nat(1u);
v___x_1132_ = lean_nat_add(v_a_1126_, v___x_1131_);
lean_dec(v_a_1126_);
v_a_1126_ = v___x_1132_;
v_b_1127_ = v_a_1130_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg___boxed(lean_object* v_upperBound_1174_, lean_object* v_args_1175_, lean_object* v_a_1176_, lean_object* v_b_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v_upperBound_1174_, v_args_1175_, v_a_1176_, v_b_1177_);
lean_dec(v_upperBound_1174_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(lean_object* v_fType_1180_, lean_object* v_args_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1188_ = lean_array_get_size(v_args_1181_);
v___x_1189_ = lean_unsigned_to_nat(0u);
v___x_1190_ = lean_box(0);
v___x_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v_fType_1180_);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1190_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
lean_inc_ref(v_args_1181_);
v___x_1193_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v___x_1188_, v_args_1181_, v___x_1189_, v___x_1192_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1211_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1196_ = v___x_1193_;
v_isShared_1197_ = v_isSharedCheck_1211_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1193_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1211_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v_fst_1198_; 
v_fst_1198_ = lean_ctor_get(v_a_1194_, 0);
if (lean_obj_tag(v_fst_1198_) == 0)
{
lean_object* v_snd_1199_; lean_object* v_fst_1200_; lean_object* v_snd_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v_snd_1199_ = lean_ctor_get(v_a_1194_, 1);
lean_inc(v_snd_1199_);
lean_dec(v_a_1194_);
v_fst_1200_ = lean_ctor_get(v_snd_1199_, 0);
lean_inc(v_fst_1200_);
v_snd_1201_ = lean_ctor_get(v_snd_1199_, 1);
lean_inc(v_snd_1201_);
lean_dec(v_snd_1199_);
v___x_1202_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(v_snd_1201_, v_fst_1200_, v___x_1188_, v_args_1181_);
lean_dec(v_fst_1200_);
lean_dec(v_snd_1201_);
v___x_1203_ = l_Lean_Expr_headBeta(v___x_1202_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1203_);
v___x_1205_ = v___x_1196_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
else
{
lean_object* v_val_1207_; lean_object* v___x_1209_; 
lean_inc_ref(v_fst_1198_);
lean_dec(v_a_1194_);
lean_dec_ref(v_args_1181_);
v_val_1207_ = lean_ctor_get(v_fst_1198_, 0);
lean_inc(v_val_1207_);
lean_dec_ref_known(v_fst_1198_, 1);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v_val_1207_);
v___x_1209_ = v___x_1196_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_val_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec_ref(v_args_1181_);
v_a_1212_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1193_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1193_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore___boxed(lean_object* v_fType_1220_, lean_object* v_args_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_fType_1220_, v_args_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec_ref(v_a_1222_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0(lean_object* v_upperBound_1229_, lean_object* v_args_1230_, lean_object* v_inst_1231_, lean_object* v_R_1232_, lean_object* v_a_1233_, lean_object* v_b_1234_, lean_object* v_c_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v_upperBound_1229_, v_args_1230_, v_a_1233_, v_b_1234_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___boxed(lean_object* v_upperBound_1243_, lean_object* v_args_1244_, lean_object* v_inst_1245_, lean_object* v_R_1246_, lean_object* v_a_1247_, lean_object* v_b_1248_, lean_object* v_c_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0(v_upperBound_1243_, v_args_1244_, v_inst_1245_, v_R_1246_, v_a_1247_, v_b_1248_, v_c_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v_upperBound_1243_);
return v_res_1256_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0);
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
return v___x_1258_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1259_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1260_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0);
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
lean_ctor_set(v___x_1262_, 2, v___x_1261_);
lean_ctor_set(v___x_1262_, 3, v___x_1261_);
lean_ctor_set(v___x_1262_, 4, v___x_1260_);
lean_ctor_set(v___x_1262_, 5, v___x_1260_);
lean_ctor_set(v___x_1262_, 6, v___x_1260_);
lean_ctor_set(v___x_1262_, 7, v___x_1260_);
lean_ctor_set(v___x_1262_, 8, v___x_1260_);
lean_ctor_set(v___x_1262_, 9, v___x_1260_);
lean_ctor_set(v___x_1262_, 10, v___x_1260_);
lean_ctor_set(v___x_1262_, 11, v___x_1259_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(lean_object* v_msg_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_ref_1269_; lean_object* v___x_1270_; lean_object* v_env_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v_ref_1269_ = lean_ctor_get(v___y_1266_, 2);
v___x_1270_ = lean_st_ref_get(v___y_1267_);
v_env_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc_ref(v_env_1271_);
lean_dec(v___x_1270_);
v___x_1272_ = lean_st_ref_get(v___y_1265_);
v___x_1273_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1264_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1296_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1296_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1296_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v_lctx_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1294_; 
v_lctx_1278_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1294_ == 0)
{
lean_object* v_unused_1295_; 
v_unused_1295_ = lean_ctor_get(v___x_1272_, 1);
lean_dec(v_unused_1295_);
v___x_1280_ = v___x_1272_;
v_isShared_1281_ = v_isSharedCheck_1294_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_lctx_1278_);
lean_dec(v___x_1272_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1294_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
uint8_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1282_ = lean_unbox(v_a_1274_);
lean_dec(v_a_1274_);
v___x_1283_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1278_, v___x_1282_);
lean_dec_ref(v_lctx_1278_);
v___x_1284_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1266_);
v___x_1285_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1);
v___x_1286_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1286_, 0, v_env_1271_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
lean_ctor_set(v___x_1286_, 2, v___x_1283_);
lean_ctor_set(v___x_1286_, 3, v___x_1284_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set_tag(v___x_1280_, 3);
lean_ctor_set(v___x_1280_, 1, v_msg_1263_);
lean_ctor_set(v___x_1280_, 0, v___x_1286_);
v___x_1288_ = v___x_1280_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_msg_1263_);
v___x_1288_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1289_; lean_object* v___x_1291_; 
lean_inc(v_ref_1269_);
v___x_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1289_, 0, v_ref_1269_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set_tag(v___x_1276_, 1);
lean_ctor_set(v___x_1276_, 0, v___x_1289_);
v___x_1291_ = v___x_1276_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec(v___x_1272_);
lean_dec_ref(v_env_1271_);
lean_dec_ref(v_msg_1263_);
v_a_1297_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1273_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1273_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___boxed(lean_object* v_msg_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v_msg_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0(lean_object* v_00_u03b1_1312_, lean_object* v_msg_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v_msg_1313_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___boxed(lean_object* v_00_u03b1_1321_, lean_object* v_msg_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0(v_00_u03b1_1321_, v_msg_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec_ref(v___y_1323_);
return v_res_1329_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__0));
v___x_1332_ = l_Lean_stringToMessageData(v___x_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(lean_object* v_upperBound_1333_, lean_object* v_s_1334_, lean_object* v_structName_1335_, lean_object* v_idx_1336_, lean_object* v_a_1337_, lean_object* v_b_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_a_1346_; uint8_t v___x_1350_; 
v___x_1350_ = lean_nat_dec_lt(v_a_1337_, v_upperBound_1333_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; 
lean_dec(v_a_1337_);
lean_dec(v_idx_1336_);
lean_dec(v_structName_1335_);
lean_dec(v_s_1334_);
v___x_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1351_, 0, v_b_1338_);
return v___x_1351_;
}
else
{
lean_object* v_snd_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1390_; 
v_snd_1352_ = lean_ctor_get(v_b_1338_, 1);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_b_1338_);
if (v_isSharedCheck_1390_ == 0)
{
lean_object* v_unused_1391_; 
v_unused_1391_ = lean_ctor_get(v_b_1338_, 0);
lean_dec(v_unused_1391_);
v___x_1354_ = v_b_1338_;
v_isShared_1355_ = v_isSharedCheck_1390_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_snd_1352_);
lean_dec(v_b_1338_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1390_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_box(0);
if (lean_obj_tag(v_snd_1352_) == 7)
{
lean_object* v_body_1357_; uint8_t v___x_1358_; 
v_body_1357_ = lean_ctor_get(v_snd_1352_, 2);
lean_inc_ref(v_body_1357_);
lean_dec_ref_known(v_snd_1352_, 3);
v___x_1358_ = l_Lean_Expr_hasLooseBVars(v_body_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1360_; 
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 1, v_body_1357_);
lean_ctor_set(v___x_1354_, 0, v___x_1356_);
v___x_1360_ = v___x_1354_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_body_1357_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
v_a_1346_ = v___x_1360_;
goto v___jp_1345_;
}
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1362_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_1363_ = lean_expr_instantiate1(v_body_1357_, v___x_1362_);
lean_dec_ref(v_body_1357_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 1, v___x_1363_);
lean_ctor_set(v___x_1354_, 0, v___x_1356_);
v___x_1365_ = v___x_1354_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
v_a_1346_ = v___x_1365_;
goto v___jp_1345_;
}
}
}
else
{
uint8_t v___x_1367_; 
v___x_1367_ = l_Lean_Expr_isErased(v_snd_1352_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1368_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
lean_inc(v_s_1334_);
v___x_1369_ = l_Lean_mkFVar(v_s_1334_);
lean_inc(v_idx_1336_);
lean_inc(v_structName_1335_);
v___x_1370_ = l_Lean_mkProj(v_structName_1335_, v_idx_1336_, v___x_1369_);
v___x_1371_ = l_Lean_indentExpr(v___x_1370_);
v___x_1372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1368_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
v___x_1373_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_1372_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v___x_1375_; 
lean_dec_ref_known(v___x_1373_, 1);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1356_);
v___x_1375_ = v___x_1354_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_snd_1352_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
v_a_1346_ = v___x_1375_;
goto v___jp_1345_;
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_del_object(v___x_1354_);
lean_dec(v_snd_1352_);
lean_dec(v_a_1337_);
lean_dec(v_idx_1336_);
lean_dec(v_structName_1335_);
lean_dec(v_s_1334_);
v_a_1377_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1373_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1373_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
lean_dec(v_a_1337_);
lean_dec(v_idx_1336_);
lean_dec(v_structName_1335_);
lean_dec(v_s_1334_);
v___x_1385_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1385_);
v___x_1387_ = v___x_1354_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_snd_1352_);
v___x_1387_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
return v___x_1388_;
}
}
}
}
}
v___jp_1345_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = lean_unsigned_to_nat(1u);
v___x_1348_ = lean_nat_add(v_a_1337_, v___x_1347_);
lean_dec(v_a_1337_);
v_a_1337_ = v___x_1348_;
v_b_1338_ = v_a_1346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___boxed(lean_object* v_upperBound_1392_, lean_object* v_s_1393_, lean_object* v_structName_1394_, lean_object* v_idx_1395_, lean_object* v_a_1396_, lean_object* v_b_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_1392_, v_s_1393_, v_structName_1394_, v_idx_1395_, v_a_1396_, v_b_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v_upperBound_1392_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(lean_object* v_upperBound_1405_, lean_object* v_s_1406_, lean_object* v_structName_1407_, lean_object* v_idx_1408_, lean_object* v_a_1409_, lean_object* v_b_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_a_1418_; uint8_t v___x_1422_; 
v___x_1422_ = lean_nat_dec_lt(v_a_1409_, v_upperBound_1405_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; 
lean_dec(v_idx_1408_);
lean_dec(v_structName_1407_);
lean_dec(v_s_1406_);
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v_b_1410_);
return v___x_1423_;
}
else
{
lean_object* v_snd_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1462_; 
v_snd_1424_ = lean_ctor_get(v_b_1410_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_b_1410_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; 
v_unused_1463_ = lean_ctor_get(v_b_1410_, 0);
lean_dec(v_unused_1463_);
v___x_1426_ = v_b_1410_;
v_isShared_1427_ = v_isSharedCheck_1462_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_snd_1424_);
lean_dec(v_b_1410_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1462_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_box(0);
if (lean_obj_tag(v_snd_1424_) == 7)
{
lean_object* v_body_1429_; uint8_t v___x_1430_; 
v_body_1429_ = lean_ctor_get(v_snd_1424_, 2);
lean_inc_ref(v_body_1429_);
lean_dec_ref_known(v_snd_1424_, 3);
v___x_1430_ = l_Lean_Expr_hasLooseBVars(v_body_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1432_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 1, v_body_1429_);
lean_ctor_set(v___x_1426_, 0, v___x_1428_);
v___x_1432_ = v___x_1426_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_body_1429_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
v_a_1418_ = v___x_1432_;
goto v___jp_1417_;
}
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1434_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_1435_ = lean_expr_instantiate1(v_body_1429_, v___x_1434_);
lean_dec_ref(v_body_1429_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 1, v___x_1435_);
lean_ctor_set(v___x_1426_, 0, v___x_1428_);
v___x_1437_ = v___x_1426_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
v_a_1418_ = v___x_1437_;
goto v___jp_1417_;
}
}
}
else
{
uint8_t v___x_1439_; 
v___x_1439_ = l_Lean_Expr_isErased(v_snd_1424_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1440_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
lean_inc(v_s_1406_);
v___x_1441_ = l_Lean_mkFVar(v_s_1406_);
lean_inc(v_idx_1408_);
lean_inc(v_structName_1407_);
v___x_1442_ = l_Lean_mkProj(v_structName_1407_, v_idx_1408_, v___x_1441_);
v___x_1443_ = l_Lean_indentExpr(v___x_1442_);
v___x_1444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1440_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_1444_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v___x_1447_; 
lean_dec_ref_known(v___x_1445_, 1);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1428_);
v___x_1447_ = v___x_1426_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_snd_1424_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
v_a_1418_ = v___x_1447_;
goto v___jp_1417_;
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_del_object(v___x_1426_);
lean_dec(v_snd_1424_);
lean_dec(v_idx_1408_);
lean_dec(v_structName_1407_);
lean_dec(v_s_1406_);
v_a_1449_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1445_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1445_);
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
else
{
lean_object* v___x_1457_; lean_object* v___x_1459_; 
lean_dec(v_idx_1408_);
lean_dec(v_structName_1407_);
lean_dec(v_s_1406_);
v___x_1457_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1457_);
v___x_1459_ = v___x_1426_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_snd_1424_);
v___x_1459_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
return v___x_1460_;
}
}
}
}
}
v___jp_1417_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = lean_unsigned_to_nat(1u);
v___x_1420_ = lean_nat_add(v_a_1409_, v___x_1419_);
v___x_1421_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_1405_, v_s_1406_, v_structName_1407_, v_idx_1408_, v___x_1420_, v_a_1418_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1421_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg___boxed(lean_object* v_upperBound_1464_, lean_object* v_s_1465_, lean_object* v_structName_1466_, lean_object* v_idx_1467_, lean_object* v_a_1468_, lean_object* v_b_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_upperBound_1464_, v_s_1465_, v_structName_1466_, v_idx_1467_, v_a_1468_, v_b_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v_a_1468_);
lean_dec(v_upperBound_1464_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_ref_1477_, lean_object* v_msg_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_toCold_1485_; lean_object* v_currRecDepth_1486_; lean_object* v_ref_1487_; uint16_t v_optionFlags_1488_; uint8_t v_suppressElabErrors_1489_; uint8_t v_isRecordingDeps_1490_; lean_object* v_ref_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v_toCold_1485_ = lean_ctor_get(v___y_1482_, 0);
v_currRecDepth_1486_ = lean_ctor_get(v___y_1482_, 1);
v_ref_1487_ = lean_ctor_get(v___y_1482_, 2);
v_optionFlags_1488_ = lean_ctor_get_uint16(v___y_1482_, sizeof(void*)*3);
v_suppressElabErrors_1489_ = lean_ctor_get_uint8(v___y_1482_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1490_ = lean_ctor_get_uint8(v___y_1482_, sizeof(void*)*3 + 3);
v_ref_1491_ = l_Lean_replaceRef(v_ref_1477_, v_ref_1487_);
lean_inc(v_currRecDepth_1486_);
lean_inc_ref(v_toCold_1485_);
v___x_1492_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1492_, 0, v_toCold_1485_);
lean_ctor_set(v___x_1492_, 1, v_currRecDepth_1486_);
lean_ctor_set(v___x_1492_, 2, v_ref_1491_);
lean_ctor_set_uint16(v___x_1492_, sizeof(void*)*3, v_optionFlags_1488_);
lean_ctor_set_uint8(v___x_1492_, sizeof(void*)*3 + 2, v_suppressElabErrors_1489_);
lean_ctor_set_uint8(v___x_1492_, sizeof(void*)*3 + 3, v_isRecordingDeps_1490_);
v___x_1493_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v_msg_1478_, v___y_1480_, v___y_1481_, v___x_1492_, v___y_1483_);
lean_dec_ref_known(v___x_1492_, 3);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_ref_1494_, lean_object* v_msg_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_1494_, v_msg_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v_ref_1494_);
return v_res_1502_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1503_ = lean_box(1);
v___x_1504_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3);
v___x_1505_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0);
v___x_1506_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
lean_ctor_set(v___x_1506_, 1, v___x_1504_);
lean_ctor_set(v___x_1506_, 2, v___x_1503_);
return v___x_1506_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__1));
v___x_1509_ = l_Lean_stringToMessageData(v___x_1508_);
return v___x_1509_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__3));
v___x_1512_ = l_Lean_stringToMessageData(v___x_1511_);
return v___x_1512_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__5));
v___x_1515_ = l_Lean_stringToMessageData(v___x_1514_);
return v___x_1515_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__7));
v___x_1518_ = l_Lean_stringToMessageData(v___x_1517_);
return v___x_1518_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__9));
v___x_1521_ = l_Lean_stringToMessageData(v___x_1520_);
return v___x_1521_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__11));
v___x_1524_ = l_Lean_stringToMessageData(v___x_1523_);
return v___x_1524_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__13));
v___x_1527_ = l_Lean_stringToMessageData(v___x_1526_);
return v___x_1527_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__16(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__15));
v___x_1530_ = l_Lean_stringToMessageData(v___x_1529_);
return v___x_1530_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__18(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__17));
v___x_1533_ = l_Lean_stringToMessageData(v___x_1532_);
return v___x_1533_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__20(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__19));
v___x_1536_ = l_Lean_stringToMessageData(v___x_1535_);
return v___x_1536_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__22(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__21));
v___x_1539_ = l_Lean_stringToMessageData(v___x_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(lean_object* v_msg_1540_, lean_object* v_declHint_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v_env_1546_; uint8_t v___x_1547_; 
v___x_1544_ = lean_box(0);
v___x_1545_ = lean_st_ref_get(v___y_1542_);
v_env_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc_ref(v_env_1546_);
lean_dec(v___x_1545_);
v___x_1547_ = l_Lean_Name_isAnonymous(v_declHint_1541_);
if (v___x_1547_ == 0)
{
uint8_t v_isExporting_1548_; 
v_isExporting_1548_ = lean_ctor_get_uint8(v_env_1546_, sizeof(void*)*13);
if (v_isExporting_1548_ == 0)
{
lean_object* v___x_1549_; 
lean_dec_ref(v_env_1546_);
lean_dec(v_declHint_1541_);
v___x_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1549_, 0, v_msg_1540_);
return v___x_1549_;
}
else
{
lean_object* v___x_1550_; uint8_t v___x_1551_; 
lean_inc_ref(v_env_1546_);
v___x_1550_ = l_Lean_Environment_setExporting(v_env_1546_, v___x_1547_);
lean_inc(v_declHint_1541_);
lean_inc_ref(v___x_1550_);
v___x_1551_ = l_Lean_Environment_contains(v___x_1550_, v_declHint_1541_, v_isExporting_1548_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; 
lean_dec_ref(v___x_1550_);
lean_dec_ref(v_env_1546_);
lean_dec(v_declHint_1541_);
v___x_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1552_, 0, v_msg_1540_);
return v___x_1552_;
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v_c_1558_; lean_object* v___x_1559_; 
v___x_1553_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1);
v___x_1554_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0);
v___x_1555_ = l_Lean_Options_empty;
v___x_1556_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1550_);
lean_ctor_set(v___x_1556_, 1, v___x_1553_);
lean_ctor_set(v___x_1556_, 2, v___x_1554_);
lean_ctor_set(v___x_1556_, 3, v___x_1555_);
lean_inc(v_declHint_1541_);
v___x_1557_ = l_Lean_MessageData_ofConstName(v_declHint_1541_, v___x_1547_);
v_c_1558_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1558_, 0, v___x_1556_);
lean_ctor_set(v_c_1558_, 1, v___x_1557_);
v___x_1559_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1546_, v_declHint_1541_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_dec_ref(v_env_1546_);
lean_dec(v_declHint_1541_);
v___x_1560_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
lean_ctor_set(v___x_1561_, 1, v_c_1558_);
v___x_1562_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4);
v___x_1563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = l_Lean_MessageData_note(v___x_1563_);
v___x_1565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1565_, 0, v_msg_1540_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
return v___x_1566_;
}
else
{
lean_object* v_val_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1623_; 
v_val_1567_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1569_ = v___x_1559_;
v_isShared_1570_ = v_isSharedCheck_1623_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_val_1567_);
lean_dec(v___x_1559_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1623_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v_modules_1572_; lean_object* v_moduleNames_1573_; lean_object* v_mod_1574_; uint8_t v___y_1576_; uint8_t v___x_1606_; 
v___x_1571_ = l_Lean_Environment_header(v_env_1546_);
lean_dec_ref(v_env_1546_);
v_modules_1572_ = lean_ctor_get(v___x_1571_, 3);
lean_inc_ref(v_modules_1572_);
v_moduleNames_1573_ = lean_ctor_get(v___x_1571_, 4);
lean_inc_ref(v_moduleNames_1573_);
lean_dec_ref(v___x_1571_);
v_mod_1574_ = lean_array_get(v___x_1544_, v_moduleNames_1573_, v_val_1567_);
lean_dec_ref(v_moduleNames_1573_);
v___x_1606_ = l_Lean_isPrivateName(v_declHint_1541_);
lean_dec(v_declHint_1541_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; uint8_t v___x_1608_; 
v___x_1607_ = lean_array_get_size(v_modules_1572_);
v___x_1608_ = lean_nat_dec_lt(v_val_1567_, v___x_1607_);
if (v___x_1608_ == 0)
{
lean_dec_ref(v_modules_1572_);
lean_dec(v_val_1567_);
v___y_1576_ = v___x_1606_;
goto v___jp_1575_;
}
else
{
lean_object* v___x_1609_; lean_object* v_toImport_1610_; uint8_t v_isExported_1611_; 
v___x_1609_ = lean_array_fget(v_modules_1572_, v_val_1567_);
lean_dec(v_val_1567_);
lean_dec_ref(v_modules_1572_);
v_toImport_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc_ref(v_toImport_1610_);
lean_dec(v___x_1609_);
v_isExported_1611_ = lean_ctor_get_uint8(v_toImport_1610_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1610_);
v___y_1576_ = v_isExported_1611_;
goto v___jp_1575_;
}
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec_ref(v_modules_1572_);
lean_del_object(v___x_1569_);
lean_dec(v_val_1567_);
v___x_1612_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2);
v___x_1613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
lean_ctor_set(v___x_1613_, 1, v_c_1558_);
v___x_1614_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__20);
v___x_1615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = l_Lean_MessageData_ofName(v_mod_1574_);
v___x_1617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1615_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
v___x_1618_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__22);
v___x_1619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1617_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = l_Lean_MessageData_note(v___x_1619_);
v___x_1621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1621_, 0, v_msg_1540_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
v___jp_1575_:
{
if (v___y_1576_ == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1577_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6);
v___x_1578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
lean_ctor_set(v___x_1578_, 1, v_c_1558_);
v___x_1579_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8);
v___x_1580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = l_Lean_MessageData_ofName(v_mod_1574_);
v___x_1582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1580_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10);
v___x_1584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = l_Lean_MessageData_note(v___x_1584_);
v___x_1586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1586_, 0, v_msg_1540_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set_tag(v___x_1569_, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1586_);
v___x_1588_ = v___x_1569_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1590_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12);
v___x_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
lean_ctor_set(v___x_1591_, 1, v_c_1558_);
v___x_1592_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14);
v___x_1593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = l_Lean_MessageData_ofName(v_mod_1574_);
lean_inc_ref(v___x_1594_);
v___x_1595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1593_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__16);
v___x_1597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
lean_ctor_set(v___x_1598_, 1, v___x_1594_);
v___x_1599_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__18);
v___x_1600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1598_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
v___x_1601_ = l_Lean_MessageData_note(v___x_1600_);
v___x_1602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1602_, 0, v_msg_1540_);
lean_ctor_set(v___x_1602_, 1, v___x_1601_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set_tag(v___x_1569_, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1602_);
v___x_1604_ = v___x_1569_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1602_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
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
lean_object* v___x_1624_; 
lean_dec_ref(v_env_1546_);
lean_dec(v_declHint_1541_);
v___x_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1624_, 0, v_msg_1540_);
return v___x_1624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_msg_1625_, lean_object* v_declHint_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_1625_, v_declHint_1626_, v___y_1627_);
lean_dec(v___y_1627_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(lean_object* v_msg_1630_, lean_object* v_declHint_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1648_; 
v___x_1638_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_1630_, v_declHint_1631_, v___y_1636_);
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1648_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1648_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1643_ = l_Lean_unknownIdentifierMessageTag;
v___x_1644_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
lean_ctor_set(v___x_1644_, 1, v_a_1639_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1644_);
v___x_1646_ = v___x_1641_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_msg_1649_, lean_object* v_declHint_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(v_msg_1649_, v_declHint_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec_ref(v___y_1651_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1658_, lean_object* v_msg_1659_, lean_object* v_declHint_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; lean_object* v_a_1668_; lean_object* v___x_1669_; 
v___x_1667_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(v_msg_1659_, v_declHint_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref(v___x_1667_);
v___x_1669_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_1658_, v_a_1668_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1670_, lean_object* v_msg_1671_, lean_object* v_declHint_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1670_, v_msg_1671_, v_declHint_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v_ref_1670_);
return v_res_1679_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__0));
v___x_1682_ = l_Lean_stringToMessageData(v___x_1681_);
return v___x_1682_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__2));
v___x_1685_ = l_Lean_stringToMessageData(v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(lean_object* v_ref_1686_, lean_object* v_constName_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v___x_1694_; uint8_t v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1694_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_1695_ = 0;
lean_inc(v_constName_1687_);
v___x_1696_ = l_Lean_MessageData_ofConstName(v_constName_1687_, v___x_1695_);
v___x_1697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1694_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3);
v___x_1699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1686_, v___x_1699_, v_constName_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1701_, lean_object* v_constName_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1701_, v_constName_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v_ref_1701_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(lean_object* v_constName_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_ref_1717_; lean_object* v___x_1718_; 
v_ref_1717_ = lean_ctor_get(v___y_1714_, 2);
v___x_1718_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1717_, v_constName_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_constName_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec_ref(v___y_1720_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(lean_object* v_constName_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; lean_object* v_env_1735_; uint8_t v___x_1736_; lean_object* v___x_1737_; 
v___x_1734_ = lean_st_ref_get(v___y_1732_);
v_env_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc_ref(v_env_1735_);
lean_dec(v___x_1734_);
v___x_1736_ = 0;
lean_inc(v_constName_1727_);
v___x_1737_ = l_Lean_Environment_find_x3f(v_env_1735_, v_constName_1727_, v___x_1736_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
return v___x_1738_;
}
else
{
lean_object* v_val_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec(v_constName_1727_);
v_val_1739_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1737_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_val_1739_);
lean_dec(v___x_1737_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set_tag(v___x_1741_, 0);
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_val_1739_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1___boxed(lean_object* v_constName_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(v_constName_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec_ref(v___y_1748_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(lean_object* v_structName_1755_, lean_object* v_idx_1756_, lean_object* v_s_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___x_1776_; 
lean_inc(v_s_1757_);
v___x_1776_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_s_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1872_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1779_ = v___x_1776_;
v_isShared_1780_ = v_isSharedCheck_1872_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1872_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1781_; uint8_t v___x_1782_; 
v___x_1781_ = l_Lean_Expr_headBeta(v_a_1777_);
v___x_1782_ = l_Lean_Expr_isErased(v___x_1781_);
if (v___x_1782_ == 0)
{
uint8_t v___x_1783_; 
v___x_1783_ = l_Lean_Expr_isAny(v___x_1781_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; 
lean_del_object(v___x_1779_);
v___x_1784_ = l_Lean_Expr_getAppFn(v___x_1781_);
if (lean_obj_tag(v___x_1784_) == 4)
{
lean_object* v_declName_1785_; lean_object* v_us_1786_; lean_object* v___x_1787_; lean_object* v_env_1788_; lean_object* v___x_1789_; 
v_declName_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_declName_1785_);
v_us_1786_ = lean_ctor_get(v___x_1784_, 1);
lean_inc(v_us_1786_);
lean_dec_ref_known(v___x_1784_, 2);
v___x_1787_ = lean_st_ref_get(v_a_1762_);
v_env_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc_ref(v_env_1788_);
lean_dec(v___x_1787_);
v___x_1789_ = l_Lean_Environment_find_x3f(v_env_1788_, v_declName_1785_, v___x_1783_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_dec(v_us_1786_);
lean_dec_ref(v___x_1781_);
v___y_1765_ = v_a_1758_;
v___y_1766_ = v_a_1759_;
v___y_1767_ = v_a_1760_;
v___y_1768_ = v_a_1761_;
v___y_1769_ = v_a_1762_;
goto v___jp_1764_;
}
else
{
lean_object* v_val_1790_; 
v_val_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_val_1790_);
lean_dec_ref_known(v___x_1789_, 1);
if (lean_obj_tag(v_val_1790_) == 5)
{
lean_object* v_val_1791_; lean_object* v_ctors_1792_; 
v_val_1791_ = lean_ctor_get(v_val_1790_, 0);
lean_inc_ref(v_val_1791_);
lean_dec_ref_known(v_val_1790_, 1);
v_ctors_1792_ = lean_ctor_get(v_val_1791_, 4);
lean_inc(v_ctors_1792_);
if (lean_obj_tag(v_ctors_1792_) == 1)
{
lean_object* v_tail_1793_; 
v_tail_1793_ = lean_ctor_get(v_ctors_1792_, 1);
if (lean_obj_tag(v_tail_1793_) == 0)
{
lean_object* v_numParams_1794_; lean_object* v_numIndices_1795_; lean_object* v_head_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1862_; 
v_numParams_1794_ = lean_ctor_get(v_val_1791_, 1);
lean_inc(v_numParams_1794_);
v_numIndices_1795_ = lean_ctor_get(v_val_1791_, 2);
lean_inc(v_numIndices_1795_);
lean_dec_ref(v_val_1791_);
v_head_1796_ = lean_ctor_get(v_ctors_1792_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_ctors_1792_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; 
v_unused_1863_ = lean_ctor_get(v_ctors_1792_, 1);
lean_dec(v_unused_1863_);
v___x_1798_ = v_ctors_1792_;
v_isShared_1799_ = v_isSharedCheck_1862_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_head_1796_);
lean_dec(v_ctors_1792_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1862_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(v_head_1796_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1801_);
lean_dec_ref_known(v___x_1800_, 1);
if (lean_obj_tag(v_a_1801_) == 6)
{
lean_object* v_val_1802_; lean_object* v_dummy_1803_; lean_object* v_nargs_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v_val_1802_ = lean_ctor_get(v_a_1801_, 0);
lean_inc_ref(v_val_1802_);
lean_dec_ref_known(v_a_1801_, 1);
v_dummy_1803_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0);
v_nargs_1804_ = l_Lean_Expr_getAppNumArgs(v___x_1781_);
lean_inc(v_nargs_1804_);
v___x_1805_ = lean_mk_array(v_nargs_1804_, v_dummy_1803_);
v___x_1806_ = lean_unsigned_to_nat(1u);
v___x_1807_ = lean_nat_sub(v_nargs_1804_, v___x_1806_);
lean_dec(v_nargs_1804_);
v___x_1808_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1781_, v___x_1805_, v___x_1807_);
v___x_1809_ = lean_nat_add(v_numParams_1794_, v_numIndices_1795_);
lean_dec(v_numIndices_1795_);
v___x_1810_ = lean_array_get_size(v___x_1808_);
v___x_1811_ = lean_nat_dec_eq(v___x_1809_, v___x_1810_);
lean_dec(v___x_1809_);
if (v___x_1811_ == 0)
{
lean_dec_ref(v___x_1808_);
lean_dec_ref(v_val_1802_);
lean_del_object(v___x_1798_);
lean_dec(v_numParams_1794_);
lean_dec(v_us_1786_);
v___y_1765_ = v_a_1758_;
v___y_1766_ = v_a_1759_;
v___y_1767_ = v_a_1760_;
v___y_1768_ = v_a_1761_;
v___y_1769_ = v_a_1762_;
goto v___jp_1764_;
}
else
{
if (v___x_1783_ == 0)
{
lean_object* v_toConstantVal_1812_; lean_object* v_name_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v_toConstantVal_1812_ = lean_ctor_get(v_val_1802_, 0);
lean_inc_ref(v_toConstantVal_1812_);
lean_dec_ref(v_val_1802_);
v_name_1813_ = lean_ctor_get(v_toConstantVal_1812_, 0);
lean_inc(v_name_1813_);
lean_dec_ref(v_toConstantVal_1812_);
v___x_1814_ = l_Lean_mkConst(v_name_1813_, v_us_1786_);
v___x_1815_ = lean_unsigned_to_nat(0u);
v___x_1816_ = l_Array_toSubarray___redArg(v___x_1808_, v___x_1815_, v_numParams_1794_);
v___x_1817_ = l_Subarray_copy___redArg(v___x_1816_);
v___x_1818_ = l_Lean_mkAppN(v___x_1814_, v___x_1817_);
lean_dec_ref(v___x_1817_);
v___x_1819_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(v___x_1818_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1821_; lean_object* v___x_1823_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref_known(v___x_1819_, 1);
v___x_1821_ = lean_box(0);
if (v_isShared_1799_ == 0)
{
lean_ctor_set_tag(v___x_1798_, 0);
lean_ctor_set(v___x_1798_, 1, v_a_1820_);
lean_ctor_set(v___x_1798_, 0, v___x_1821_);
v___x_1823_ = v___x_1798_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1821_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_a_1820_);
v___x_1823_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1824_; 
lean_inc(v_structName_1755_);
lean_inc(v_s_1757_);
lean_inc(v_idx_1756_);
v___x_1824_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_idx_1756_, v_s_1757_, v_structName_1755_, v_idx_1756_, v___x_1815_, v___x_1823_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1844_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1844_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1844_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_fst_1829_; 
v_fst_1829_ = lean_ctor_get(v_a_1825_, 0);
if (lean_obj_tag(v_fst_1829_) == 0)
{
lean_object* v_snd_1830_; 
v_snd_1830_ = lean_ctor_get(v_a_1825_, 1);
lean_inc(v_snd_1830_);
lean_dec(v_a_1825_);
if (lean_obj_tag(v_snd_1830_) == 7)
{
lean_object* v_binderType_1831_; lean_object* v___x_1833_; 
lean_dec(v_s_1757_);
lean_dec(v_idx_1756_);
lean_dec(v_structName_1755_);
v_binderType_1831_ = lean_ctor_get(v_snd_1830_, 1);
lean_inc_ref(v_binderType_1831_);
lean_dec_ref_known(v_snd_1830_, 3);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v_binderType_1831_);
v___x_1833_ = v___x_1827_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_binderType_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
else
{
uint8_t v___x_1835_; 
v___x_1835_ = l_Lean_Expr_isErased(v_snd_1830_);
lean_dec(v_snd_1830_);
if (v___x_1835_ == 0)
{
lean_del_object(v___x_1827_);
v___y_1765_ = v_a_1758_;
v___y_1766_ = v_a_1759_;
v___y_1767_ = v_a_1760_;
v___y_1768_ = v_a_1761_;
v___y_1769_ = v_a_1762_;
goto v___jp_1764_;
}
else
{
lean_object* v___x_1836_; lean_object* v___x_1838_; 
lean_dec(v_s_1757_);
lean_dec(v_idx_1756_);
lean_dec(v_structName_1755_);
v___x_1836_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1836_);
v___x_1838_ = v___x_1827_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
else
{
lean_object* v_val_1840_; lean_object* v___x_1842_; 
lean_inc_ref(v_fst_1829_);
lean_dec(v_a_1825_);
lean_dec(v_s_1757_);
lean_dec(v_idx_1756_);
lean_dec(v_structName_1755_);
v_val_1840_ = lean_ctor_get(v_fst_1829_, 0);
lean_inc(v_val_1840_);
lean_dec_ref_known(v_fst_1829_, 1);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v_val_1840_);
v___x_1842_ = v___x_1827_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_val_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec(v_s_1757_);
lean_dec(v_idx_1756_);
lean_dec(v_structName_1755_);
v_a_1845_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1824_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1824_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
}
else
{
lean_del_object(v___x_1798_);
lean_dec(v_s_1757_);
lean_dec(v_idx_1756_);
lean_dec(v_structName_1755_);
return v___x_1819_;
}
}
else
{
lean_dec_ref(v___x_1808_);
lean_dec_ref(v_val_1802_);
lean_del_object(v___x_1798_);
lean_dec(v_numParams_1794_);
lean_dec(v_us_1786_);
v___y_1765_ = v_a_1758_;
v___y_1766_ = v_a_1759_;
v___y_1767_ = v_a_1760_;
v___y_1768_ = v_a_1761_;
v___y_1769_ = v_a_1762_;
goto v___jp_1764_;
}
}
}
else
{
lean_dec(v_a_1801_);
lean_del_object(v___x_1798_);
lean_dec(v_numIndices_1795_);
lean_dec(v_numParams_1794_);
lean_dec(v_us_1786_);
lean_dec_ref(v___x_1781_);
v___y_1765_ = v_a_1758_;
v___y_1766_ = v_a_1759_;
v___y_1767_ = v_a_1760_;
v___y_1768_ = v_a_1761_;
v___y_1769_ = v_a_1762_;
goto v___jp_1764_;
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_del_object(v___x_1798_);
lean_dec(v_numIndices_1795_);
lean_dec(v_numParams_1794_);
lean_dec(v_us_1786_);
lean_dec_ref(v___x_1781_);
lean_dec(v_s_1757_);
lean_dec(v_idx_1756_);
lean_dec(v_structName_1755_);
v_a_1854_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1800_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1800_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1792_, 2);
lean_dec_ref(v_val_1791_);
lean_dec(v_us_1786_);
lean_dec_ref(v___x_1781_);
v___y_1765_ = v_a_1758_;
v___y_1766_ = v_a_1759_;
v___y_1767_ = v_a_1760_;
v___y_1768_ = v_a_1761_;
v___y_1769_ = v_a_1762_;
goto v___jp_1764_;
}
}
else
{
lean_dec(v_ctors_1792_);
lean_dec_ref(v_val_1791_);
lean_dec(v_us_1786_);
lean_dec_ref(v___x_1781_);
v___y_1765_ = v_a_1758_;
v___y_1766_ = v_a_1759_;
v___y_1767_ = v_a_1760_;
v___y_1768_ = v_a_1761_;
v___y_1769_ = v_a_1762_;
goto v___jp_1764_;
}
}
else
{
lean_dec(v_val_1790_);
lean_dec(v_us_1786_);
lean_dec_ref(v___x_1781_);
v___y_1765_ = v_a_1758_;
v___y_1766_ = v_a_1759_;
v___y_1767_ = v_a_1760_;
v___y_1768_ = v_a_1761_;
v___y_1769_ = v_a_1762_;
goto v___jp_1764_;
}
}
}
else
{
lean_dec_ref(v___x_1784_);
lean_dec_ref(v___x_1781_);
v___y_1765_ = v_a_1758_;
v___y_1766_ = v_a_1759_;
v___y_1767_ = v_a_1760_;
v___y_1768_ = v_a_1761_;
v___y_1769_ = v_a_1762_;
goto v___jp_1764_;
}
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1866_; 
lean_dec_ref(v___x_1781_);
lean_dec(v_s_1757_);
lean_dec(v_idx_1756_);
lean_dec(v_structName_1755_);
v___x_1864_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1864_);
v___x_1866_ = v___x_1779_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
else
{
lean_object* v___x_1868_; lean_object* v___x_1870_; 
lean_dec_ref(v___x_1781_);
lean_dec(v_s_1757_);
lean_dec(v_idx_1756_);
lean_dec(v_structName_1755_);
v___x_1868_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1868_);
v___x_1870_ = v___x_1779_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
else
{
lean_dec(v_s_1757_);
lean_dec(v_idx_1756_);
lean_dec(v_structName_1755_);
return v___x_1776_;
}
v___jp_1764_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1770_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
v___x_1771_ = l_Lean_mkFVar(v_s_1757_);
v___x_1772_ = l_Lean_mkProj(v_structName_1755_, v_idx_1756_, v___x_1771_);
v___x_1773_ = l_Lean_indentExpr(v___x_1772_);
v___x_1774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1770_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_1774_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
return v___x_1775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferProjType___boxed(lean_object* v_structName_1873_, lean_object* v_idx_1874_, lean_object* v_s_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(v_structName_1873_, v_idx_1874_, v_s_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
lean_dec(v_a_1878_);
lean_dec_ref(v_a_1877_);
lean_dec_ref(v_a_1876_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2(lean_object* v_upperBound_1883_, lean_object* v_s_1884_, lean_object* v_structName_1885_, lean_object* v_idx_1886_, lean_object* v_inst_1887_, lean_object* v_R_1888_, lean_object* v_a_1889_, lean_object* v_b_1890_, lean_object* v_c_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_upperBound_1883_, v_s_1884_, v_structName_1885_, v_idx_1886_, v_a_1889_, v_b_1890_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___boxed(lean_object* v_upperBound_1899_, lean_object* v_s_1900_, lean_object* v_structName_1901_, lean_object* v_idx_1902_, lean_object* v_inst_1903_, lean_object* v_R_1904_, lean_object* v_a_1905_, lean_object* v_b_1906_, lean_object* v_c_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2(v_upperBound_1899_, v_s_1900_, v_structName_1901_, v_idx_1902_, v_inst_1903_, v_R_1904_, v_a_1905_, v_b_1906_, v_c_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v_a_1905_);
lean_dec(v_upperBound_1899_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1(lean_object* v_00_u03b1_1915_, lean_object* v_constName_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___boxed(lean_object* v_00_u03b1_1924_, lean_object* v_constName_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1(v_00_u03b1_1924_, v_constName_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec_ref(v___y_1926_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3(lean_object* v_upperBound_1933_, lean_object* v_s_1934_, lean_object* v_structName_1935_, lean_object* v_idx_1936_, lean_object* v_inst_1937_, lean_object* v_R_1938_, lean_object* v_a_1939_, lean_object* v_b_1940_, lean_object* v_c_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_1933_, v_s_1934_, v_structName_1935_, v_idx_1936_, v_a_1939_, v_b_1940_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___boxed(lean_object* v_upperBound_1949_, lean_object* v_s_1950_, lean_object* v_structName_1951_, lean_object* v_idx_1952_, lean_object* v_inst_1953_, lean_object* v_R_1954_, lean_object* v_a_1955_, lean_object* v_b_1956_, lean_object* v_c_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3(v_upperBound_1949_, v_s_1950_, v_structName_1951_, v_idx_1952_, v_inst_1953_, v_R_1954_, v_a_1955_, v_b_1956_, v_c_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v_upperBound_1949_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_1965_, lean_object* v_ref_1966_, lean_object* v_constName_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1966_, v_constName_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1975_, lean_object* v_ref_1976_, lean_object* v_constName_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2(v_00_u03b1_1975_, v_ref_1976_, v_constName_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v_ref_1976_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1985_, lean_object* v_ref_1986_, lean_object* v_msg_1987_, lean_object* v_declHint_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1986_, v_msg_1987_, v_declHint_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1996_, lean_object* v_ref_1997_, lean_object* v_msg_1998_, lean_object* v_declHint_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4(v_00_u03b1_1996_, v_ref_1997_, v_msg_1998_, v_declHint_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v_ref_1997_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msg_2007_, lean_object* v_declHint_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_2007_, v_declHint_2008_, v___y_2013_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_2016_, lean_object* v_declHint_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_2016_, v_declHint_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec_ref(v___y_2018_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b1_2025_, lean_object* v_ref_2026_, lean_object* v_msg_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_2026_, v_msg_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b1_2035_, lean_object* v_ref_2036_, lean_object* v_msg_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7(v_00_u03b1_2035_, v_ref_2036_, v_msg_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v_ref_2036_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(lean_object* v_e_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
switch(lean_obj_tag(v_e_2045_))
{
case 0:
{
lean_object* v_value_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2060_; 
v_value_2052_ = lean_ctor_get(v_e_2045_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v_e_2045_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2054_ = v_e_2045_;
v_isShared_2055_ = v_isSharedCheck_2060_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_value_2052_);
lean_dec(v_e_2045_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2060_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2056_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType(v_value_2052_);
lean_dec_ref(v_value_2052_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2056_);
v___x_2058_ = v___x_2054_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
case 1:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
return v___x_2062_;
}
case 2:
{
lean_object* v_typeName_2063_; lean_object* v_idx_2064_; lean_object* v_struct_2065_; lean_object* v___x_2066_; 
v_typeName_2063_ = lean_ctor_get(v_e_2045_, 0);
lean_inc(v_typeName_2063_);
v_idx_2064_ = lean_ctor_get(v_e_2045_, 1);
lean_inc(v_idx_2064_);
v_struct_2065_ = lean_ctor_get(v_e_2045_, 2);
lean_inc(v_struct_2065_);
lean_dec_ref_known(v_e_2045_, 3);
v___x_2066_ = l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(v_typeName_2063_, v_idx_2064_, v_struct_2065_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_);
return v___x_2066_;
}
case 3:
{
lean_object* v_declName_2067_; lean_object* v_us_2068_; lean_object* v_args_2069_; lean_object* v___x_2070_; 
v_declName_2067_ = lean_ctor_get(v_e_2045_, 0);
lean_inc(v_declName_2067_);
v_us_2068_ = lean_ctor_get(v_e_2045_, 1);
lean_inc(v_us_2068_);
v_args_2069_ = lean_ctor_get(v_e_2045_, 2);
lean_inc_ref(v_args_2069_);
lean_dec_ref_known(v_e_2045_, 3);
v___x_2070_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(v_declName_2067_, v_us_2068_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2072_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref_known(v___x_2070_, 1);
v___x_2072_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2071_, v_args_2069_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_);
return v___x_2072_;
}
else
{
lean_dec_ref(v_args_2069_);
return v___x_2070_;
}
}
default: 
{
lean_object* v_fvarId_2073_; lean_object* v_args_2074_; lean_object* v___x_2075_; 
v_fvarId_2073_ = lean_ctor_get(v_e_2045_, 0);
lean_inc(v_fvarId_2073_);
v_args_2074_ = lean_ctor_get(v_e_2045_, 1);
lean_inc_ref(v_args_2074_);
lean_dec_ref_known(v_e_2045_, 2);
v___x_2075_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_fvarId_2073_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2077_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2075_, 1);
v___x_2077_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2076_, v_args_2074_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_);
return v___x_2077_;
}
else
{
lean_dec_ref(v_args_2074_);
return v___x_2075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType___boxed(lean_object* v_e_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(v_e_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec_ref(v_a_2079_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType(lean_object* v_e_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2092_ = lean_unsigned_to_nat(32u);
v___x_2093_ = lean_mk_empty_array_with_capacity(v___x_2092_);
lean_dec_ref(v___x_2093_);
v___x_2094_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2095_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_e_2086_, v___x_2094_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType___boxed(lean_object* v_e_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_Compiler_LCNF_inferType(v_e_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(lean_object* v_msg_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v___x_2109_; lean_object* v_toApplicative_2110_; lean_object* v_toFunctor_2111_; lean_object* v_toSeq_2112_; lean_object* v_toSeqLeft_2113_; lean_object* v_toSeqRight_2114_; lean_object* v___f_2115_; lean_object* v___f_2116_; lean_object* v___f_2117_; lean_object* v___f_2118_; lean_object* v___x_2119_; lean_object* v___f_2120_; lean_object* v___f_2121_; lean_object* v___f_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___f_2128_; lean_object* v___x_148__overap_2129_; lean_object* v___x_2130_; 
v___x_2109_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_2110_ = lean_ctor_get(v___x_2109_, 0);
v_toFunctor_2111_ = lean_ctor_get(v_toApplicative_2110_, 0);
v_toSeq_2112_ = lean_ctor_get(v_toApplicative_2110_, 2);
v_toSeqLeft_2113_ = lean_ctor_get(v_toApplicative_2110_, 3);
v_toSeqRight_2114_ = lean_ctor_get(v_toApplicative_2110_, 4);
v___f_2115_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_2116_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2111_, 2);
v___f_2117_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2117_, 0, v_toFunctor_2111_);
v___f_2118_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2118_, 0, v_toFunctor_2111_);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___f_2117_);
lean_ctor_set(v___x_2119_, 1, v___f_2118_);
lean_inc(v_toSeqRight_2114_);
v___f_2120_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2120_, 0, v_toSeqRight_2114_);
lean_inc(v_toSeqLeft_2113_);
v___f_2121_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2121_, 0, v_toSeqLeft_2113_);
lean_inc(v_toSeq_2112_);
v___f_2122_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2122_, 0, v_toSeq_2112_);
v___x_2123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2119_);
lean_ctor_set(v___x_2123_, 1, v___f_2115_);
lean_ctor_set(v___x_2123_, 2, v___f_2122_);
lean_ctor_set(v___x_2123_, 3, v___f_2121_);
lean_ctor_set(v___x_2123_, 4, v___f_2120_);
v___x_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
lean_ctor_set(v___x_2124_, 1, v___f_2116_);
v___x_2125_ = l_StateRefT_x27_instMonad___redArg(v___x_2124_);
v___x_2126_ = l_Lean_instInhabitedExpr;
v___x_2127_ = l_instInhabitedOfMonad___redArg(v___x_2125_, v___x_2126_);
v___f_2128_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2128_, 0, v___x_2127_);
v___x_148__overap_2129_ = lean_panic_fn_borrowed(v___f_2128_, v_msg_2103_);
lean_dec_ref(v___f_2128_);
lean_inc(v___y_2107_);
lean_inc_ref(v___y_2106_);
lean_inc(v___y_2105_);
lean_inc_ref(v___y_2104_);
v___x_2130_ = lean_apply_5(v___x_148__overap_2129_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, lean_box(0));
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0___boxed(lean_object* v_msg_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v_msg_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
return v_res_2137_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inferAppType___closed__2(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2140_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2141_ = lean_unsigned_to_nat(15u);
v___x_2142_ = lean_unsigned_to_nat(258u);
v___x_2143_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__0));
v___x_2144_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2145_ = l_mkPanicMessageWithDecl(v___x_2144_, v___x_2143_, v___x_2142_, v___x_2141_, v___x_2140_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType(uint8_t v_pu_2146_, lean_object* v_fnType_2147_, lean_object* v_args_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
if (v_pu_2146_ == 0)
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2155_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_fnType_2147_, v_args_2148_, v___x_2154_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
return v___x_2155_;
}
else
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
lean_dec_ref(v_args_2148_);
lean_dec_ref(v_fnType_2147_);
v___x_2156_ = lean_obj_once(&l_Lean_Compiler_LCNF_inferAppType___closed__2, &l_Lean_Compiler_LCNF_inferAppType___closed__2_once, _init_l_Lean_Compiler_LCNF_inferAppType___closed__2);
v___x_2157_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2156_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
return v___x_2157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType___boxed(lean_object* v_pu_2158_, lean_object* v_fnType_2159_, lean_object* v_args_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
uint8_t v_pu_boxed_2166_; lean_object* v_res_2167_; 
v_pu_boxed_2166_ = lean_unbox(v_pu_2158_);
v_res_2167_ = l_Lean_Compiler_LCNF_inferAppType(v_pu_boxed_2166_, v_fnType_2159_, v_args_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
return v_res_2167_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Arg_inferType___closed__1(void){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2169_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2170_ = lean_unsigned_to_nat(15u);
v___x_2171_ = lean_unsigned_to_nat(263u);
v___x_2172_ = ((lean_object*)(l_Lean_Compiler_LCNF_Arg_inferType___closed__0));
v___x_2173_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2174_ = l_mkPanicMessageWithDecl(v___x_2173_, v___x_2172_, v___x_2171_, v___x_2170_, v___x_2169_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType(uint8_t v_pu_2175_, lean_object* v_arg_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_){
_start:
{
if (v_pu_2175_ == 0)
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2183_ = l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(v_arg_2176_, v___x_2182_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
return v___x_2183_;
}
else
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
lean_dec(v_arg_2176_);
v___x_2184_ = lean_obj_once(&l_Lean_Compiler_LCNF_Arg_inferType___closed__1, &l_Lean_Compiler_LCNF_Arg_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_Arg_inferType___closed__1);
v___x_2185_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2184_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
return v___x_2185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType___boxed(lean_object* v_pu_2186_, lean_object* v_arg_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_){
_start:
{
uint8_t v_pu_boxed_2193_; lean_object* v_res_2194_; 
v_pu_boxed_2193_ = lean_unbox(v_pu_2186_);
v_res_2194_ = l_Lean_Compiler_LCNF_Arg_inferType(v_pu_boxed_2193_, v_arg_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_);
lean_dec(v_a_2191_);
lean_dec_ref(v_a_2190_);
lean_dec(v_a_2189_);
lean_dec_ref(v_a_2188_);
return v_res_2194_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LetValue_inferType___closed__1(void){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2196_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2197_ = lean_unsigned_to_nat(15u);
v___x_2198_ = lean_unsigned_to_nat(268u);
v___x_2199_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_inferType___closed__0));
v___x_2200_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2201_ = l_mkPanicMessageWithDecl(v___x_2200_, v___x_2199_, v___x_2198_, v___x_2197_, v___x_2196_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(uint8_t v_pu_2202_, lean_object* v_e_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_){
_start:
{
if (v_pu_2202_ == 0)
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2210_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(v_e_2203_, v___x_2209_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_);
return v___x_2210_;
}
else
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
lean_dec(v_e_2203_);
v___x_2211_ = lean_obj_once(&l_Lean_Compiler_LCNF_LetValue_inferType___closed__1, &l_Lean_Compiler_LCNF_LetValue_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_LetValue_inferType___closed__1);
v___x_2212_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2211_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_);
return v___x_2212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType___boxed(lean_object* v_pu_2213_, lean_object* v_e_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_){
_start:
{
uint8_t v_pu_boxed_2220_; lean_object* v_res_2221_; 
v_pu_boxed_2220_ = lean_unbox(v_pu_2213_);
v_res_2221_ = l_Lean_Compiler_LCNF_LetValue_inferType(v_pu_boxed_2220_, v_e_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
return v_res_2221_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_inferType___closed__1(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2223_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2224_ = lean_unsigned_to_nat(15u);
v___x_2225_ = lean_unsigned_to_nat(279u);
v___x_2226_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_inferType___closed__0));
v___x_2227_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2228_ = l_mkPanicMessageWithDecl(v___x_2227_, v___x_2226_, v___x_2225_, v___x_2224_, v___x_2223_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t v_pu_2229_, lean_object* v_code_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_){
_start:
{
if (v_pu_2229_ == 0)
{
switch(lean_obj_tag(v_code_2230_))
{
case 3:
{
lean_object* v_fvarId_2236_; lean_object* v_args_2237_; lean_object* v___x_2238_; 
v_fvarId_2236_ = lean_ctor_get(v_code_2230_, 0);
lean_inc(v_fvarId_2236_);
v_args_2237_ = lean_ctor_get(v_code_2230_, 1);
lean_inc_ref(v_args_2237_);
lean_dec_ref_known(v_code_2230_, 2);
v___x_2238_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2236_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2238_, 1);
v___x_2240_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2241_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2239_, v_args_2237_, v___x_2240_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
return v___x_2241_;
}
else
{
lean_dec_ref(v_args_2237_);
return v___x_2238_;
}
}
case 4:
{
lean_object* v_cases_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2250_; 
v_cases_2242_ = lean_ctor_get(v_code_2230_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v_code_2230_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2244_ = v_code_2230_;
v_isShared_2245_ = v_isSharedCheck_2250_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_cases_2242_);
lean_dec(v_code_2230_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2250_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v_resultType_2246_; lean_object* v___x_2248_; 
v_resultType_2246_ = lean_ctor_get(v_cases_2242_, 1);
lean_inc_ref(v_resultType_2246_);
lean_dec_ref(v_cases_2242_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set_tag(v___x_2244_, 0);
lean_ctor_set(v___x_2244_, 0, v_resultType_2246_);
v___x_2248_ = v___x_2244_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_resultType_2246_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
case 5:
{
lean_object* v_fvarId_2251_; lean_object* v___x_2252_; 
v_fvarId_2251_ = lean_ctor_get(v_code_2230_, 0);
lean_inc(v_fvarId_2251_);
lean_dec_ref_known(v_code_2230_, 1);
v___x_2252_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2251_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
return v___x_2252_;
}
case 6:
{
lean_object* v_type_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
v_type_2253_ = lean_ctor_get(v_code_2230_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v_code_2230_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v_code_2230_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_type_2253_);
lean_dec(v_code_2230_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
lean_ctor_set_tag(v___x_2255_, 0);
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_type_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
default: 
{
lean_object* v_k_2261_; 
v_k_2261_ = lean_ctor_get(v_code_2230_, 1);
lean_inc_ref(v_k_2261_);
lean_dec_ref(v_code_2230_);
v_code_2230_ = v_k_2261_;
goto _start;
}
}
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
lean_dec_ref(v_code_2230_);
v___x_2263_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_inferType___closed__1, &l_Lean_Compiler_LCNF_Code_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_Code_inferType___closed__1);
v___x_2264_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2263_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
return v___x_2264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType___boxed(lean_object* v_pu_2265_, lean_object* v_code_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
uint8_t v_pu_boxed_2272_; lean_object* v_res_2273_; 
v_pu_boxed_2272_ = lean_unbox(v_pu_2265_);
v_res_2273_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_boxed_2272_, v_code_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_);
lean_dec(v_a_2270_);
lean_dec_ref(v_a_2269_);
lean_dec(v_a_2268_);
lean_dec_ref(v_a_2267_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg(uint8_t v_pu_2274_, lean_object* v_code_2275_, lean_object* v_h__1_2276_, lean_object* v_h__2_2277_){
_start:
{
if (v_pu_2274_ == 0)
{
lean_object* v___x_2278_; 
lean_dec(v_h__2_2277_);
v___x_2278_ = lean_apply_1(v_h__1_2276_, v_code_2275_);
return v___x_2278_;
}
else
{
lean_object* v___x_2279_; 
lean_dec(v_h__1_2276_);
v___x_2279_ = lean_apply_1(v_h__2_2277_, v_code_2275_);
return v___x_2279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg___boxed(lean_object* v_pu_2280_, lean_object* v_code_2281_, lean_object* v_h__1_2282_, lean_object* v_h__2_2283_){
_start:
{
uint8_t v_pu_32__boxed_2284_; lean_object* v_res_2285_; 
v_pu_32__boxed_2284_ = lean_unbox(v_pu_2280_);
v_res_2285_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg(v_pu_32__boxed_2284_, v_code_2281_, v_h__1_2282_, v_h__2_2283_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter(lean_object* v_motive_2286_, uint8_t v_pu_2287_, lean_object* v_code_2288_, lean_object* v_h__1_2289_, lean_object* v_h__2_2290_){
_start:
{
if (v_pu_2287_ == 0)
{
lean_object* v___x_2291_; 
lean_dec(v_h__2_2290_);
v___x_2291_ = lean_apply_1(v_h__1_2289_, v_code_2288_);
return v___x_2291_;
}
else
{
lean_object* v___x_2292_; 
lean_dec(v_h__1_2289_);
v___x_2292_ = lean_apply_1(v_h__2_2290_, v_code_2288_);
return v___x_2292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___boxed(lean_object* v_motive_2293_, lean_object* v_pu_2294_, lean_object* v_code_2295_, lean_object* v_h__1_2296_, lean_object* v_h__2_2297_){
_start:
{
uint8_t v_pu_39__boxed_2298_; lean_object* v_res_2299_; 
v_pu_39__boxed_2298_ = lean_unbox(v_pu_2294_);
v_res_2299_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter(v_motive_2293_, v_pu_39__boxed_2298_, v_code_2295_, v_h__1_2296_, v_h__2_2297_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__1_splitter___redArg(lean_object* v_code_2300_, lean_object* v_h__1_2301_, lean_object* v_h__2_2302_, lean_object* v_h__3_2303_, lean_object* v_h__4_2304_, lean_object* v_h__5_2305_, lean_object* v_h__6_2306_, lean_object* v_h__7_2307_){
_start:
{
switch(lean_obj_tag(v_code_2300_))
{
case 0:
{
lean_object* v_decl_2308_; lean_object* v_k_2309_; lean_object* v___x_2310_; 
lean_dec(v_h__7_2307_);
lean_dec(v_h__6_2306_);
lean_dec(v_h__5_2305_);
lean_dec(v_h__4_2304_);
lean_dec(v_h__3_2303_);
lean_dec(v_h__2_2302_);
v_decl_2308_ = lean_ctor_get(v_code_2300_, 0);
lean_inc_ref(v_decl_2308_);
v_k_2309_ = lean_ctor_get(v_code_2300_, 1);
lean_inc_ref(v_k_2309_);
lean_dec_ref_known(v_code_2300_, 2);
v___x_2310_ = lean_apply_2(v_h__1_2301_, v_decl_2308_, v_k_2309_);
return v___x_2310_;
}
case 1:
{
lean_object* v_decl_2311_; lean_object* v_k_2312_; lean_object* v___x_2313_; 
lean_dec(v_h__7_2307_);
lean_dec(v_h__6_2306_);
lean_dec(v_h__5_2305_);
lean_dec(v_h__4_2304_);
lean_dec(v_h__3_2303_);
lean_dec(v_h__1_2301_);
v_decl_2311_ = lean_ctor_get(v_code_2300_, 0);
lean_inc_ref(v_decl_2311_);
v_k_2312_ = lean_ctor_get(v_code_2300_, 1);
lean_inc_ref(v_k_2312_);
lean_dec_ref_known(v_code_2300_, 2);
v___x_2313_ = lean_apply_3(v_h__2_2302_, v_decl_2311_, v_k_2312_, lean_box(0));
return v___x_2313_;
}
case 2:
{
lean_object* v_decl_2314_; lean_object* v_k_2315_; lean_object* v___x_2316_; 
lean_dec(v_h__7_2307_);
lean_dec(v_h__6_2306_);
lean_dec(v_h__5_2305_);
lean_dec(v_h__4_2304_);
lean_dec(v_h__2_2302_);
lean_dec(v_h__1_2301_);
v_decl_2314_ = lean_ctor_get(v_code_2300_, 0);
lean_inc_ref(v_decl_2314_);
v_k_2315_ = lean_ctor_get(v_code_2300_, 1);
lean_inc_ref(v_k_2315_);
lean_dec_ref_known(v_code_2300_, 2);
v___x_2316_ = lean_apply_2(v_h__3_2303_, v_decl_2314_, v_k_2315_);
return v___x_2316_;
}
case 3:
{
lean_object* v_fvarId_2317_; lean_object* v_args_2318_; lean_object* v___x_2319_; 
lean_dec(v_h__7_2307_);
lean_dec(v_h__6_2306_);
lean_dec(v_h__4_2304_);
lean_dec(v_h__3_2303_);
lean_dec(v_h__2_2302_);
lean_dec(v_h__1_2301_);
v_fvarId_2317_ = lean_ctor_get(v_code_2300_, 0);
lean_inc(v_fvarId_2317_);
v_args_2318_ = lean_ctor_get(v_code_2300_, 1);
lean_inc_ref(v_args_2318_);
lean_dec_ref_known(v_code_2300_, 2);
v___x_2319_ = lean_apply_2(v_h__5_2305_, v_fvarId_2317_, v_args_2318_);
return v___x_2319_;
}
case 4:
{
lean_object* v_cases_2320_; lean_object* v___x_2321_; 
lean_dec(v_h__6_2306_);
lean_dec(v_h__5_2305_);
lean_dec(v_h__4_2304_);
lean_dec(v_h__3_2303_);
lean_dec(v_h__2_2302_);
lean_dec(v_h__1_2301_);
v_cases_2320_ = lean_ctor_get(v_code_2300_, 0);
lean_inc_ref(v_cases_2320_);
lean_dec_ref_known(v_code_2300_, 1);
v___x_2321_ = lean_apply_1(v_h__7_2307_, v_cases_2320_);
return v___x_2321_;
}
case 5:
{
lean_object* v_fvarId_2322_; lean_object* v___x_2323_; 
lean_dec(v_h__7_2307_);
lean_dec(v_h__6_2306_);
lean_dec(v_h__5_2305_);
lean_dec(v_h__3_2303_);
lean_dec(v_h__2_2302_);
lean_dec(v_h__1_2301_);
v_fvarId_2322_ = lean_ctor_get(v_code_2300_, 0);
lean_inc(v_fvarId_2322_);
lean_dec_ref_known(v_code_2300_, 1);
v___x_2323_ = lean_apply_1(v_h__4_2304_, v_fvarId_2322_);
return v___x_2323_;
}
default: 
{
lean_object* v_type_2324_; lean_object* v___x_2325_; 
lean_dec(v_h__7_2307_);
lean_dec(v_h__5_2305_);
lean_dec(v_h__4_2304_);
lean_dec(v_h__3_2303_);
lean_dec(v_h__2_2302_);
lean_dec(v_h__1_2301_);
v_type_2324_ = lean_ctor_get(v_code_2300_, 0);
lean_inc_ref(v_type_2324_);
lean_dec_ref_known(v_code_2300_, 1);
v___x_2325_ = lean_apply_1(v_h__6_2306_, v_type_2324_);
return v___x_2325_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__1_splitter(lean_object* v_motive_2326_, lean_object* v_code_2327_, lean_object* v_h__1_2328_, lean_object* v_h__2_2329_, lean_object* v_h__3_2330_, lean_object* v_h__4_2331_, lean_object* v_h__5_2332_, lean_object* v_h__6_2333_, lean_object* v_h__7_2334_){
_start:
{
switch(lean_obj_tag(v_code_2327_))
{
case 0:
{
lean_object* v_decl_2335_; lean_object* v_k_2336_; lean_object* v___x_2337_; 
lean_dec(v_h__7_2334_);
lean_dec(v_h__6_2333_);
lean_dec(v_h__5_2332_);
lean_dec(v_h__4_2331_);
lean_dec(v_h__3_2330_);
lean_dec(v_h__2_2329_);
v_decl_2335_ = lean_ctor_get(v_code_2327_, 0);
lean_inc_ref(v_decl_2335_);
v_k_2336_ = lean_ctor_get(v_code_2327_, 1);
lean_inc_ref(v_k_2336_);
lean_dec_ref_known(v_code_2327_, 2);
v___x_2337_ = lean_apply_2(v_h__1_2328_, v_decl_2335_, v_k_2336_);
return v___x_2337_;
}
case 1:
{
lean_object* v_decl_2338_; lean_object* v_k_2339_; lean_object* v___x_2340_; 
lean_dec(v_h__7_2334_);
lean_dec(v_h__6_2333_);
lean_dec(v_h__5_2332_);
lean_dec(v_h__4_2331_);
lean_dec(v_h__3_2330_);
lean_dec(v_h__1_2328_);
v_decl_2338_ = lean_ctor_get(v_code_2327_, 0);
lean_inc_ref(v_decl_2338_);
v_k_2339_ = lean_ctor_get(v_code_2327_, 1);
lean_inc_ref(v_k_2339_);
lean_dec_ref_known(v_code_2327_, 2);
v___x_2340_ = lean_apply_3(v_h__2_2329_, v_decl_2338_, v_k_2339_, lean_box(0));
return v___x_2340_;
}
case 2:
{
lean_object* v_decl_2341_; lean_object* v_k_2342_; lean_object* v___x_2343_; 
lean_dec(v_h__7_2334_);
lean_dec(v_h__6_2333_);
lean_dec(v_h__5_2332_);
lean_dec(v_h__4_2331_);
lean_dec(v_h__2_2329_);
lean_dec(v_h__1_2328_);
v_decl_2341_ = lean_ctor_get(v_code_2327_, 0);
lean_inc_ref(v_decl_2341_);
v_k_2342_ = lean_ctor_get(v_code_2327_, 1);
lean_inc_ref(v_k_2342_);
lean_dec_ref_known(v_code_2327_, 2);
v___x_2343_ = lean_apply_2(v_h__3_2330_, v_decl_2341_, v_k_2342_);
return v___x_2343_;
}
case 3:
{
lean_object* v_fvarId_2344_; lean_object* v_args_2345_; lean_object* v___x_2346_; 
lean_dec(v_h__7_2334_);
lean_dec(v_h__6_2333_);
lean_dec(v_h__4_2331_);
lean_dec(v_h__3_2330_);
lean_dec(v_h__2_2329_);
lean_dec(v_h__1_2328_);
v_fvarId_2344_ = lean_ctor_get(v_code_2327_, 0);
lean_inc(v_fvarId_2344_);
v_args_2345_ = lean_ctor_get(v_code_2327_, 1);
lean_inc_ref(v_args_2345_);
lean_dec_ref_known(v_code_2327_, 2);
v___x_2346_ = lean_apply_2(v_h__5_2332_, v_fvarId_2344_, v_args_2345_);
return v___x_2346_;
}
case 4:
{
lean_object* v_cases_2347_; lean_object* v___x_2348_; 
lean_dec(v_h__6_2333_);
lean_dec(v_h__5_2332_);
lean_dec(v_h__4_2331_);
lean_dec(v_h__3_2330_);
lean_dec(v_h__2_2329_);
lean_dec(v_h__1_2328_);
v_cases_2347_ = lean_ctor_get(v_code_2327_, 0);
lean_inc_ref(v_cases_2347_);
lean_dec_ref_known(v_code_2327_, 1);
v___x_2348_ = lean_apply_1(v_h__7_2334_, v_cases_2347_);
return v___x_2348_;
}
case 5:
{
lean_object* v_fvarId_2349_; lean_object* v___x_2350_; 
lean_dec(v_h__7_2334_);
lean_dec(v_h__6_2333_);
lean_dec(v_h__5_2332_);
lean_dec(v_h__3_2330_);
lean_dec(v_h__2_2329_);
lean_dec(v_h__1_2328_);
v_fvarId_2349_ = lean_ctor_get(v_code_2327_, 0);
lean_inc(v_fvarId_2349_);
lean_dec_ref_known(v_code_2327_, 1);
v___x_2350_ = lean_apply_1(v_h__4_2331_, v_fvarId_2349_);
return v___x_2350_;
}
default: 
{
lean_object* v_type_2351_; lean_object* v___x_2352_; 
lean_dec(v_h__7_2334_);
lean_dec(v_h__5_2332_);
lean_dec(v_h__4_2331_);
lean_dec(v_h__3_2330_);
lean_dec(v_h__2_2329_);
lean_dec(v_h__1_2328_);
v_type_2351_ = lean_ctor_get(v_code_2327_, 0);
lean_inc_ref(v_type_2351_);
lean_dec_ref_known(v_code_2327_, 1);
v___x_2352_ = lean_apply_1(v_h__6_2333_, v_type_2351_);
return v___x_2352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(uint8_t v_pu_2353_, lean_object* v_params_2354_, lean_object* v_code_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2353_, v_code_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; size_t v_sz_2363_; size_t v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v_sz_2363_ = lean_array_size(v_params_2354_);
v___x_2364_ = ((size_t)0ULL);
v___x_2365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(v_sz_2363_, v___x_2364_, v_params_2354_);
v___x_2366_ = lean_unsigned_to_nat(32u);
v___x_2367_ = lean_mk_empty_array_with_capacity(v___x_2366_);
lean_dec_ref(v___x_2367_);
v___x_2368_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2369_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v___x_2365_, v_a_2362_, v___x_2368_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
lean_dec(v_a_2362_);
lean_dec_ref(v___x_2365_);
return v___x_2369_;
}
else
{
lean_dec_ref(v_params_2354_);
return v___x_2361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType___boxed(lean_object* v_pu_2370_, lean_object* v_params_2371_, lean_object* v_code_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
uint8_t v_pu_boxed_2378_; lean_object* v_res_2379_; 
v_pu_boxed_2378_ = lean_unbox(v_pu_2370_);
v_res_2379_ = l_Lean_Compiler_LCNF_Code_inferParamType(v_pu_boxed_2378_, v_params_2371_, v_code_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType(uint8_t v_pu_2380_, lean_object* v_alt_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_){
_start:
{
switch(lean_obj_tag(v_alt_2381_))
{
case 0:
{
lean_object* v_code_2387_; lean_object* v___x_2388_; 
v_code_2387_ = lean_ctor_get(v_alt_2381_, 2);
lean_inc_ref(v_code_2387_);
lean_dec_ref_known(v_alt_2381_, 3);
v___x_2388_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2380_, v_code_2387_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
return v___x_2388_;
}
case 1:
{
lean_object* v_code_2389_; lean_object* v___x_2390_; 
v_code_2389_ = lean_ctor_get(v_alt_2381_, 1);
lean_inc_ref(v_code_2389_);
lean_dec_ref_known(v_alt_2381_, 2);
v___x_2390_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2380_, v_code_2389_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
return v___x_2390_;
}
default: 
{
lean_object* v_code_2391_; lean_object* v___x_2392_; 
v_code_2391_ = lean_ctor_get(v_alt_2381_, 0);
lean_inc_ref(v_code_2391_);
lean_dec_ref_known(v_alt_2381_, 1);
v___x_2392_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2380_, v_code_2391_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
return v___x_2392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType___boxed(lean_object* v_pu_2393_, lean_object* v_alt_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
uint8_t v_pu_boxed_2400_; lean_object* v_res_2401_; 
v_pu_boxed_2400_ = lean_unbox(v_pu_2393_);
v_res_2401_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_boxed_2400_, v_alt_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t v_pu_2402_, lean_object* v_e_2403_, lean_object* v_prefixName_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_prefixName_2404_, v_a_2406_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2412_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_a_2411_);
lean_dec_ref_known(v___x_2410_, 1);
lean_inc(v_e_2403_);
v___x_2412_ = l_Lean_Compiler_LCNF_LetValue_inferType(v_pu_2402_, v_e_2403_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v___x_2414_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2413_);
lean_dec_ref_known(v___x_2412_, 1);
v___x_2414_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2402_, v_a_2411_, v_a_2413_, v_e_2403_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
return v___x_2414_;
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_dec(v_a_2411_);
lean_dec(v_e_2403_);
v_a_2415_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2412_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2412_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
else
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
lean_dec(v_e_2403_);
v_a_2423_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2425_ = v___x_2410_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2410_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl___boxed(lean_object* v_pu_2431_, lean_object* v_e_2432_, lean_object* v_prefixName_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
uint8_t v_pu_boxed_2439_; lean_object* v_res_2440_; 
v_pu_boxed_2439_ = lean_unbox(v_pu_2431_);
v_res_2440_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v_pu_boxed_2439_, v_e_2432_, v_prefixName_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
return v_res_2440_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkForallParams___closed__1(void){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2442_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2443_ = lean_unsigned_to_nat(15u);
v___x_2444_ = lean_unsigned_to_nat(295u);
v___x_2445_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkForallParams___closed__0));
v___x_2446_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2447_ = l_mkPanicMessageWithDecl(v___x_2446_, v___x_2445_, v___x_2444_, v___x_2443_, v___x_2442_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams(uint8_t v_pu_2448_, lean_object* v_params_2449_, lean_object* v_type_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
if (v_pu_2448_ == 0)
{
lean_object* v___x_2456_; 
v___x_2456_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(v_params_2449_, v_type_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
return v___x_2456_;
}
else
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
lean_dec_ref(v_params_2449_);
v___x_2457_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkForallParams___closed__1, &l_Lean_Compiler_LCNF_mkForallParams___closed__1_once, _init_l_Lean_Compiler_LCNF_mkForallParams___closed__1);
v___x_2458_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2457_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
return v___x_2458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams___boxed(lean_object* v_pu_2459_, lean_object* v_params_2460_, lean_object* v_type_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_){
_start:
{
uint8_t v_pu_boxed_2467_; lean_object* v_res_2468_; 
v_pu_boxed_2467_ = lean_unbox(v_pu_2459_);
v_res_2468_ = l_Lean_Compiler_LCNF_mkForallParams(v_pu_boxed_2467_, v_params_2460_, v_type_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_);
lean_dec(v_a_2465_);
lean_dec_ref(v_a_2464_);
lean_dec(v_a_2463_);
lean_dec_ref(v_a_2462_);
lean_dec_ref(v_type_2461_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(uint8_t v_pu_2469_, lean_object* v_params_2470_, lean_object* v_code_2471_, lean_object* v_prefixName_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v___x_2478_; 
lean_inc_ref(v_code_2471_);
v___x_2478_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2469_, v_code_2471_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2480_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2479_);
lean_dec_ref_known(v___x_2478_, 1);
lean_inc_ref(v_params_2470_);
v___x_2480_ = l_Lean_Compiler_LCNF_mkForallParams(v_pu_2469_, v_params_2470_, v_a_2479_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
lean_dec(v_a_2479_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_a_2481_; lean_object* v___x_2482_; 
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_a_2481_);
lean_dec_ref_known(v___x_2480_, 1);
v___x_2482_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_prefixName_2472_, v_a_2474_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; lean_object* v___x_2484_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_a_2483_);
lean_dec_ref_known(v___x_2482_, 1);
v___x_2484_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_2469_, v_a_2483_, v_a_2481_, v_params_2470_, v_code_2471_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
return v___x_2484_;
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec(v_a_2481_);
lean_dec_ref(v_code_2471_);
lean_dec_ref(v_params_2470_);
v_a_2485_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2482_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2482_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_dec(v_prefixName_2472_);
lean_dec_ref(v_code_2471_);
lean_dec_ref(v_params_2470_);
v_a_2493_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2480_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2480_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_dec(v_prefixName_2472_);
lean_dec_ref(v_code_2471_);
lean_dec_ref(v_params_2470_);
v_a_2501_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2478_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2478_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux___boxed(lean_object* v_pu_2509_, lean_object* v_params_2510_, lean_object* v_code_2511_, lean_object* v_prefixName_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_){
_start:
{
uint8_t v_pu_boxed_2518_; lean_object* v_res_2519_; 
v_pu_boxed_2518_ = lean_unbox(v_pu_2509_);
v_res_2519_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_boxed_2518_, v_params_2510_, v_code_2511_, v_prefixName_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object* v_params_2520_, lean_object* v_code_2521_, lean_object* v_prefixName_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
uint8_t v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = 0;
v___x_2529_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v___x_2528_, v_params_2520_, v_code_2521_, v_prefixName_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl___boxed(lean_object* v_params_2530_, lean_object* v_code_2531_, lean_object* v_prefixName_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v_params_2530_, v_code_2531_, v_prefixName_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
lean_dec(v_a_2536_);
lean_dec_ref(v_a_2535_);
lean_dec(v_a_2534_);
lean_dec_ref(v_a_2533_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(uint8_t v_pu_2539_, lean_object* v_params_2540_, lean_object* v_code_2541_, lean_object* v_prefixName_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v___x_2548_; 
v___x_2548_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_2539_, v_params_2540_, v_code_2541_, v_prefixName_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl___boxed(lean_object* v_pu_2549_, lean_object* v_params_2550_, lean_object* v_code_2551_, lean_object* v_prefixName_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
uint8_t v_pu_boxed_2558_; lean_object* v_res_2559_; 
v_pu_boxed_2558_ = lean_unbox(v_pu_2549_);
v_res_2559_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v_pu_boxed_2558_, v_params_2550_, v_code_2551_, v_prefixName_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
lean_dec(v_a_2556_);
lean_dec_ref(v_a_2555_);
lean_dec(v_a_2554_);
lean_dec_ref(v_a_2553_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(uint8_t v_pu_2560_, lean_object* v_param_2561_, lean_object* v_code_2562_, lean_object* v_prefixName_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v_params_2571_; lean_object* v___x_2572_; 
v___x_2569_ = lean_unsigned_to_nat(1u);
v___x_2570_ = lean_mk_empty_array_with_capacity(v___x_2569_);
v_params_2571_ = lean_array_push(v___x_2570_, v_param_2561_);
v___x_2572_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_2560_, v_params_2571_, v_code_2562_, v_prefixName_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___boxed(lean_object* v_pu_2573_, lean_object* v_param_2574_, lean_object* v_code_2575_, lean_object* v_prefixName_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_){
_start:
{
uint8_t v_pu_boxed_2582_; lean_object* v_res_2583_; 
v_pu_boxed_2582_ = lean_unbox(v_pu_2573_);
v_res_2583_ = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(v_pu_boxed_2582_, v_param_2574_, v_code_2575_, v_prefixName_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
lean_dec(v_a_2578_);
lean_dec_ref(v_a_2577_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(lean_object* v_msg_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v_ref_2590_; lean_object* v___x_2591_; lean_object* v_env_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v_ref_2590_ = lean_ctor_get(v___y_2587_, 2);
v___x_2591_ = lean_st_ref_get(v___y_2588_);
v_env_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc_ref(v_env_2592_);
lean_dec(v___x_2591_);
v___x_2593_ = lean_st_ref_get(v___y_2586_);
v___x_2594_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_2585_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2617_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2597_ = v___x_2594_;
v_isShared_2598_ = v_isSharedCheck_2617_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2594_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2617_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v_lctx_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2615_; 
v_lctx_2599_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2615_ == 0)
{
lean_object* v_unused_2616_; 
v_unused_2616_ = lean_ctor_get(v___x_2593_, 1);
lean_dec(v_unused_2616_);
v___x_2601_ = v___x_2593_;
v_isShared_2602_ = v_isSharedCheck_2615_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_lctx_2599_);
lean_dec(v___x_2593_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2615_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
uint8_t v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2609_; 
v___x_2603_ = lean_unbox(v_a_2595_);
lean_dec(v_a_2595_);
v___x_2604_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2599_, v___x_2603_);
lean_dec_ref(v_lctx_2599_);
v___x_2605_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2587_);
v___x_2606_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1);
v___x_2607_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2607_, 0, v_env_2592_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
lean_ctor_set(v___x_2607_, 2, v___x_2604_);
lean_ctor_set(v___x_2607_, 3, v___x_2605_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set_tag(v___x_2601_, 3);
lean_ctor_set(v___x_2601_, 1, v_msg_2584_);
lean_ctor_set(v___x_2601_, 0, v___x_2607_);
v___x_2609_ = v___x_2601_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2607_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v_msg_2584_);
v___x_2609_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
lean_object* v___x_2610_; lean_object* v___x_2612_; 
lean_inc(v_ref_2590_);
v___x_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2610_, 0, v_ref_2590_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set_tag(v___x_2597_, 1);
lean_ctor_set(v___x_2597_, 0, v___x_2610_);
v___x_2612_ = v___x_2597_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
lean_dec(v___x_2593_);
lean_dec_ref(v_env_2592_);
lean_dec_ref(v_msg_2584_);
v_a_2618_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2594_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2594_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg___boxed(lean_object* v_msg_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v_msg_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1(lean_object* v_00_u03b1_2633_, lean_object* v_msg_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v_msg_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___boxed(lean_object* v_00_u03b1_2641_, lean_object* v_msg_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1(v_00_u03b1_2641_, v_msg_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(uint8_t v_pu_2649_, lean_object* v_a_2650_, lean_object* v_b_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v_array_2657_; lean_object* v_start_2658_; lean_object* v_stop_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2675_; 
v_array_2657_ = lean_ctor_get(v_a_2650_, 0);
v_start_2658_ = lean_ctor_get(v_a_2650_, 1);
v_stop_2659_ = lean_ctor_get(v_a_2650_, 2);
v_isSharedCheck_2675_ = !lean_is_exclusive(v_a_2650_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2661_ = v_a_2650_;
v_isShared_2662_ = v_isSharedCheck_2675_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_stop_2659_);
lean_inc(v_start_2658_);
lean_inc(v_array_2657_);
lean_dec(v_a_2650_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2675_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
uint8_t v___x_2663_; 
v___x_2663_ = lean_nat_dec_lt(v_start_2658_, v_stop_2659_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; 
lean_del_object(v___x_2661_);
lean_dec(v_stop_2659_);
lean_dec(v_start_2658_);
lean_dec_ref(v_array_2657_);
v___x_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2664_, 0, v_b_2651_);
return v___x_2664_;
}
else
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2668_; 
v___x_2665_ = lean_unsigned_to_nat(1u);
v___x_2666_ = lean_nat_add(v_start_2658_, v___x_2665_);
lean_inc_ref(v_array_2657_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 1, v___x_2666_);
v___x_2668_ = v___x_2661_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_array_2657_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2674_, 2, v_stop_2659_);
v___x_2668_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = lean_array_fget(v_array_2657_, v_start_2658_);
lean_dec(v_start_2658_);
lean_dec_ref(v_array_2657_);
v___x_2670_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_2649_, v___x_2669_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v___x_2672_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v___x_2670_, 1);
v___x_2672_ = l_Lean_Compiler_LCNF_joinTypes(v_b_2651_, v_a_2671_);
v_a_2650_ = v___x_2668_;
v_b_2651_ = v___x_2672_;
goto _start;
}
else
{
lean_dec_ref(v___x_2668_);
lean_dec_ref(v_b_2651_);
return v___x_2670_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg___boxed(lean_object* v_pu_2676_, lean_object* v_a_2677_, lean_object* v_b_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
uint8_t v_pu_boxed_2684_; lean_object* v_res_2685_; 
v_pu_boxed_2684_ = lean_unbox(v_pu_2676_);
v_res_2685_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_boxed_2684_, v_a_2677_, v_b_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
return v_res_2685_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__0(void){
_start:
{
lean_object* v___x_2686_; 
v___x_2686_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
return v___x_2686_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__2(void){
_start:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2688_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkCasesResultType___closed__1));
v___x_2689_ = l_Lean_stringToMessageData(v___x_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(uint8_t v_pu_2690_, lean_object* v_alts_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v___x_2697_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___x_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; 
v___x_2697_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkCasesResultType___closed__0, &l_Lean_Compiler_LCNF_mkCasesResultType___closed__0_once, _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__0);
v___x_2711_ = lean_array_get_size(v_alts_2691_);
v___x_2712_ = lean_unsigned_to_nat(0u);
v___x_2713_ = lean_nat_dec_eq(v___x_2711_, v___x_2712_);
if (v___x_2713_ == 0)
{
v___y_2699_ = v_a_2692_;
v___y_2700_ = v_a_2693_;
v___y_2701_ = v_a_2694_;
v___y_2702_ = v_a_2695_;
goto v___jp_2698_;
}
else
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
lean_dec_ref(v_alts_2691_);
v___x_2714_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkCasesResultType___closed__2, &l_Lean_Compiler_LCNF_mkCasesResultType___closed__2_once, _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__2);
v___x_2715_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v___x_2714_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
v___jp_2698_:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2703_ = lean_unsigned_to_nat(0u);
v___x_2704_ = lean_array_get_borrowed(v___x_2697_, v_alts_2691_, v___x_2703_);
lean_inc(v___x_2704_);
v___x_2705_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_2690_, v___x_2704_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2705_, 1);
v___x_2707_ = lean_unsigned_to_nat(1u);
v___x_2708_ = lean_array_get_size(v_alts_2691_);
v___x_2709_ = l_Array_toSubarray___redArg(v_alts_2691_, v___x_2707_, v___x_2708_);
v___x_2710_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_2690_, v___x_2709_, v_a_2706_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
return v___x_2710_;
}
else
{
lean_dec_ref(v_alts_2691_);
return v___x_2705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___boxed(lean_object* v_pu_2724_, lean_object* v_alts_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_){
_start:
{
uint8_t v_pu_boxed_2731_; lean_object* v_res_2732_; 
v_pu_boxed_2731_ = lean_unbox(v_pu_2724_);
v_res_2732_ = l_Lean_Compiler_LCNF_mkCasesResultType(v_pu_boxed_2731_, v_alts_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
lean_dec(v_a_2729_);
lean_dec_ref(v_a_2728_);
lean_dec(v_a_2727_);
lean_dec_ref(v_a_2726_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0(uint8_t v_pu_2733_, lean_object* v_inst_2734_, lean_object* v_R_2735_, lean_object* v_a_2736_, lean_object* v_b_2737_, lean_object* v_c_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_2733_, v_a_2736_, v_b_2737_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___boxed(lean_object* v_pu_2745_, lean_object* v_inst_2746_, lean_object* v_R_2747_, lean_object* v_a_2748_, lean_object* v_b_2749_, lean_object* v_c_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
uint8_t v_pu_boxed_2756_; lean_object* v_res_2757_; 
v_pu_boxed_2756_ = lean_unbox(v_pu_2745_);
v_res_2757_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0(v_pu_boxed_2756_, v_inst_2746_, v_R_2747_, v_a_2748_, v_b_2749_, v_c_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(lean_object* v_msg_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v___x_2764_; lean_object* v_toApplicative_2765_; lean_object* v_toFunctor_2766_; lean_object* v_toSeq_2767_; lean_object* v_toSeqLeft_2768_; lean_object* v_toSeqRight_2769_; lean_object* v___f_2770_; lean_object* v___f_2771_; lean_object* v___f_2772_; lean_object* v___f_2773_; lean_object* v___x_2774_; lean_object* v___f_2775_; lean_object* v___f_2776_; lean_object* v___f_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; uint8_t v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___f_2784_; lean_object* v___x_970__overap_2785_; lean_object* v___x_2786_; 
v___x_2764_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_2765_ = lean_ctor_get(v___x_2764_, 0);
v_toFunctor_2766_ = lean_ctor_get(v_toApplicative_2765_, 0);
v_toSeq_2767_ = lean_ctor_get(v_toApplicative_2765_, 2);
v_toSeqLeft_2768_ = lean_ctor_get(v_toApplicative_2765_, 3);
v_toSeqRight_2769_ = lean_ctor_get(v_toApplicative_2765_, 4);
v___f_2770_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_2771_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2766_, 2);
v___f_2772_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2772_, 0, v_toFunctor_2766_);
v___f_2773_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2773_, 0, v_toFunctor_2766_);
v___x_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___f_2772_);
lean_ctor_set(v___x_2774_, 1, v___f_2773_);
lean_inc(v_toSeqRight_2769_);
v___f_2775_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2775_, 0, v_toSeqRight_2769_);
lean_inc(v_toSeqLeft_2768_);
v___f_2776_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2776_, 0, v_toSeqLeft_2768_);
lean_inc(v_toSeq_2767_);
v___f_2777_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2777_, 0, v_toSeq_2767_);
v___x_2778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2774_);
lean_ctor_set(v___x_2778_, 1, v___f_2770_);
lean_ctor_set(v___x_2778_, 2, v___f_2777_);
lean_ctor_set(v___x_2778_, 3, v___f_2776_);
lean_ctor_set(v___x_2778_, 4, v___f_2775_);
v___x_2779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2778_);
lean_ctor_set(v___x_2779_, 1, v___f_2771_);
v___x_2780_ = l_StateRefT_x27_instMonad___redArg(v___x_2779_);
v___x_2781_ = 0;
v___x_2782_ = lean_box(v___x_2781_);
v___x_2783_ = l_instInhabitedOfMonad___redArg(v___x_2780_, v___x_2782_);
v___f_2784_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2784_, 0, v___x_2783_);
v___x_970__overap_2785_ = lean_panic_fn_borrowed(v___f_2784_, v_msg_2758_);
lean_dec_ref(v___f_2784_);
lean_inc(v___y_2762_);
lean_inc_ref(v___y_2761_);
lean_inc(v___y_2760_);
lean_inc_ref(v___y_2759_);
v___x_2786_ = lean_apply_5(v___x_970__overap_2785_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, lean_box(0));
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0___boxed(lean_object* v_msg_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(v_msg_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
return v_res_2793_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1(void){
_start:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2795_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2));
v___x_2796_ = lean_unsigned_to_nat(50u);
v___x_2797_ = lean_unsigned_to_nat(345u);
v___x_2798_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__0));
v___x_2799_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2800_ = l_mkPanicMessageWithDecl(v___x_2799_, v___x_2798_, v___x_2797_, v___x_2796_, v___x_2795_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(lean_object* v_type_2801_, lean_object* v_predVars_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v_t_2809_; lean_object* v_b_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v_type_2819_; 
v_type_2819_ = l_Lean_Expr_headBeta(v_type_2801_);
switch(lean_obj_tag(v_type_2819_))
{
case 0:
{
lean_object* v_deBruijnIndex_2820_; uint8_t v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v_deBruijnIndex_2820_ = lean_ctor_get(v_type_2819_, 0);
lean_inc(v_deBruijnIndex_2820_);
lean_dec_ref_known(v_type_2819_, 1);
v___x_2821_ = 0;
v___x_2822_ = lean_array_get_size(v_predVars_2802_);
v___x_2823_ = lean_nat_sub(v___x_2822_, v_deBruijnIndex_2820_);
lean_dec(v_deBruijnIndex_2820_);
v___x_2824_ = lean_unsigned_to_nat(1u);
v___x_2825_ = lean_nat_sub(v___x_2823_, v___x_2824_);
lean_dec(v___x_2823_);
v___x_2826_ = lean_box(v___x_2821_);
v___x_2827_ = lean_array_get(v___x_2826_, v_predVars_2802_, v___x_2825_);
lean_dec(v___x_2825_);
lean_dec_ref(v_predVars_2802_);
lean_dec(v___x_2826_);
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
return v___x_2828_;
}
case 1:
{
lean_object* v_fvarId_2829_; lean_object* v___x_2830_; 
lean_dec_ref(v_predVars_2802_);
v_fvarId_2829_ = lean_ctor_get(v_type_2819_, 0);
lean_inc(v_fvarId_2829_);
lean_dec_ref_known(v_type_2819_, 1);
v___x_2830_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2829_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2840_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2833_ = v___x_2830_;
v_isShared_2834_ = v_isSharedCheck_2840_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2830_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2840_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
uint8_t v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2838_; 
v___x_2835_ = l_Lean_Compiler_LCNF_isPredicateType(v_a_2831_);
v___x_2836_ = lean_box(v___x_2835_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 0, v___x_2836_);
v___x_2838_ = v___x_2833_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2836_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
else
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
v_a_2841_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2830_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2830_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
case 3:
{
uint8_t v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; 
lean_dec_ref_known(v_type_2819_, 1);
lean_dec_ref(v_predVars_2802_);
v___x_2849_ = 0;
v___x_2850_ = lean_box(v___x_2849_);
v___x_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2850_);
return v___x_2851_;
}
case 4:
{
uint8_t v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
lean_dec_ref(v_predVars_2802_);
v___x_2852_ = l_Lean_Expr_isErased(v_type_2819_);
lean_dec_ref_known(v_type_2819_, 2);
v___x_2853_ = lean_box(v___x_2852_);
v___x_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
return v___x_2854_;
}
case 5:
{
lean_object* v_fn_2855_; 
v_fn_2855_ = lean_ctor_get(v_type_2819_, 0);
lean_inc_ref(v_fn_2855_);
lean_dec_ref_known(v_type_2819_, 2);
v_type_2801_ = v_fn_2855_;
goto _start;
}
case 6:
{
lean_object* v_binderType_2857_; lean_object* v_body_2858_; 
v_binderType_2857_ = lean_ctor_get(v_type_2819_, 1);
lean_inc_ref(v_binderType_2857_);
v_body_2858_ = lean_ctor_get(v_type_2819_, 2);
lean_inc_ref(v_body_2858_);
lean_dec_ref_known(v_type_2819_, 3);
v_t_2809_ = v_binderType_2857_;
v_b_2810_ = v_body_2858_;
v___y_2811_ = v_a_2803_;
v___y_2812_ = v_a_2804_;
v___y_2813_ = v_a_2805_;
v___y_2814_ = v_a_2806_;
goto v___jp_2808_;
}
case 7:
{
lean_object* v_binderType_2859_; lean_object* v_body_2860_; 
v_binderType_2859_ = lean_ctor_get(v_type_2819_, 1);
lean_inc_ref(v_binderType_2859_);
v_body_2860_ = lean_ctor_get(v_type_2819_, 2);
lean_inc_ref(v_body_2860_);
lean_dec_ref_known(v_type_2819_, 3);
v_t_2809_ = v_binderType_2859_;
v_b_2810_ = v_body_2860_;
v___y_2811_ = v_a_2803_;
v___y_2812_ = v_a_2804_;
v___y_2813_ = v_a_2805_;
v___y_2814_ = v_a_2806_;
goto v___jp_2808_;
}
case 10:
{
lean_object* v_expr_2861_; 
v_expr_2861_ = lean_ctor_get(v_type_2819_, 1);
lean_inc_ref(v_expr_2861_);
lean_dec_ref_known(v_type_2819_, 2);
v_type_2801_ = v_expr_2861_;
goto _start;
}
default: 
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
lean_dec_ref(v_type_2819_);
lean_dec_ref(v_predVars_2802_);
v___x_2863_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1, &l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1);
v___x_2864_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(v___x_2863_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
return v___x_2864_;
}
}
v___jp_2808_:
{
uint8_t v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2815_ = l_Lean_Compiler_LCNF_isPredicateType(v_t_2809_);
v___x_2816_ = lean_box(v___x_2815_);
v___x_2817_ = lean_array_push(v_predVars_2802_, v___x_2816_);
v_type_2801_ = v_b_2810_;
v_predVars_2802_ = v___x_2817_;
v_a_2803_ = v___y_2811_;
v_a_2804_ = v___y_2812_;
v_a_2805_ = v___y_2813_;
v_a_2806_ = v___y_2814_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___boxed(lean_object* v_type_2865_, lean_object* v_predVars_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(v_type_2865_, v_predVars_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
lean_dec(v_a_2870_);
lean_dec_ref(v_a_2869_);
lean_dec(v_a_2868_);
lean_dec_ref(v_a_2867_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible(lean_object* v_type_2873_, lean_object* v_predVars_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(v_type_2873_, v_predVars_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible___boxed(lean_object* v_type_2881_, lean_object* v_predVars_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Lean_Compiler_LCNF_isErasedCompatible(v_type_2881_, v_predVars_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
lean_dec(v_a_2884_);
lean_dec_ref(v_a_2883_);
return v_res_2888_;
}
}
LEAN_EXPORT uint8_t l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(lean_object* v_x_2889_, lean_object* v_x_2890_){
_start:
{
if (lean_obj_tag(v_x_2889_) == 0)
{
if (lean_obj_tag(v_x_2890_) == 0)
{
uint8_t v___x_2891_; 
v___x_2891_ = 1;
return v___x_2891_;
}
else
{
uint8_t v___x_2892_; 
v___x_2892_ = 0;
return v___x_2892_;
}
}
else
{
if (lean_obj_tag(v_x_2890_) == 0)
{
uint8_t v___x_2893_; 
v___x_2893_ = 0;
return v___x_2893_;
}
else
{
lean_object* v_head_2894_; lean_object* v_tail_2895_; lean_object* v_head_2896_; lean_object* v_tail_2897_; uint8_t v___x_2898_; 
v_head_2894_ = lean_ctor_get(v_x_2889_, 0);
v_tail_2895_ = lean_ctor_get(v_x_2889_, 1);
v_head_2896_ = lean_ctor_get(v_x_2890_, 0);
v_tail_2897_ = lean_ctor_get(v_x_2890_, 1);
v___x_2898_ = l_Lean_Level_isEquiv(v_head_2894_, v_head_2896_);
if (v___x_2898_ == 0)
{
return v___x_2898_;
}
else
{
v_x_2889_ = v_tail_2895_;
v_x_2890_ = v_tail_2897_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0___boxed(lean_object* v_x_2900_, lean_object* v_x_2901_){
_start:
{
uint8_t v_res_2902_; lean_object* v_r_2903_; 
v_res_2902_ = l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(v_x_2900_, v_x_2901_);
lean_dec(v_x_2901_);
lean_dec(v_x_2900_);
v_r_2903_ = lean_box(v_res_2902_);
return v_r_2903_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_eqvTypes(lean_object* v_a_2904_, lean_object* v_b_2905_){
_start:
{
uint8_t v___x_2906_; lean_object* v_d_u2081_2908_; lean_object* v_b_u2081_2909_; lean_object* v_d_u2082_2910_; lean_object* v_b_u2082_2911_; uint8_t v___x_2914_; uint8_t v___y_2916_; 
v___x_2906_ = lean_expr_eqv(v_a_2904_, v_b_2905_);
v___x_2914_ = 1;
if (v___x_2906_ == 0)
{
uint8_t v___x_2960_; 
v___x_2960_ = l_Lean_Expr_isErased(v_a_2904_);
if (v___x_2960_ == 0)
{
v___y_2916_ = v___x_2906_;
goto v___jp_2915_;
}
else
{
uint8_t v___x_2961_; 
v___x_2961_ = l_Lean_Expr_isErased(v_b_2905_);
v___y_2916_ = v___x_2961_;
goto v___jp_2915_;
}
}
else
{
lean_dec_ref(v_b_2905_);
lean_dec_ref(v_a_2904_);
return v___x_2914_;
}
v___jp_2907_:
{
uint8_t v___x_2912_; 
v___x_2912_ = l_Lean_Compiler_LCNF_eqvTypes(v_d_u2081_2908_, v_d_u2082_2910_);
if (v___x_2912_ == 0)
{
lean_dec_ref(v_b_u2082_2911_);
lean_dec_ref(v_b_u2081_2909_);
return v___x_2906_;
}
else
{
v_a_2904_ = v_b_u2081_2909_;
v_b_2905_ = v_b_u2082_2911_;
goto _start;
}
}
v___jp_2915_:
{
if (v___y_2916_ == 0)
{
lean_object* v_a_x27_2917_; lean_object* v_b_x27_2918_; uint8_t v___x_2919_; 
lean_inc_ref(v_a_2904_);
v_a_x27_2917_ = l_Lean_Expr_headBeta(v_a_2904_);
lean_inc_ref(v_b_2905_);
v_b_x27_2918_ = l_Lean_Expr_headBeta(v_b_2905_);
v___x_2919_ = lean_expr_eqv(v_a_2904_, v_a_x27_2917_);
if (v___x_2919_ == 0)
{
lean_dec_ref(v_b_2905_);
lean_dec_ref(v_a_2904_);
v_a_2904_ = v_a_x27_2917_;
v_b_2905_ = v_b_x27_2918_;
goto _start;
}
else
{
uint8_t v___x_2921_; 
v___x_2921_ = lean_expr_eqv(v_b_2905_, v_b_x27_2918_);
if (v___x_2921_ == 0)
{
lean_dec_ref(v_b_2905_);
lean_dec_ref(v_a_2904_);
v_a_2904_ = v_a_x27_2917_;
v_b_2905_ = v_b_x27_2918_;
goto _start;
}
else
{
lean_dec_ref(v_b_x27_2918_);
lean_dec_ref(v_a_x27_2917_);
switch(lean_obj_tag(v_a_2904_))
{
case 10:
{
lean_object* v_expr_2923_; 
v_expr_2923_ = lean_ctor_get(v_a_2904_, 1);
lean_inc_ref(v_expr_2923_);
lean_dec_ref_known(v_a_2904_, 2);
v_a_2904_ = v_expr_2923_;
goto _start;
}
case 5:
{
switch(lean_obj_tag(v_b_2905_))
{
case 10:
{
lean_object* v_expr_2925_; 
v_expr_2925_ = lean_ctor_get(v_b_2905_, 1);
lean_inc_ref(v_expr_2925_);
lean_dec_ref_known(v_b_2905_, 2);
v_b_2905_ = v_expr_2925_;
goto _start;
}
case 5:
{
lean_object* v_fn_2927_; lean_object* v_arg_2928_; lean_object* v_fn_2929_; lean_object* v_arg_2930_; uint8_t v___x_2931_; 
v_fn_2927_ = lean_ctor_get(v_a_2904_, 0);
lean_inc_ref(v_fn_2927_);
v_arg_2928_ = lean_ctor_get(v_a_2904_, 1);
lean_inc_ref(v_arg_2928_);
lean_dec_ref_known(v_a_2904_, 2);
v_fn_2929_ = lean_ctor_get(v_b_2905_, 0);
lean_inc_ref(v_fn_2929_);
v_arg_2930_ = lean_ctor_get(v_b_2905_, 1);
lean_inc_ref(v_arg_2930_);
lean_dec_ref_known(v_b_2905_, 2);
v___x_2931_ = l_Lean_Compiler_LCNF_eqvTypes(v_fn_2927_, v_fn_2929_);
if (v___x_2931_ == 0)
{
lean_dec_ref(v_arg_2930_);
lean_dec_ref(v_arg_2928_);
return v___x_2906_;
}
else
{
v_a_2904_ = v_arg_2928_;
v_b_2905_ = v_arg_2930_;
goto _start;
}
}
default: 
{
lean_dec_ref_known(v_a_2904_, 2);
lean_dec_ref(v_b_2905_);
return v___y_2916_;
}
}
}
case 7:
{
switch(lean_obj_tag(v_b_2905_))
{
case 10:
{
lean_object* v_expr_2933_; 
v_expr_2933_ = lean_ctor_get(v_b_2905_, 1);
lean_inc_ref(v_expr_2933_);
lean_dec_ref_known(v_b_2905_, 2);
v_b_2905_ = v_expr_2933_;
goto _start;
}
case 7:
{
lean_object* v_binderType_2935_; lean_object* v_body_2936_; lean_object* v_binderType_2937_; lean_object* v_body_2938_; 
v_binderType_2935_ = lean_ctor_get(v_a_2904_, 1);
lean_inc_ref(v_binderType_2935_);
v_body_2936_ = lean_ctor_get(v_a_2904_, 2);
lean_inc_ref(v_body_2936_);
lean_dec_ref_known(v_a_2904_, 3);
v_binderType_2937_ = lean_ctor_get(v_b_2905_, 1);
lean_inc_ref(v_binderType_2937_);
v_body_2938_ = lean_ctor_get(v_b_2905_, 2);
lean_inc_ref(v_body_2938_);
lean_dec_ref_known(v_b_2905_, 3);
v_d_u2081_2908_ = v_binderType_2935_;
v_b_u2081_2909_ = v_body_2936_;
v_d_u2082_2910_ = v_binderType_2937_;
v_b_u2082_2911_ = v_body_2938_;
goto v___jp_2907_;
}
default: 
{
lean_dec_ref_known(v_a_2904_, 3);
lean_dec_ref(v_b_2905_);
return v___y_2916_;
}
}
}
case 6:
{
switch(lean_obj_tag(v_b_2905_))
{
case 10:
{
lean_object* v_expr_2939_; 
v_expr_2939_ = lean_ctor_get(v_b_2905_, 1);
lean_inc_ref(v_expr_2939_);
lean_dec_ref_known(v_b_2905_, 2);
v_b_2905_ = v_expr_2939_;
goto _start;
}
case 6:
{
lean_object* v_binderType_2941_; lean_object* v_body_2942_; lean_object* v_binderType_2943_; lean_object* v_body_2944_; 
v_binderType_2941_ = lean_ctor_get(v_a_2904_, 1);
lean_inc_ref(v_binderType_2941_);
v_body_2942_ = lean_ctor_get(v_a_2904_, 2);
lean_inc_ref(v_body_2942_);
lean_dec_ref_known(v_a_2904_, 3);
v_binderType_2943_ = lean_ctor_get(v_b_2905_, 1);
lean_inc_ref(v_binderType_2943_);
v_body_2944_ = lean_ctor_get(v_b_2905_, 2);
lean_inc_ref(v_body_2944_);
lean_dec_ref_known(v_b_2905_, 3);
v_d_u2081_2908_ = v_binderType_2941_;
v_b_u2081_2909_ = v_body_2942_;
v_d_u2082_2910_ = v_binderType_2943_;
v_b_u2082_2911_ = v_body_2944_;
goto v___jp_2907_;
}
default: 
{
lean_dec_ref_known(v_a_2904_, 3);
lean_dec_ref(v_b_2905_);
return v___y_2916_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_b_2905_))
{
case 10:
{
lean_object* v_expr_2945_; 
v_expr_2945_ = lean_ctor_get(v_b_2905_, 1);
lean_inc_ref(v_expr_2945_);
lean_dec_ref_known(v_b_2905_, 2);
v_b_2905_ = v_expr_2945_;
goto _start;
}
case 3:
{
lean_object* v_u_2947_; lean_object* v_u_2948_; uint8_t v___x_2949_; 
v_u_2947_ = lean_ctor_get(v_a_2904_, 0);
lean_inc(v_u_2947_);
lean_dec_ref_known(v_a_2904_, 1);
v_u_2948_ = lean_ctor_get(v_b_2905_, 0);
lean_inc(v_u_2948_);
lean_dec_ref_known(v_b_2905_, 1);
v___x_2949_ = l_Lean_Level_isEquiv(v_u_2947_, v_u_2948_);
lean_dec(v_u_2948_);
lean_dec(v_u_2947_);
return v___x_2949_;
}
default: 
{
lean_dec_ref_known(v_a_2904_, 1);
lean_dec_ref(v_b_2905_);
return v___y_2916_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_b_2905_))
{
case 10:
{
lean_object* v_expr_2950_; 
v_expr_2950_ = lean_ctor_get(v_b_2905_, 1);
lean_inc_ref(v_expr_2950_);
lean_dec_ref_known(v_b_2905_, 2);
v_b_2905_ = v_expr_2950_;
goto _start;
}
case 4:
{
lean_object* v_declName_2952_; lean_object* v_us_2953_; lean_object* v_declName_2954_; lean_object* v_us_2955_; uint8_t v___x_2956_; 
v_declName_2952_ = lean_ctor_get(v_a_2904_, 0);
lean_inc(v_declName_2952_);
v_us_2953_ = lean_ctor_get(v_a_2904_, 1);
lean_inc(v_us_2953_);
lean_dec_ref_known(v_a_2904_, 2);
v_declName_2954_ = lean_ctor_get(v_b_2905_, 0);
lean_inc(v_declName_2954_);
v_us_2955_ = lean_ctor_get(v_b_2905_, 1);
lean_inc(v_us_2955_);
lean_dec_ref_known(v_b_2905_, 2);
v___x_2956_ = lean_name_eq(v_declName_2952_, v_declName_2954_);
lean_dec(v_declName_2954_);
lean_dec(v_declName_2952_);
if (v___x_2956_ == 0)
{
lean_dec(v_us_2955_);
lean_dec(v_us_2953_);
return v___x_2906_;
}
else
{
uint8_t v___x_2957_; 
v___x_2957_ = l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(v_us_2953_, v_us_2955_);
lean_dec(v_us_2955_);
lean_dec(v_us_2953_);
return v___x_2957_;
}
}
default: 
{
lean_dec_ref_known(v_a_2904_, 2);
lean_dec_ref(v_b_2905_);
return v___y_2916_;
}
}
}
default: 
{
if (lean_obj_tag(v_b_2905_) == 10)
{
lean_object* v_expr_2958_; 
v_expr_2958_ = lean_ctor_get(v_b_2905_, 1);
lean_inc_ref(v_expr_2958_);
lean_dec_ref_known(v_b_2905_, 2);
v_b_2905_ = v_expr_2958_;
goto _start;
}
else
{
lean_dec_ref(v_b_2905_);
lean_dec_ref(v_a_2904_);
return v___y_2916_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_b_2905_);
lean_dec_ref(v_a_2904_);
return v___x_2914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eqvTypes___boxed(lean_object* v_a_2962_, lean_object* v_b_2963_){
_start:
{
uint8_t v_res_2964_; lean_object* v_r_2965_; 
v_res_2964_ = l_Lean_Compiler_LCNF_eqvTypes(v_a_2962_, v_b_2963_);
v_r_2965_ = lean_box(v_res_2964_);
return v_r_2965_;
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
