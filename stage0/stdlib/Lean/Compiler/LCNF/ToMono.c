// Lean compiler output
// Module: Lean.Compiler.LCNF.ToMono
// Imports: public import Lean.Compiler.ImplementedByAttr public import Lean.Compiler.LCNF.InferType public import Lean.Compiler.NoncomputableAttr public import Lean.Compiler.LCNF.MonoTypes import Init.While
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default(uint8_t);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(uint8_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_anyExpr;
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toMonoType(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isTypeFormerType(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedLetValue_default(uint8_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_Compiler_getImplementedBy_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_argToMono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_argToMono___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_argToMono___redArg___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_argToMono___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_argToMono___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_argToMono___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argsToMonoWithFnType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argsToMonoWithFnType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_ctorAppToMono___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_ctorAppToMono___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ctorAppToMono___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ctorAppToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ctorAppToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4_value;
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Quot"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__2_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 113, 137, 82, 82, 132, 58, 248)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "lcInv"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__4_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__3_value),LEAN_SCALAR_PTR_LITERAL(246, 129, 23, 78, 51, 209, 87, 155)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__4_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__5_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__5_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__7_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__6_value),LEAN_SCALAR_PTR_LITERAL(51, 81, 163, 94, 71, 156, 90, 186)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__7_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__5_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__9_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__8_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__9_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Compiler.LCNF.ToMono"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__10_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Compiler.LCNF.LetValue.toMono"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__11_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__12_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_LetValue_toMono___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__13;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__14_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__14_value)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Lean.Compiler.LCNF.mkFieldParamsForComputedFields"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__2(lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toMono___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__2;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "expected inductive type"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Compiler.LCNF.Code.toMono"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toMono___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__4;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toMono___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__5;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__5_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__5_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__7_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__6_value),LEAN_SCALAR_PTR_LITERAL(210, 189, 86, 121, 130, 22, 242, 236)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__7_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__5_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__8_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__9_value;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__10_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__10_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__11_value;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__12_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__12_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__13_value;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__14_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__14_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__15_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__16_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ByteArray"};
static const lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(16, 14, 5, 86, 33, 2, 113, 205)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__17 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__17_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "FloatArray"};
static const lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(159, 8, 149, 159, 140, 65, 145, 29)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__18 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__18_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__19 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__19_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Float"};
static const lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(56, 69, 114, 85, 163, 177, 220, 67)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__20 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__20_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Float32"};
static const lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 232, 182, 48, 64, 193, 160, 231)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__21 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__21_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Thunk"};
static const lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(85, 24, 139, 128, 157, 117, 211, 220)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__22 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__22_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Task"};
static const lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(189, 131, 95, 48, 7, 243, 177, 18)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__23 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__23_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "assertion violation: c.alts.size == 1\n  "};
static const lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_trivialStructToMono___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Compiler.LCNF.trivialStructToMono"};
static const lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_trivialStructToMono___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_trivialStructToMono___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3;
static const lean_string_object l_Lean_Compiler_LCNF_trivialStructToMono___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "assertion violation: ctorName == info.ctorName\n  "};
static const lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_trivialStructToMono___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_trivialStructToMono___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___closed__3;
static const lean_string_object l_Lean_Compiler_LCNF_trivialStructToMono___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "assertion violation: info.fieldIdx < ps.size\n  "};
static const lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_trivialStructToMono___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_trivialStructToMono___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___closed__5;
static lean_once_cell_t l_Lean_Compiler_LCNF_trivialStructToMono___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected constructor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_impl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__3_value),LEAN_SCALAR_PTR_LITERAL(130, 78, 106, 49, 240, 167, 66, 80)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Compiler.LCNF.casesTaskToMono"};
static const lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "get"};
static const lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(189, 131, 95, 48, 7, 243, 177, 18)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(19, 166, 147, 197, 228, 63, 159, 146)}};
static const lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Compiler.LCNF.casesThunkToMono"};
static const lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(85, 24, 139, 128, 157, 117, 211, 220)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 110, 84, 99, 226, 14, 63, 127)}};
static const lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PUnit"};
static const lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(23, 153, 158, 141, 176, 162, 235, 153)}};
static const lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Compiler.LCNF.casesFloat32ToMono"};
static const lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toModel"};
static const lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 232, 182, 48, 64, 193, 160, 231)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(100, 9, 102, 51, 239, 149, 150, 6)}};
static const lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Compiler.LCNF.casesFloatToMono"};
static const lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(56, 69, 114, 85, 163, 177, 220, 67)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(34, 196, 85, 139, 247, 89, 238, 57)}};
static const lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Compiler.LCNF.casesStringToMono"};
static const lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "toByteArray"};
static const lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(162, 189, 23, 98, 222, 233, 190, 57)}};
static const lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Compiler.LCNF.casesFloatArrayToMono"};
static const lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(159, 8, 149, 159, 140, 65, 145, 29)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(81, 91, 150, 235, 33, 239, 26, 16)}};
static const lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Compiler.LCNF.casesByteArrayToMono"};
static const lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(16, 14, 5, 86, 33, 2, 113, 205)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(106, 177, 159, 83, 171, 235, 26, 160)}};
static const lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Compiler.LCNF.casesArrayToMono"};
static const lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toList"};
static const lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(236, 208, 194, 233, 254, 64, 157, 114)}};
static const lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Compiler.LCNF.casesUIntToMono"};
static const lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2;
static const lean_string_object l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toBitVec"};
static const lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natZero"};
static const lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(64, 77, 91, 107, 150, 196, 51, 157)}};
static const lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "intZero"};
static const lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(175, 223, 173, 123, 47, 34, 50, 67)}};
static const lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6;
static const lean_string_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__8_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(192, 66, 133, 102, 95, 170, 134, 92)}};
static const lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__8_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "isNeg"};
static const lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(104, 77, 119, 5, 20, 206, 20, 211)}};
static const lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__10_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7;
static const lean_string_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "decLt"};
static const lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(168, 105, 33, 134, 172, 206, 181, 195)}};
static const lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "negSucc"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 236, 205, 0, 179, 53, 99, 201)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natAbs"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 186, 174, 182, 213, 167, 94, 168)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__9_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__10_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "abs"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__4_value),LEAN_SCALAR_PTR_LITERAL(11, 180, 28, 55, 197, 20, 206, 35)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "one"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__3_value),LEAN_SCALAR_PTR_LITERAL(167, 166, 239, 19, 130, 98, 40, 185)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sub"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__5_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__7_value),LEAN_SCALAR_PTR_LITERAL(9, 137, 41, 185, 216, 152, 145, 196)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__6_value),LEAN_SCALAR_PTR_LITERAL(147, 155, 141, 233, 87, 0, 52, 207)}};
static const lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isZero"};
static const lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(65, 194, 46, 57, 180, 54, 219, 130)}};
static const lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__4_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "decEq"};
static const lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__5_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__9_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(13, 188, 70, 193, 211, 173, 121, 176)}};
static const lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__9_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Code_toMono___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_toMono___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_toMono___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_toMono___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_toMono___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_toMono___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toMono"};
static const lean_object* l_Lean_Compiler_LCNF_toMono___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_toMono___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_toMono___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_toMono___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 72, 84, 185, 246, 162, 165, 228)}};
static const lean_object* l_Lean_Compiler_LCNF_toMono___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_toMono___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_toMono___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_toMono___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_toMono___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_toMono___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_toMono___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_toMono = (const lean_object*)&l_Lean_Compiler_LCNF_toMono___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_toMono___closed__1_value),LEAN_SCALAR_PTR_LITERAL(209, 219, 170, 209, 222, 12, 94, 82)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ToMono"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(206, 213, 106, 42, 86, 241, 124, 56)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(247, 243, 51, 59, 0, 163, 178, 192)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(138, 36, 50, 250, 127, 60, 38, 40)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(88, 144, 253, 182, 89, 128, 119, 217)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 161, 241, 253, 80, 60, 193, 46)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(104, 59, 249, 219, 158, 31, 128, 205)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 27, 53, 217, 235, 25, 86, 66)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(252, 41, 14, 40, 231, 191, 209, 206)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 25, 250, 149, 42, 149, 98, 101)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 16, 206, 127, 24, 211, 135, 93)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 134, 59, 125, 71, 39, 210, 179)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1770774466) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(203, 42, 10, 85, 186, 109, 216, 155)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(48, 197, 191, 160, 255, 168, 81, 88)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 210, 128, 230, 105, 208, 140, 127)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(141, 169, 189, 240, 156, 89, 230, 119)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
return v_x_1_;
}
else
{
lean_object* v_key_3_; lean_object* v_value_4_; lean_object* v_tail_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_28_; 
v_key_3_ = lean_ctor_get(v_x_2_, 0);
v_value_4_ = lean_ctor_get(v_x_2_, 1);
v_tail_5_ = lean_ctor_get(v_x_2_, 2);
v_isSharedCheck_28_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_28_ == 0)
{
v___x_7_ = v_x_2_;
v_isShared_8_ = v_isSharedCheck_28_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_tail_5_);
lean_inc(v_value_4_);
lean_inc(v_key_3_);
lean_dec(v_x_2_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_28_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; uint64_t v___x_10_; uint64_t v___x_11_; uint64_t v___x_12_; uint64_t v_fold_13_; uint64_t v___x_14_; uint64_t v___x_15_; uint64_t v___x_16_; size_t v___x_17_; size_t v___x_18_; size_t v___x_19_; size_t v___x_20_; size_t v___x_21_; lean_object* v___x_22_; lean_object* v___x_24_; 
v___x_9_ = lean_array_get_size(v_x_1_);
v___x_10_ = l_Lean_instHashableFVarId_hash(v_key_3_);
v___x_11_ = 32ULL;
v___x_12_ = lean_uint64_shift_right(v___x_10_, v___x_11_);
v_fold_13_ = lean_uint64_xor(v___x_10_, v___x_12_);
v___x_14_ = 16ULL;
v___x_15_ = lean_uint64_shift_right(v_fold_13_, v___x_14_);
v___x_16_ = lean_uint64_xor(v_fold_13_, v___x_15_);
v___x_17_ = lean_uint64_to_usize(v___x_16_);
v___x_18_ = lean_usize_of_nat(v___x_9_);
v___x_19_ = ((size_t)1ULL);
v___x_20_ = lean_usize_sub(v___x_18_, v___x_19_);
v___x_21_ = lean_usize_land(v___x_17_, v___x_20_);
v___x_22_ = lean_array_uget_borrowed(v_x_1_, v___x_21_);
lean_inc(v___x_22_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 2, v___x_22_);
v___x_24_ = v___x_7_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_key_3_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v_value_4_);
lean_ctor_set(v_reuseFailAlloc_27_, 2, v___x_22_);
v___x_24_ = v_reuseFailAlloc_27_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
lean_object* v___x_25_; 
v___x_25_ = lean_array_uset(v_x_1_, v___x_21_, v___x_24_);
v_x_1_ = v___x_25_;
v_x_2_ = v_tail_5_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2___redArg(lean_object* v_i_29_, lean_object* v_source_30_, lean_object* v_target_31_){
_start:
{
lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_32_ = lean_array_get_size(v_source_30_);
v___x_33_ = lean_nat_dec_lt(v_i_29_, v___x_32_);
if (v___x_33_ == 0)
{
lean_dec_ref(v_source_30_);
lean_dec(v_i_29_);
return v_target_31_;
}
else
{
lean_object* v_es_34_; lean_object* v___x_35_; lean_object* v_source_36_; lean_object* v_target_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v_es_34_ = lean_array_fget(v_source_30_, v_i_29_);
v___x_35_ = lean_box(0);
v_source_36_ = lean_array_fset(v_source_30_, v_i_29_, v___x_35_);
v_target_37_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2_spec__3___redArg(v_target_31_, v_es_34_);
v___x_38_ = lean_unsigned_to_nat(1u);
v___x_39_ = lean_nat_add(v_i_29_, v___x_38_);
lean_dec(v_i_29_);
v_i_29_ = v___x_39_;
v_source_30_ = v_source_36_;
v_target_31_ = v_target_37_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1___redArg(lean_object* v_data_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_nbuckets_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_42_ = lean_array_get_size(v_data_41_);
v___x_43_ = lean_unsigned_to_nat(2u);
v_nbuckets_44_ = lean_nat_mul(v___x_42_, v___x_43_);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_box(0);
v___x_47_ = lean_mk_array(v_nbuckets_44_, v___x_46_);
v___x_48_ = lean_array_propagate_mark(v_data_41_, v___x_47_);
v___x_49_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2___redArg(v___x_45_, v_data_41_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(lean_object* v_a_50_, lean_object* v_x_51_){
_start:
{
if (lean_obj_tag(v_x_51_) == 0)
{
uint8_t v___x_52_; 
v___x_52_ = 0;
return v___x_52_;
}
else
{
lean_object* v_key_53_; lean_object* v_tail_54_; uint8_t v___x_55_; 
v_key_53_ = lean_ctor_get(v_x_51_, 0);
v_tail_54_ = lean_ctor_get(v_x_51_, 2);
v___x_55_ = l_Lean_instBEqFVarId_beq(v_key_53_, v_a_50_);
if (v___x_55_ == 0)
{
v_x_51_ = v_tail_54_;
goto _start;
}
else
{
return v___x_55_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg___boxed(lean_object* v_a_57_, lean_object* v_x_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(v_a_57_, v_x_58_);
lean_dec(v_x_58_);
lean_dec(v_a_57_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg(lean_object* v_m_61_, lean_object* v_a_62_, lean_object* v_b_63_){
_start:
{
lean_object* v_size_64_; lean_object* v_buckets_65_; lean_object* v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; uint64_t v___x_69_; uint64_t v_fold_70_; uint64_t v___x_71_; uint64_t v___x_72_; uint64_t v___x_73_; size_t v___x_74_; size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; size_t v___x_78_; lean_object* v_bkt_79_; uint8_t v___x_80_; 
v_size_64_ = lean_ctor_get(v_m_61_, 0);
v_buckets_65_ = lean_ctor_get(v_m_61_, 1);
v___x_66_ = lean_array_get_size(v_buckets_65_);
v___x_67_ = l_Lean_instHashableFVarId_hash(v_a_62_);
v___x_68_ = 32ULL;
v___x_69_ = lean_uint64_shift_right(v___x_67_, v___x_68_);
v_fold_70_ = lean_uint64_xor(v___x_67_, v___x_69_);
v___x_71_ = 16ULL;
v___x_72_ = lean_uint64_shift_right(v_fold_70_, v___x_71_);
v___x_73_ = lean_uint64_xor(v_fold_70_, v___x_72_);
v___x_74_ = lean_uint64_to_usize(v___x_73_);
v___x_75_ = lean_usize_of_nat(v___x_66_);
v___x_76_ = ((size_t)1ULL);
v___x_77_ = lean_usize_sub(v___x_75_, v___x_76_);
v___x_78_ = lean_usize_land(v___x_74_, v___x_77_);
v_bkt_79_ = lean_array_uget_borrowed(v_buckets_65_, v___x_78_);
v___x_80_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(v_a_62_, v_bkt_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_101_; 
lean_inc_ref(v_buckets_65_);
lean_inc(v_size_64_);
v_isSharedCheck_101_ = !lean_is_exclusive(v_m_61_);
if (v_isSharedCheck_101_ == 0)
{
lean_object* v_unused_102_; lean_object* v_unused_103_; 
v_unused_102_ = lean_ctor_get(v_m_61_, 1);
lean_dec(v_unused_102_);
v_unused_103_ = lean_ctor_get(v_m_61_, 0);
lean_dec(v_unused_103_);
v___x_82_ = v_m_61_;
v_isShared_83_ = v_isSharedCheck_101_;
goto v_resetjp_81_;
}
else
{
lean_dec(v_m_61_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_101_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; lean_object* v_size_x27_85_; lean_object* v___x_86_; lean_object* v_buckets_x27_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_84_ = lean_unsigned_to_nat(1u);
v_size_x27_85_ = lean_nat_add(v_size_64_, v___x_84_);
lean_dec(v_size_64_);
lean_inc(v_bkt_79_);
v___x_86_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_86_, 0, v_a_62_);
lean_ctor_set(v___x_86_, 1, v_b_63_);
lean_ctor_set(v___x_86_, 2, v_bkt_79_);
v_buckets_x27_87_ = lean_array_uset(v_buckets_65_, v___x_78_, v___x_86_);
v___x_88_ = lean_unsigned_to_nat(4u);
v___x_89_ = lean_nat_mul(v_size_x27_85_, v___x_88_);
v___x_90_ = lean_unsigned_to_nat(3u);
v___x_91_ = lean_nat_div(v___x_89_, v___x_90_);
lean_dec(v___x_89_);
v___x_92_ = lean_array_get_size(v_buckets_x27_87_);
v___x_93_ = lean_nat_dec_le(v___x_91_, v___x_92_);
lean_dec(v___x_91_);
if (v___x_93_ == 0)
{
lean_object* v_val_94_; lean_object* v___x_96_; 
v_val_94_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1___redArg(v_buckets_x27_87_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 1, v_val_94_);
lean_ctor_set(v___x_82_, 0, v_size_x27_85_);
v___x_96_ = v___x_82_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_size_x27_85_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_val_94_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
else
{
lean_object* v___x_99_; 
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 1, v_buckets_x27_87_);
lean_ctor_set(v___x_82_, 0, v_size_x27_85_);
v___x_99_ = v___x_82_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_size_x27_85_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_buckets_x27_87_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
else
{
lean_dec(v_b_63_);
lean_dec(v_a_62_);
return v_m_61_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___redArg(lean_object* v_param_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_fvarId_110_; lean_object* v_type_111_; lean_object* v___y_113_; lean_object* v___y_114_; lean_object* v___y_115_; uint8_t v___x_128_; 
v_fvarId_110_ = lean_ctor_get(v_param_104_, 0);
v_type_111_ = lean_ctor_get(v_param_104_, 2);
lean_inc_ref(v_type_111_);
v___x_128_ = l_Lean_Compiler_LCNF_isTypeFormerType(v_type_111_);
if (v___x_128_ == 0)
{
v___y_113_ = v_a_106_;
v___y_114_ = v_a_107_;
v___y_115_ = v_a_108_;
goto v___jp_112_;
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_129_ = lean_st_ref_take(v_a_105_);
v___x_130_ = lean_box(0);
lean_inc(v_fvarId_110_);
v___x_131_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg(v___x_129_, v_fvarId_110_, v___x_130_);
v___x_132_ = lean_st_ref_put(v_a_105_, v___x_131_);
v___y_113_ = v_a_106_;
v___y_114_ = v_a_107_;
v___y_115_ = v_a_108_;
goto v___jp_112_;
}
v___jp_112_:
{
lean_object* v___x_116_; 
lean_inc_ref(v_type_111_);
v___x_116_ = l_Lean_Compiler_LCNF_toMonoType(v_type_111_, v___y_114_, v___y_115_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; uint8_t v___x_118_; lean_object* v___x_119_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref_known(v___x_116_, 1);
v___x_118_ = 0;
v___x_119_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v___x_118_, v_param_104_, v_a_117_, v___y_113_);
return v___x_119_;
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
lean_dec_ref(v_param_104_);
v_a_120_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_116_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_116_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___redArg___boxed(lean_object* v_param_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Compiler_LCNF_Param_toMono___redArg(v_param_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
lean_dec(v_a_135_);
lean_dec(v_a_134_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono(lean_object* v_param_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Compiler_LCNF_Param_toMono___redArg(v_param_140_, v_a_141_, v_a_143_, v_a_144_, v_a_145_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___boxed(lean_object* v_param_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Compiler_LCNF_Param_toMono(v_param_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0(lean_object* v_00_u03b2_156_, lean_object* v_m_157_, lean_object* v_a_158_, lean_object* v_b_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg(v_m_157_, v_a_158_, v_b_159_);
return v___x_160_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0(lean_object* v_00_u03b2_161_, lean_object* v_a_162_, lean_object* v_x_163_){
_start:
{
uint8_t v___x_164_; 
v___x_164_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(v_a_162_, v_x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___boxed(lean_object* v_00_u03b2_165_, lean_object* v_a_166_, lean_object* v_x_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0(v_00_u03b2_165_, v_a_166_, v_x_167_);
lean_dec(v_x_167_);
lean_dec(v_a_166_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1(lean_object* v_00_u03b2_170_, lean_object* v_data_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1___redArg(v_data_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_173_, lean_object* v_i_174_, lean_object* v_source_175_, lean_object* v_target_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2___redArg(v_i_174_, v_source_175_, v_target_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_178_, lean_object* v_x_179_, lean_object* v_x_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2_spec__3___redArg(v_x_179_, v_x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___redArg(lean_object* v_arg_184_, lean_object* v_a_185_){
_start:
{
if (lean_obj_tag(v_arg_184_) == 1)
{
lean_object* v_fvarId_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v_fvarId_187_ = lean_ctor_get(v_arg_184_, 0);
v___x_188_ = lean_st_ref_get(v_a_185_);
v___x_189_ = ((lean_object*)(l_Lean_Compiler_LCNF_argToMono___redArg___closed__0));
v___x_190_ = ((lean_object*)(l_Lean_Compiler_LCNF_argToMono___redArg___closed__1));
lean_inc(v_fvarId_187_);
v___x_191_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_189_, v___x_190_, v___x_188_, v_fvarId_187_);
lean_dec(v___x_188_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; 
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v_arg_184_);
return v___x_192_;
}
else
{
lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_200_; 
v_isSharedCheck_200_ = !lean_is_exclusive(v_arg_184_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; 
v_unused_201_ = lean_ctor_get(v_arg_184_, 0);
lean_dec(v_unused_201_);
v___x_194_ = v_arg_184_;
v_isShared_195_ = v_isSharedCheck_200_;
goto v_resetjp_193_;
}
else
{
lean_dec(v_arg_184_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_200_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_196_ = lean_box(0);
if (v_isShared_195_ == 0)
{
lean_ctor_set_tag(v___x_194_, 0);
lean_ctor_set(v___x_194_, 0, v___x_196_);
v___x_198_ = v___x_194_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_196_);
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
else
{
lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec(v_arg_184_);
v___x_202_ = lean_box(0);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___redArg___boxed(lean_object* v_arg_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Compiler_LCNF_argToMono___redArg(v_arg_204_, v_a_205_);
lean_dec(v_a_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono(lean_object* v_arg_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
if (lean_obj_tag(v_arg_208_) == 1)
{
lean_object* v_fvarId_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v_fvarId_215_ = lean_ctor_get(v_arg_208_, 0);
v___x_216_ = lean_st_ref_get(v_a_209_);
v___x_217_ = ((lean_object*)(l_Lean_Compiler_LCNF_argToMono___redArg___closed__0));
v___x_218_ = ((lean_object*)(l_Lean_Compiler_LCNF_argToMono___redArg___closed__1));
lean_inc(v_fvarId_215_);
v___x_219_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_217_, v___x_218_, v___x_216_, v_fvarId_215_);
lean_dec(v___x_216_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; 
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v_arg_208_);
return v___x_220_;
}
else
{
lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_228_; 
v_isSharedCheck_228_ = !lean_is_exclusive(v_arg_208_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; 
v_unused_229_ = lean_ctor_get(v_arg_208_, 0);
lean_dec(v_unused_229_);
v___x_222_ = v_arg_208_;
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
else
{
lean_dec(v_arg_208_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_224_ = lean_box(0);
if (v_isShared_223_ == 0)
{
lean_ctor_set_tag(v___x_222_, 0);
lean_ctor_set(v___x_222_, 0, v___x_224_);
v___x_226_ = v___x_222_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
else
{
lean_object* v___x_230_; lean_object* v___x_231_; 
lean_dec(v_arg_208_);
v___x_230_ = lean_box(0);
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___boxed(lean_object* v_arg_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Compiler_LCNF_argToMono(v_arg_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
lean_dec(v_a_233_);
return v_res_239_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(lean_object* v_m_240_, lean_object* v_a_241_){
_start:
{
lean_object* v_buckets_242_; lean_object* v___x_243_; uint64_t v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; uint64_t v_fold_247_; uint64_t v___x_248_; uint64_t v___x_249_; uint64_t v___x_250_; size_t v___x_251_; size_t v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v_buckets_242_ = lean_ctor_get(v_m_240_, 1);
v___x_243_ = lean_array_get_size(v_buckets_242_);
v___x_244_ = l_Lean_instHashableFVarId_hash(v_a_241_);
v___x_245_ = 32ULL;
v___x_246_ = lean_uint64_shift_right(v___x_244_, v___x_245_);
v_fold_247_ = lean_uint64_xor(v___x_244_, v___x_246_);
v___x_248_ = 16ULL;
v___x_249_ = lean_uint64_shift_right(v_fold_247_, v___x_248_);
v___x_250_ = lean_uint64_xor(v_fold_247_, v___x_249_);
v___x_251_ = lean_uint64_to_usize(v___x_250_);
v___x_252_ = lean_usize_of_nat(v___x_243_);
v___x_253_ = ((size_t)1ULL);
v___x_254_ = lean_usize_sub(v___x_252_, v___x_253_);
v___x_255_ = lean_usize_land(v___x_251_, v___x_254_);
v___x_256_ = lean_array_uget_borrowed(v_buckets_242_, v___x_255_);
v___x_257_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(v_a_241_, v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg___boxed(lean_object* v_m_258_, lean_object* v_a_259_){
_start:
{
uint8_t v_res_260_; lean_object* v_r_261_; 
v_res_260_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v_m_258_, v_a_259_);
lean_dec(v_a_259_);
lean_dec_ref(v_m_258_);
v_r_261_ = lean_box(v_res_260_);
return v_r_261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg(lean_object* v_as_262_, size_t v_sz_263_, size_t v_i_264_, lean_object* v_b_265_, lean_object* v___y_266_){
_start:
{
uint8_t v___x_268_; 
v___x_268_ = lean_usize_dec_lt(v_i_264_, v_sz_263_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v_b_265_);
return v___x_269_;
}
else
{
lean_object* v_fst_270_; lean_object* v_snd_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_311_; 
v_fst_270_ = lean_ctor_get(v_b_265_, 0);
v_snd_271_ = lean_ctor_get(v_b_265_, 1);
v_isSharedCheck_311_ = !lean_is_exclusive(v_b_265_);
if (v_isSharedCheck_311_ == 0)
{
v___x_273_ = v_b_265_;
v_isShared_274_ = v_isSharedCheck_311_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_snd_271_);
lean_inc(v_fst_270_);
lean_dec(v_b_265_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_311_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v_monoArg_276_; lean_object* v_remainingType_277_; lean_object* v_a_285_; lean_object* v___y_287_; 
v_a_285_ = lean_array_uget_borrowed(v_as_262_, v_i_264_);
if (lean_obj_tag(v_fst_270_) == 1)
{
lean_object* v_val_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_310_; 
v_val_294_ = lean_ctor_get(v_fst_270_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v_fst_270_);
if (v_isSharedCheck_310_ == 0)
{
v___x_296_ = v_fst_270_;
v_isShared_297_ = v_isSharedCheck_310_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_val_294_);
lean_dec(v_fst_270_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_310_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
if (lean_obj_tag(v_val_294_) == 7)
{
lean_object* v_binderType_298_; lean_object* v_body_299_; lean_object* v___x_301_; 
v_binderType_298_ = lean_ctor_get(v_val_294_, 1);
lean_inc_ref(v_binderType_298_);
v_body_299_ = lean_ctor_get(v_val_294_, 2);
lean_inc_ref(v_body_299_);
lean_dec_ref_known(v_val_294_, 3);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v_body_299_);
v___x_301_ = v___x_296_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_body_299_);
v___x_301_ = v_reuseFailAlloc_309_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
uint8_t v___x_302_; 
v___x_302_ = l_Lean_Expr_isErased(v_binderType_298_);
lean_dec_ref(v_binderType_298_);
if (v___x_302_ == 0)
{
if (lean_obj_tag(v_a_285_) == 1)
{
lean_object* v_fvarId_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v_fvarId_303_ = lean_ctor_get(v_a_285_, 0);
v___x_304_ = lean_st_ref_get(v___y_266_);
v___x_305_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_304_, v_fvarId_303_);
lean_dec(v___x_304_);
if (v___x_305_ == 0)
{
lean_inc_ref(v_a_285_);
v_monoArg_276_ = v_a_285_;
v_remainingType_277_ = v___x_301_;
goto v___jp_275_;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = lean_box(0);
v_monoArg_276_ = v___x_306_;
v_remainingType_277_ = v___x_301_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_307_; 
v___x_307_ = lean_box(0);
v_monoArg_276_ = v___x_307_;
v_remainingType_277_ = v___x_301_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_308_; 
v___x_308_ = lean_box(0);
v_monoArg_276_ = v___x_308_;
v_remainingType_277_ = v___x_301_;
goto v___jp_275_;
}
}
}
else
{
lean_del_object(v___x_296_);
lean_dec(v_val_294_);
v___y_287_ = v___y_266_;
goto v___jp_286_;
}
}
}
else
{
lean_dec(v_fst_270_);
v___y_287_ = v___y_266_;
goto v___jp_286_;
}
v___jp_275_:
{
lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_278_ = lean_array_push(v_snd_271_, v_monoArg_276_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 1, v___x_278_);
lean_ctor_set(v___x_273_, 0, v_remainingType_277_);
v___x_280_ = v___x_273_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_remainingType_277_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v___x_278_);
v___x_280_ = v_reuseFailAlloc_284_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
size_t v___x_281_; size_t v___x_282_; 
v___x_281_ = ((size_t)1ULL);
v___x_282_ = lean_usize_add(v_i_264_, v___x_281_);
v_i_264_ = v___x_282_;
v_b_265_ = v___x_280_;
goto _start;
}
}
v___jp_286_:
{
lean_object* v___x_288_; 
v___x_288_ = lean_box(0);
if (lean_obj_tag(v_a_285_) == 1)
{
lean_object* v_fvarId_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_fvarId_289_ = lean_ctor_get(v_a_285_, 0);
v___x_290_ = lean_st_ref_get(v___y_287_);
v___x_291_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_290_, v_fvarId_289_);
lean_dec(v___x_290_);
if (v___x_291_ == 0)
{
lean_inc_ref(v_a_285_);
v_monoArg_276_ = v_a_285_;
v_remainingType_277_ = v___x_288_;
goto v___jp_275_;
}
else
{
lean_object* v___x_292_; 
v___x_292_ = lean_box(0);
v_monoArg_276_ = v___x_292_;
v_remainingType_277_ = v___x_288_;
goto v___jp_275_;
}
}
else
{
lean_object* v___x_293_; 
v___x_293_ = lean_box(0);
v_monoArg_276_ = v___x_293_;
v_remainingType_277_ = v___x_288_;
goto v___jp_275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg___boxed(lean_object* v_as_312_, lean_object* v_sz_313_, lean_object* v_i_314_, lean_object* v_b_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
size_t v_sz_boxed_318_; size_t v_i_boxed_319_; lean_object* v_res_320_; 
v_sz_boxed_318_ = lean_unbox_usize(v_sz_313_);
lean_dec(v_sz_313_);
v_i_boxed_319_ = lean_unbox_usize(v_i_314_);
lean_dec(v_i_314_);
v_res_320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg(v_as_312_, v_sz_boxed_318_, v_i_boxed_319_, v_b_315_, v___y_316_);
lean_dec(v___y_316_);
lean_dec_ref(v_as_312_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argsToMonoWithFnType(lean_object* v_args_321_, lean_object* v_type_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_remainingType_329_; lean_object* v___x_330_; lean_object* v_result_331_; lean_object* v___x_332_; size_t v_sz_333_; size_t v___x_334_; lean_object* v___x_335_; 
v_remainingType_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_remainingType_329_, 0, v_type_322_);
v___x_330_ = lean_array_get_size(v_args_321_);
v_result_331_ = lean_mk_empty_array_with_capacity(v___x_330_);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v_remainingType_329_);
lean_ctor_set(v___x_332_, 1, v_result_331_);
v_sz_333_ = lean_array_size(v_args_321_);
v___x_334_ = ((size_t)0ULL);
v___x_335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg(v_args_321_, v_sz_333_, v___x_334_, v___x_332_, v_a_323_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_344_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_344_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_344_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_344_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v_snd_340_; lean_object* v___x_342_; 
v_snd_340_ = lean_ctor_get(v_a_336_, 1);
lean_inc(v_snd_340_);
lean_dec(v_a_336_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v_snd_340_);
v___x_342_ = v___x_338_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_snd_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
v_a_345_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_335_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_335_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argsToMonoWithFnType___boxed(lean_object* v_args_353_, lean_object* v_type_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Compiler_LCNF_argsToMonoWithFnType(v_args_353_, v_type_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_args_353_);
return v_res_361_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0(lean_object* v_00_u03b2_362_, lean_object* v_m_363_, lean_object* v_a_364_){
_start:
{
uint8_t v___x_365_; 
v___x_365_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v_m_363_, v_a_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___boxed(lean_object* v_00_u03b2_366_, lean_object* v_m_367_, lean_object* v_a_368_){
_start:
{
uint8_t v_res_369_; lean_object* v_r_370_; 
v_res_369_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0(v_00_u03b2_366_, v_m_367_, v_a_368_);
lean_dec(v_a_368_);
lean_dec_ref(v_m_367_);
v_r_370_ = lean_box(v_res_369_);
return v_r_370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1(lean_object* v_as_371_, size_t v_sz_372_, size_t v_i_373_, lean_object* v_b_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg(v_as_371_, v_sz_372_, v_i_373_, v_b_374_, v___y_375_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___boxed(lean_object* v_as_382_, lean_object* v_sz_383_, lean_object* v_i_384_, lean_object* v_b_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
size_t v_sz_boxed_392_; size_t v_i_boxed_393_; lean_object* v_res_394_; 
v_sz_boxed_392_ = lean_unbox_usize(v_sz_383_);
lean_dec(v_sz_383_);
v_i_boxed_393_ = lean_unbox_usize(v_i_384_);
lean_dec(v_i_384_);
v_res_394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1(v_as_382_, v_sz_boxed_392_, v_i_boxed_393_, v_b_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v_as_382_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(lean_object* v_a_395_, lean_object* v_b_396_){
_start:
{
lean_object* v_array_397_; lean_object* v_start_398_; lean_object* v_stop_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_412_; 
v_array_397_ = lean_ctor_get(v_a_395_, 0);
v_start_398_ = lean_ctor_get(v_a_395_, 1);
v_stop_399_ = lean_ctor_get(v_a_395_, 2);
v_isSharedCheck_412_ = !lean_is_exclusive(v_a_395_);
if (v_isSharedCheck_412_ == 0)
{
v___x_401_ = v_a_395_;
v_isShared_402_ = v_isSharedCheck_412_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_stop_399_);
lean_inc(v_start_398_);
lean_inc(v_array_397_);
lean_dec(v_a_395_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_412_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
uint8_t v___x_403_; 
v___x_403_ = lean_nat_dec_lt(v_start_398_, v_stop_399_);
if (v___x_403_ == 0)
{
lean_del_object(v___x_401_);
lean_dec(v_stop_399_);
lean_dec(v_start_398_);
lean_dec_ref(v_array_397_);
return v_b_396_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_404_ = lean_unsigned_to_nat(1u);
v___x_405_ = lean_nat_add(v_start_398_, v___x_404_);
lean_inc_ref(v_array_397_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 1, v___x_405_);
v___x_407_ = v___x_401_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_array_397_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_stop_399_);
v___x_407_ = v_reuseFailAlloc_411_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_array_fget(v_array_397_, v_start_398_);
lean_dec(v_start_398_);
lean_dec_ref(v_array_397_);
v___x_409_ = lean_array_push(v_b_396_, v___x_408_);
v_a_395_ = v___x_407_;
v_b_396_ = v___x_409_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(size_t v_sz_413_, size_t v_i_414_, lean_object* v_bs_415_, lean_object* v___y_416_){
_start:
{
uint8_t v___x_418_; 
v___x_418_ = lean_usize_dec_lt(v_i_414_, v_sz_413_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v_bs_415_);
return v___x_419_;
}
else
{
lean_object* v_v_420_; lean_object* v___x_421_; lean_object* v_bs_x27_422_; lean_object* v_a_424_; 
v_v_420_ = lean_array_uget(v_bs_415_, v_i_414_);
v___x_421_ = lean_unsigned_to_nat(0u);
v_bs_x27_422_ = lean_array_uset(v_bs_415_, v_i_414_, v___x_421_);
if (lean_obj_tag(v_v_420_) == 1)
{
lean_object* v_fvarId_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v_fvarId_429_ = lean_ctor_get(v_v_420_, 0);
v___x_430_ = lean_st_ref_get(v___y_416_);
v___x_431_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_430_, v_fvarId_429_);
lean_dec(v___x_430_);
if (v___x_431_ == 0)
{
v_a_424_ = v_v_420_;
goto v___jp_423_;
}
else
{
lean_object* v___x_432_; 
lean_dec_ref_known(v_v_420_, 1);
v___x_432_ = lean_box(0);
v_a_424_ = v___x_432_;
goto v___jp_423_;
}
}
else
{
lean_object* v___x_433_; 
lean_dec(v_v_420_);
v___x_433_ = lean_box(0);
v_a_424_ = v___x_433_;
goto v___jp_423_;
}
v___jp_423_:
{
size_t v___x_425_; size_t v___x_426_; lean_object* v___x_427_; 
v___x_425_ = ((size_t)1ULL);
v___x_426_ = lean_usize_add(v_i_414_, v___x_425_);
v___x_427_ = lean_array_uset(v_bs_x27_422_, v_i_414_, v_a_424_);
v_i_414_ = v___x_426_;
v_bs_415_ = v___x_427_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg___boxed(lean_object* v_sz_434_, lean_object* v_i_435_, lean_object* v_bs_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
size_t v_sz_boxed_439_; size_t v_i_boxed_440_; lean_object* v_res_441_; 
v_sz_boxed_439_ = lean_unbox_usize(v_sz_434_);
lean_dec(v_sz_434_);
v_i_boxed_440_ = lean_unbox_usize(v_i_435_);
lean_dec(v_i_435_);
v_res_441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_boxed_439_, v_i_boxed_440_, v_bs_436_, v___y_437_);
lean_dec(v___y_437_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ctorAppToMono(lean_object* v_ctorInfo_444_, lean_object* v_args_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_toConstantVal_452_; lean_object* v_numParams_453_; lean_object* v___x_454_; lean_object* v_argsNewParams_455_; lean_object* v_lower_457_; lean_object* v_upper_458_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v_toConstantVal_452_ = lean_ctor_get(v_ctorInfo_444_, 0);
lean_inc_ref(v_toConstantVal_452_);
v_numParams_453_ = lean_ctor_get(v_ctorInfo_444_, 3);
lean_inc_n(v_numParams_453_, 2);
lean_dec_ref(v_ctorInfo_444_);
v___x_454_ = lean_box(0);
v_argsNewParams_455_ = lean_mk_array(v_numParams_453_, v___x_454_);
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = lean_array_get_size(v_args_445_);
v___x_495_ = lean_nat_dec_le(v_numParams_453_, v___x_493_);
if (v___x_495_ == 0)
{
v_lower_457_ = v_numParams_453_;
v_upper_458_ = v___x_494_;
goto v___jp_456_;
}
else
{
lean_dec(v_numParams_453_);
v_lower_457_ = v___x_493_;
v_upper_458_ = v___x_494_;
goto v___jp_456_;
}
v___jp_456_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; size_t v_sz_462_; size_t v___x_463_; lean_object* v___x_464_; 
v___x_459_ = l_Array_toSubarray___redArg(v_args_445_, v_lower_457_, v_upper_458_);
v___x_460_ = ((lean_object*)(l_Lean_Compiler_LCNF_ctorAppToMono___closed__0));
v___x_461_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(v___x_459_, v___x_460_);
v_sz_462_ = lean_array_size(v___x_461_);
v___x_463_ = ((size_t)0ULL);
v___x_464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_462_, v___x_463_, v___x_461_, v_a_446_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_484_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_484_ == 0)
{
v___x_467_ = v___x_464_;
v_isShared_468_ = v_isSharedCheck_484_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_484_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v_name_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_481_; 
v_name_469_ = lean_ctor_get(v_toConstantVal_452_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v_toConstantVal_452_);
if (v_isSharedCheck_481_ == 0)
{
lean_object* v_unused_482_; lean_object* v_unused_483_; 
v_unused_482_ = lean_ctor_get(v_toConstantVal_452_, 2);
lean_dec(v_unused_482_);
v_unused_483_ = lean_ctor_get(v_toConstantVal_452_, 1);
lean_dec(v_unused_483_);
v___x_471_ = v_toConstantVal_452_;
v_isShared_472_ = v_isSharedCheck_481_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_name_469_);
lean_dec(v_toConstantVal_452_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_481_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_473_ = l_Array_append___redArg(v_argsNewParams_455_, v_a_465_);
lean_dec(v_a_465_);
v___x_474_ = lean_box(0);
if (v_isShared_472_ == 0)
{
lean_ctor_set_tag(v___x_471_, 3);
lean_ctor_set(v___x_471_, 2, v___x_473_);
lean_ctor_set(v___x_471_, 1, v___x_474_);
v___x_476_ = v___x_471_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_name_469_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v___x_473_);
v___x_476_ = v_reuseFailAlloc_480_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_478_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_476_);
v___x_478_ = v___x_467_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec_ref(v_argsNewParams_455_);
lean_dec_ref(v_toConstantVal_452_);
v_a_485_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_464_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_464_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ctorAppToMono___boxed(lean_object* v_ctorInfo_496_, lean_object* v_args_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Compiler_LCNF_ctorAppToMono(v_ctorInfo_496_, v_args_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0(lean_object* v_inst_505_, lean_object* v_R_506_, lean_object* v_a_507_, lean_object* v_b_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(v_a_507_, v_b_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1(size_t v_sz_510_, size_t v_i_511_, lean_object* v_bs_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_510_, v_i_511_, v_bs_512_, v___y_513_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___boxed(lean_object* v_sz_520_, lean_object* v_i_521_, lean_object* v_bs_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
size_t v_sz_boxed_529_; size_t v_i_boxed_530_; lean_object* v_res_531_; 
v_sz_boxed_529_ = lean_unbox_usize(v_sz_520_);
lean_dec(v_sz_520_);
v_i_boxed_530_ = lean_unbox_usize(v_i_521_);
lean_dec(v_i_521_);
v_res_531_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1(v_sz_boxed_529_, v_i_boxed_530_, v_bs_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
return v_res_531_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0(void){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_instMonadEIO(lean_box(0));
return v___x_532_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5(void){
_start:
{
uint8_t v___x_537_; lean_object* v___x_538_; 
v___x_537_ = 0;
v___x_538_ = l_Lean_Compiler_LCNF_instInhabitedLetValue_default(v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(lean_object* v_msg_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v_toApplicative_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_610_; 
v___x_546_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_547_ = l_StateRefT_x27_instMonad___redArg(v___x_546_);
v_toApplicative_548_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v___x_547_, 1);
lean_dec(v_unused_611_);
v___x_550_ = v___x_547_;
v_isShared_551_ = v_isSharedCheck_610_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_toApplicative_548_);
lean_dec(v___x_547_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_610_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v_toFunctor_552_; lean_object* v_toSeq_553_; lean_object* v_toSeqLeft_554_; lean_object* v_toSeqRight_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_608_; 
v_toFunctor_552_ = lean_ctor_get(v_toApplicative_548_, 0);
v_toSeq_553_ = lean_ctor_get(v_toApplicative_548_, 2);
v_toSeqLeft_554_ = lean_ctor_get(v_toApplicative_548_, 3);
v_toSeqRight_555_ = lean_ctor_get(v_toApplicative_548_, 4);
v_isSharedCheck_608_ = !lean_is_exclusive(v_toApplicative_548_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; 
v_unused_609_ = lean_ctor_get(v_toApplicative_548_, 1);
lean_dec(v_unused_609_);
v___x_557_ = v_toApplicative_548_;
v_isShared_558_ = v_isSharedCheck_608_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_toSeqRight_555_);
lean_inc(v_toSeqLeft_554_);
lean_inc(v_toSeq_553_);
lean_inc(v_toFunctor_552_);
lean_dec(v_toApplicative_548_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_608_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___f_559_; lean_object* v___f_560_; lean_object* v___f_561_; lean_object* v___f_562_; lean_object* v___x_563_; lean_object* v___f_564_; lean_object* v___f_565_; lean_object* v___f_566_; lean_object* v___x_568_; 
v___f_559_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_560_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_552_);
v___f_561_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_561_, 0, v_toFunctor_552_);
v___f_562_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_562_, 0, v_toFunctor_552_);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v___f_561_);
lean_ctor_set(v___x_563_, 1, v___f_562_);
v___f_564_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_564_, 0, v_toSeqRight_555_);
v___f_565_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_565_, 0, v_toSeqLeft_554_);
v___f_566_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_566_, 0, v_toSeq_553_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 4, v___f_564_);
lean_ctor_set(v___x_557_, 3, v___f_565_);
lean_ctor_set(v___x_557_, 2, v___f_566_);
lean_ctor_set(v___x_557_, 1, v___f_559_);
lean_ctor_set(v___x_557_, 0, v___x_563_);
v___x_568_ = v___x_557_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v___f_559_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v___f_566_);
lean_ctor_set(v_reuseFailAlloc_607_, 3, v___f_565_);
lean_ctor_set(v_reuseFailAlloc_607_, 4, v___f_564_);
v___x_568_ = v_reuseFailAlloc_607_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_570_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v___f_560_);
lean_ctor_set(v___x_550_, 0, v___x_568_);
v___x_570_ = v___x_550_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v___f_560_);
v___x_570_ = v_reuseFailAlloc_606_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; lean_object* v_toApplicative_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_604_; 
v___x_571_ = l_StateRefT_x27_instMonad___redArg(v___x_570_);
v_toApplicative_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_604_ == 0)
{
lean_object* v_unused_605_; 
v_unused_605_ = lean_ctor_get(v___x_571_, 1);
lean_dec(v_unused_605_);
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_604_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_toApplicative_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_604_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v_toFunctor_576_; lean_object* v_toSeq_577_; lean_object* v_toSeqLeft_578_; lean_object* v_toSeqRight_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_602_; 
v_toFunctor_576_ = lean_ctor_get(v_toApplicative_572_, 0);
v_toSeq_577_ = lean_ctor_get(v_toApplicative_572_, 2);
v_toSeqLeft_578_ = lean_ctor_get(v_toApplicative_572_, 3);
v_toSeqRight_579_ = lean_ctor_get(v_toApplicative_572_, 4);
v_isSharedCheck_602_ = !lean_is_exclusive(v_toApplicative_572_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v_toApplicative_572_, 1);
lean_dec(v_unused_603_);
v___x_581_ = v_toApplicative_572_;
v_isShared_582_ = v_isSharedCheck_602_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_toSeqRight_579_);
lean_inc(v_toSeqLeft_578_);
lean_inc(v_toSeq_577_);
lean_inc(v_toFunctor_576_);
lean_dec(v_toApplicative_572_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_602_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___f_583_; lean_object* v___f_584_; lean_object* v___f_585_; lean_object* v___f_586_; lean_object* v___x_587_; lean_object* v___f_588_; lean_object* v___f_589_; lean_object* v___f_590_; lean_object* v___x_592_; 
v___f_583_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_584_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_576_);
v___f_585_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_585_, 0, v_toFunctor_576_);
v___f_586_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_586_, 0, v_toFunctor_576_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v___f_585_);
lean_ctor_set(v___x_587_, 1, v___f_586_);
v___f_588_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_588_, 0, v_toSeqRight_579_);
v___f_589_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_589_, 0, v_toSeqLeft_578_);
v___f_590_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_590_, 0, v_toSeq_577_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 4, v___f_588_);
lean_ctor_set(v___x_581_, 3, v___f_589_);
lean_ctor_set(v___x_581_, 2, v___f_590_);
lean_ctor_set(v___x_581_, 1, v___f_583_);
lean_ctor_set(v___x_581_, 0, v___x_587_);
v___x_592_ = v___x_581_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v___f_583_);
lean_ctor_set(v_reuseFailAlloc_601_, 2, v___f_590_);
lean_ctor_set(v_reuseFailAlloc_601_, 3, v___f_589_);
lean_ctor_set(v_reuseFailAlloc_601_, 4, v___f_588_);
v___x_592_ = v_reuseFailAlloc_601_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_594_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 1, v___f_584_);
lean_ctor_set(v___x_574_, 0, v___x_592_);
v___x_594_ = v___x_574_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v___f_584_);
v___x_594_ = v_reuseFailAlloc_600_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_6495__overap_598_; lean_object* v___x_599_; 
v___x_595_ = l_StateRefT_x27_instMonad___redArg(v___x_594_);
v___x_596_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5);
v___x_597_ = l_instInhabitedOfMonad___redArg(v___x_595_, v___x_596_);
v___x_6495__overap_598_ = lean_panic_fn_borrowed(v___x_597_, v_msg_539_);
lean_dec(v___x_597_);
lean_inc(v___y_544_);
lean_inc_ref(v___y_543_);
lean_inc(v___y_542_);
lean_inc_ref(v___y_541_);
lean_inc(v___y_540_);
v___x_599_ = lean_apply_6(v___x_6495__overap_598_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, lean_box(0));
return v___x_599_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___boxed(lean_object* v_msg_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(v_msg_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(lean_object* v_upperBound_620_, lean_object* v_args_621_, lean_object* v_a_622_, lean_object* v_b_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_a_627_; uint8_t v___x_632_; 
v___x_632_ = lean_nat_dec_lt(v_a_622_, v_upperBound_620_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
lean_dec(v_a_622_);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v_b_623_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_box(0);
v___x_635_ = lean_array_get_borrowed(v___x_634_, v_args_621_, v_a_622_);
if (lean_obj_tag(v___x_635_) == 1)
{
lean_object* v_fvarId_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_fvarId_636_ = lean_ctor_get(v___x_635_, 0);
v___x_637_ = lean_st_ref_get(v___y_624_);
v___x_638_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_637_, v_fvarId_636_);
lean_dec(v___x_637_);
if (v___x_638_ == 0)
{
lean_inc_ref(v___x_635_);
v_a_627_ = v___x_635_;
goto v___jp_626_;
}
else
{
v_a_627_ = v___x_634_;
goto v___jp_626_;
}
}
else
{
v_a_627_ = v___x_634_;
goto v___jp_626_;
}
}
v___jp_626_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = lean_array_push(v_b_623_, v_a_627_);
v___x_629_ = lean_unsigned_to_nat(1u);
v___x_630_ = lean_nat_add(v_a_622_, v___x_629_);
lean_dec(v_a_622_);
v_a_622_ = v___x_630_;
v_b_623_ = v___x_628_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg___boxed(lean_object* v_upperBound_639_, lean_object* v_args_640_, lean_object* v_a_641_, lean_object* v_b_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v_upperBound_639_, v_args_640_, v_a_641_, v_b_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v_args_640_);
lean_dec(v_upperBound_639_);
return v_res_645_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LetValue_toMono___closed__13(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_667_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_668_ = lean_unsigned_to_nat(6u);
v___x_669_ = lean_unsigned_to_nat(83u);
v___x_670_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__11));
v___x_671_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_672_ = l_mkPanicMessageWithDecl(v___x_671_, v___x_670_, v___x_669_, v___x_668_, v___x_667_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono(lean_object* v_e_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
switch(lean_obj_tag(v_e_677_))
{
case 2:
{
lean_object* v_typeName_684_; lean_object* v_idx_685_; lean_object* v_struct_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v_typeName_684_ = lean_ctor_get(v_e_677_, 0);
v_idx_685_ = lean_ctor_get(v_e_677_, 1);
v_struct_686_ = lean_ctor_get(v_e_677_, 2);
v___x_687_ = lean_st_ref_get(v_a_678_);
v___x_688_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_687_, v_struct_686_);
lean_dec(v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; 
lean_inc(v_typeName_684_);
v___x_689_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_typeName_684_, v_a_681_, v_a_682_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_709_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_709_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_709_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_709_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
if (lean_obj_tag(v_a_690_) == 1)
{
lean_object* v_val_694_; lean_object* v_fieldIdx_695_; uint8_t v___x_696_; 
lean_inc(v_struct_686_);
lean_inc(v_idx_685_);
lean_dec_ref_known(v_e_677_, 3);
v_val_694_ = lean_ctor_get(v_a_690_, 0);
lean_inc(v_val_694_);
lean_dec_ref_known(v_a_690_, 1);
v_fieldIdx_695_ = lean_ctor_get(v_val_694_, 2);
lean_inc(v_fieldIdx_695_);
lean_dec(v_val_694_);
v___x_696_ = lean_nat_dec_eq(v_fieldIdx_695_, v_idx_685_);
lean_dec(v_idx_685_);
lean_dec(v_fieldIdx_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_699_; 
lean_dec(v_struct_686_);
v___x_697_ = lean_box(1);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_697_);
v___x_699_ = v___x_692_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_701_ = ((lean_object*)(l_Lean_Compiler_LCNF_ctorAppToMono___closed__0));
v___x_702_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_702_, 0, v_struct_686_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_702_);
v___x_704_ = v___x_692_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
else
{
lean_object* v___x_707_; 
lean_dec(v_a_690_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v_e_677_);
v___x_707_ = v___x_692_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_e_677_);
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
lean_dec_ref_known(v_e_677_, 3);
v_a_710_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_689_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_689_);
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
lean_object* v___x_718_; lean_object* v___x_719_; 
lean_dec_ref_known(v_e_677_, 3);
v___x_718_ = lean_box(1);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
}
case 3:
{
lean_object* v_declName_720_; lean_object* v_args_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_843_; 
v_declName_720_ = lean_ctor_get(v_e_677_, 0);
v_args_721_ = lean_ctor_get(v_e_677_, 2);
v_isSharedCheck_843_ = !lean_is_exclusive(v_e_677_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; 
v_unused_844_ = lean_ctor_get(v_e_677_, 1);
lean_dec(v_unused_844_);
v___x_723_ = v_e_677_;
v_isShared_724_ = v_isSharedCheck_843_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_args_721_);
lean_inc(v_declName_720_);
lean_dec(v_e_677_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_843_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v_args_726_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_773_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__2));
v___x_774_ = lean_name_eq(v_declName_720_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__4));
v___x_776_ = lean_name_eq(v_declName_720_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_777_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__7));
v___x_778_ = lean_name_eq(v_declName_720_, v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_779_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__9));
v___x_780_ = lean_name_eq(v_declName_720_, v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; lean_object* v_env_782_; lean_object* v___x_783_; 
v___x_781_ = lean_st_ref_get(v_a_682_);
v_env_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc_ref(v_env_782_);
lean_dec(v___x_781_);
lean_inc(v_declName_720_);
v___x_783_ = l_Lean_Environment_find_x3f(v_env_782_, v_declName_720_, v___x_780_);
if (lean_obj_tag(v___x_783_) == 1)
{
lean_object* v_val_784_; 
v_val_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_val_784_);
lean_dec_ref_known(v___x_783_, 1);
if (lean_obj_tag(v_val_784_) == 6)
{
lean_object* v_val_785_; lean_object* v_induct_786_; lean_object* v_numParams_787_; lean_object* v___x_788_; 
lean_del_object(v___x_723_);
lean_dec(v_declName_720_);
v_val_785_ = lean_ctor_get(v_val_784_, 0);
lean_inc_ref(v_val_785_);
lean_dec_ref_known(v_val_784_, 1);
v_induct_786_ = lean_ctor_get(v_val_785_, 1);
v_numParams_787_ = lean_ctor_get(v_val_785_, 3);
lean_inc(v_induct_786_);
v___x_788_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_induct_786_, v_a_681_, v_a_682_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
if (lean_obj_tag(v_a_789_) == 1)
{
lean_object* v_val_790_; lean_object* v_fieldIdx_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_inc(v_numParams_787_);
lean_dec_ref(v_val_785_);
v_val_790_ = lean_ctor_get(v_a_789_, 0);
lean_inc(v_val_790_);
lean_dec_ref_known(v_a_789_, 1);
v_fieldIdx_791_ = lean_ctor_get(v_val_790_, 2);
lean_inc(v_fieldIdx_791_);
lean_dec(v_val_790_);
v___x_792_ = lean_box(0);
v___x_793_ = lean_nat_add(v_numParams_787_, v_fieldIdx_791_);
lean_dec(v_fieldIdx_791_);
lean_dec(v_numParams_787_);
v___x_794_ = lean_array_get(v___x_792_, v_args_721_, v___x_793_);
lean_dec(v___x_793_);
lean_dec_ref(v_args_721_);
v___x_795_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_794_);
lean_dec(v___x_794_);
v_e_677_ = v___x_795_;
goto _start;
}
else
{
lean_object* v___x_797_; 
lean_dec(v_a_789_);
v___x_797_ = l_Lean_Compiler_LCNF_ctorAppToMono(v_val_785_, v_args_721_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
return v___x_797_;
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec_ref(v_val_785_);
lean_dec_ref(v_args_721_);
v_a_798_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_788_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_788_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
else
{
lean_dec(v_val_784_);
v___y_733_ = v_a_678_;
v___y_734_ = v_a_679_;
v___y_735_ = v_a_680_;
v___y_736_ = v_a_681_;
v___y_737_ = v_a_682_;
goto v___jp_732_;
}
}
else
{
lean_dec(v___x_783_);
v___y_733_ = v_a_678_;
v___y_734_ = v_a_679_;
v___y_735_ = v_a_680_;
v___y_736_ = v_a_681_;
v___y_737_ = v_a_682_;
goto v___jp_732_;
}
}
else
{
lean_object* v___x_806_; lean_object* v___x_807_; 
lean_del_object(v___x_723_);
lean_dec_ref(v_args_721_);
lean_dec(v_declName_720_);
v___x_806_ = lean_obj_once(&l_Lean_Compiler_LCNF_LetValue_toMono___closed__13, &l_Lean_Compiler_LCNF_LetValue_toMono___closed__13_once, _init_l_Lean_Compiler_LCNF_LetValue_toMono___closed__13);
v___x_807_ = l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(v___x_806_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
return v___x_807_;
}
}
else
{
lean_object* v___x_808_; lean_object* v___x_809_; 
lean_del_object(v___x_723_);
lean_dec_ref(v_args_721_);
lean_dec(v_declName_720_);
v___x_808_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__15));
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
return v___x_809_;
}
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
lean_del_object(v___x_723_);
lean_dec(v_declName_720_);
v___x_810_ = lean_box(0);
v___x_811_ = lean_unsigned_to_nat(2u);
v___x_812_ = lean_array_get_borrowed(v___x_810_, v_args_721_, v___x_811_);
if (lean_obj_tag(v___x_812_) == 1)
{
lean_object* v_fvarId_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v_extraArgs_817_; lean_object* v___x_818_; 
v_fvarId_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_fvarId_813_);
v___x_814_ = lean_array_get_size(v_args_721_);
v___x_815_ = lean_unsigned_to_nat(3u);
v___x_816_ = lean_nat_sub(v___x_814_, v___x_815_);
v_extraArgs_817_ = lean_mk_empty_array_with_capacity(v___x_816_);
lean_dec(v___x_816_);
v___x_818_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v___x_814_, v_args_721_, v___x_815_, v_extraArgs_817_, v_a_678_);
lean_dec_ref(v_args_721_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_827_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_827_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_823_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_823_, 0, v_fvarId_813_);
lean_ctor_set(v___x_823_, 1, v_a_819_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_823_);
v___x_825_ = v___x_821_;
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
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_dec(v_fvarId_813_);
v_a_828_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_818_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_818_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec_ref(v_args_721_);
v___x_836_ = lean_box(1);
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
return v___x_837_;
}
}
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
lean_del_object(v___x_723_);
lean_dec(v_declName_720_);
v___x_838_ = lean_box(0);
v___x_839_ = lean_unsigned_to_nat(2u);
v___x_840_ = lean_array_get(v___x_838_, v_args_721_, v___x_839_);
lean_dec_ref(v_args_721_);
v___x_841_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_840_);
lean_dec(v___x_840_);
v___x_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
return v___x_842_;
}
v___jp_725_:
{
lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_727_ = lean_box(0);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 2, v_args_726_);
lean_ctor_set(v___x_723_, 1, v___x_727_);
v___x_729_ = v___x_723_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_declName_720_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_731_, 2, v_args_726_);
v___x_729_ = v_reuseFailAlloc_731_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_730_; 
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
}
v___jp_732_:
{
lean_object* v___x_738_; 
lean_inc(v_declName_720_);
v___x_738_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_720_, v___y_737_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
if (lean_obj_tag(v_a_739_) == 1)
{
lean_object* v_val_740_; lean_object* v_toSignature_741_; lean_object* v_type_742_; lean_object* v___x_743_; 
v_val_740_ = lean_ctor_get(v_a_739_, 0);
lean_inc(v_val_740_);
lean_dec_ref_known(v_a_739_, 1);
v_toSignature_741_ = lean_ctor_get(v_val_740_, 0);
lean_inc_ref(v_toSignature_741_);
lean_dec(v_val_740_);
v_type_742_ = lean_ctor_get(v_toSignature_741_, 2);
lean_inc_ref(v_type_742_);
lean_dec_ref(v_toSignature_741_);
v___x_743_ = l_Lean_Compiler_LCNF_argsToMonoWithFnType(v_args_721_, v_type_742_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec_ref(v_args_721_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref_known(v___x_743_, 1);
v_args_726_ = v_a_744_;
goto v___jp_725_;
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_del_object(v___x_723_);
lean_dec(v_declName_720_);
v_a_745_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_743_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_743_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
else
{
size_t v_sz_753_; size_t v___x_754_; lean_object* v___x_755_; 
lean_dec(v_a_739_);
v_sz_753_ = lean_array_size(v_args_721_);
v___x_754_ = ((size_t)0ULL);
v___x_755_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_753_, v___x_754_, v_args_721_, v___y_733_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_755_, 1);
v_args_726_ = v_a_756_;
goto v___jp_725_;
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_del_object(v___x_723_);
lean_dec(v_declName_720_);
v_a_757_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_755_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_755_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_del_object(v___x_723_);
lean_dec_ref(v_args_721_);
lean_dec(v_declName_720_);
v_a_765_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_738_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_738_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
}
case 4:
{
lean_object* v_fvarId_845_; lean_object* v_args_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_876_; 
v_fvarId_845_ = lean_ctor_get(v_e_677_, 0);
v_args_846_ = lean_ctor_get(v_e_677_, 1);
v_isSharedCheck_876_ = !lean_is_exclusive(v_e_677_);
if (v_isSharedCheck_876_ == 0)
{
v___x_848_ = v_e_677_;
v_isShared_849_ = v_isSharedCheck_876_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_args_846_);
lean_inc(v_fvarId_845_);
lean_dec(v_e_677_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_876_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_850_ = lean_st_ref_get(v_a_678_);
v___x_851_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_850_, v_fvarId_845_);
lean_dec(v___x_850_);
if (v___x_851_ == 0)
{
size_t v_sz_852_; size_t v___x_853_; lean_object* v___x_854_; 
v_sz_852_ = lean_array_size(v_args_846_);
v___x_853_ = ((size_t)0ULL);
v___x_854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_852_, v___x_853_, v_args_846_, v_a_678_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_865_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_865_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_865_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_865_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 1, v_a_855_);
v___x_860_ = v___x_848_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_fvarId_845_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_a_855_);
v___x_860_ = v_reuseFailAlloc_864_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_862_; 
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_860_);
v___x_862_ = v___x_857_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_del_object(v___x_848_);
lean_dec(v_fvarId_845_);
v_a_866_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_854_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_854_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
else
{
lean_object* v___x_874_; lean_object* v___x_875_; 
lean_del_object(v___x_848_);
lean_dec_ref(v_args_846_);
lean_dec(v_fvarId_845_);
v___x_874_ = lean_box(1);
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
}
}
}
default: 
{
lean_object* v___x_877_; 
v___x_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_877_, 0, v_e_677_);
return v___x_877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___boxed(lean_object* v_e_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_Compiler_LCNF_LetValue_toMono(v_e_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1(lean_object* v_upperBound_886_, lean_object* v_args_887_, lean_object* v_inst_888_, lean_object* v_R_889_, lean_object* v_a_890_, lean_object* v_b_891_, lean_object* v_c_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v_upperBound_886_, v_args_887_, v_a_890_, v_b_891_, v___y_893_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___boxed(lean_object* v_upperBound_900_, lean_object* v_args_901_, lean_object* v_inst_902_, lean_object* v_R_903_, lean_object* v_a_904_, lean_object* v_b_905_, lean_object* v_c_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1(v_upperBound_900_, v_args_901_, v_inst_902_, v_R_903_, v_a_904_, v_b_905_, v_c_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v_args_901_);
lean_dec(v_upperBound_900_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono(lean_object* v_decl_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_type_921_; lean_object* v_value_922_; lean_object* v___x_923_; 
v_type_921_ = lean_ctor_get(v_decl_914_, 2);
v_value_922_ = lean_ctor_get(v_decl_914_, 3);
lean_inc_ref(v_type_921_);
v___x_923_ = l_Lean_Compiler_LCNF_toMonoType(v_type_921_, v_a_918_, v_a_919_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_925_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
lean_dec_ref_known(v___x_923_, 1);
lean_inc(v_value_922_);
v___x_925_ = l_Lean_Compiler_LCNF_LetValue_toMono(v_value_922_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; uint8_t v___x_927_; lean_object* v___x_928_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
lean_dec_ref_known(v___x_925_, 1);
v___x_927_ = 0;
v___x_928_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_927_, v_decl_914_, v_a_924_, v_a_926_, v_a_917_);
return v___x_928_;
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_dec(v_a_924_);
lean_dec_ref(v_decl_914_);
v_a_929_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_925_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_925_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v_decl_914_);
v_a_937_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_923_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_923_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono___boxed(lean_object* v_decl_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_Compiler_LCNF_LetDecl_toMono(v_decl_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(lean_object* v_msg_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v_toApplicative_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_1024_; 
v___x_960_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_961_ = l_StateRefT_x27_instMonad___redArg(v___x_960_);
v_toApplicative_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; 
v_unused_1025_ = lean_ctor_get(v___x_961_, 1);
lean_dec(v_unused_1025_);
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_1024_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_toApplicative_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_1024_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v_toFunctor_966_; lean_object* v_toSeq_967_; lean_object* v_toSeqLeft_968_; lean_object* v_toSeqRight_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_1022_; 
v_toFunctor_966_ = lean_ctor_get(v_toApplicative_962_, 0);
v_toSeq_967_ = lean_ctor_get(v_toApplicative_962_, 2);
v_toSeqLeft_968_ = lean_ctor_get(v_toApplicative_962_, 3);
v_toSeqRight_969_ = lean_ctor_get(v_toApplicative_962_, 4);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_toApplicative_962_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; 
v_unused_1023_ = lean_ctor_get(v_toApplicative_962_, 1);
lean_dec(v_unused_1023_);
v___x_971_ = v_toApplicative_962_;
v_isShared_972_ = v_isSharedCheck_1022_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_toSeqRight_969_);
lean_inc(v_toSeqLeft_968_);
lean_inc(v_toSeq_967_);
lean_inc(v_toFunctor_966_);
lean_dec(v_toApplicative_962_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_1022_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___f_973_; lean_object* v___f_974_; lean_object* v___f_975_; lean_object* v___f_976_; lean_object* v___x_977_; lean_object* v___f_978_; lean_object* v___f_979_; lean_object* v___f_980_; lean_object* v___x_982_; 
v___f_973_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_974_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_966_);
v___f_975_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_975_, 0, v_toFunctor_966_);
v___f_976_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_976_, 0, v_toFunctor_966_);
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v___f_975_);
lean_ctor_set(v___x_977_, 1, v___f_976_);
v___f_978_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_978_, 0, v_toSeqRight_969_);
v___f_979_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_979_, 0, v_toSeqLeft_968_);
v___f_980_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_980_, 0, v_toSeq_967_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 4, v___f_978_);
lean_ctor_set(v___x_971_, 3, v___f_979_);
lean_ctor_set(v___x_971_, 2, v___f_980_);
lean_ctor_set(v___x_971_, 1, v___f_973_);
lean_ctor_set(v___x_971_, 0, v___x_977_);
v___x_982_ = v___x_971_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v___f_973_);
lean_ctor_set(v_reuseFailAlloc_1021_, 2, v___f_980_);
lean_ctor_set(v_reuseFailAlloc_1021_, 3, v___f_979_);
lean_ctor_set(v_reuseFailAlloc_1021_, 4, v___f_978_);
v___x_982_ = v_reuseFailAlloc_1021_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_984_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v___f_974_);
lean_ctor_set(v___x_964_, 0, v___x_982_);
v___x_984_ = v___x_964_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v___f_974_);
v___x_984_ = v_reuseFailAlloc_1020_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_985_; lean_object* v_toApplicative_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1018_; 
v___x_985_ = l_StateRefT_x27_instMonad___redArg(v___x_984_);
v_toApplicative_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; 
v_unused_1019_ = lean_ctor_get(v___x_985_, 1);
lean_dec(v_unused_1019_);
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_1018_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_toApplicative_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1018_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v_toFunctor_990_; lean_object* v_toSeq_991_; lean_object* v_toSeqLeft_992_; lean_object* v_toSeqRight_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1016_; 
v_toFunctor_990_ = lean_ctor_get(v_toApplicative_986_, 0);
v_toSeq_991_ = lean_ctor_get(v_toApplicative_986_, 2);
v_toSeqLeft_992_ = lean_ctor_get(v_toApplicative_986_, 3);
v_toSeqRight_993_ = lean_ctor_get(v_toApplicative_986_, 4);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_toApplicative_986_);
if (v_isSharedCheck_1016_ == 0)
{
lean_object* v_unused_1017_; 
v_unused_1017_ = lean_ctor_get(v_toApplicative_986_, 1);
lean_dec(v_unused_1017_);
v___x_995_ = v_toApplicative_986_;
v_isShared_996_ = v_isSharedCheck_1016_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_toSeqRight_993_);
lean_inc(v_toSeqLeft_992_);
lean_inc(v_toSeq_991_);
lean_inc(v_toFunctor_990_);
lean_dec(v_toApplicative_986_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1016_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___f_997_; lean_object* v___f_998_; lean_object* v___f_999_; lean_object* v___f_1000_; lean_object* v___x_1001_; lean_object* v___f_1002_; lean_object* v___f_1003_; lean_object* v___f_1004_; lean_object* v___x_1006_; 
v___f_997_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_998_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_990_);
v___f_999_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_999_, 0, v_toFunctor_990_);
v___f_1000_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1000_, 0, v_toFunctor_990_);
v___x_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___f_999_);
lean_ctor_set(v___x_1001_, 1, v___f_1000_);
v___f_1002_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1002_, 0, v_toSeqRight_993_);
v___f_1003_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1003_, 0, v_toSeqLeft_992_);
v___f_1004_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1004_, 0, v_toSeq_991_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 4, v___f_1002_);
lean_ctor_set(v___x_995_, 3, v___f_1003_);
lean_ctor_set(v___x_995_, 2, v___f_1004_);
lean_ctor_set(v___x_995_, 1, v___f_997_);
lean_ctor_set(v___x_995_, 0, v___x_1001_);
v___x_1006_ = v___x_995_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v___f_997_);
lean_ctor_set(v_reuseFailAlloc_1015_, 2, v___f_1004_);
lean_ctor_set(v_reuseFailAlloc_1015_, 3, v___f_1003_);
lean_ctor_set(v_reuseFailAlloc_1015_, 4, v___f_1002_);
v___x_1006_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1008_; 
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 1, v___f_998_);
lean_ctor_set(v___x_988_, 0, v___x_1006_);
v___x_1008_ = v___x_988_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v___f_998_);
v___x_1008_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_4525__overap_1012_; lean_object* v___x_1013_; 
v___x_1009_ = l_StateRefT_x27_instMonad___redArg(v___x_1008_);
v___x_1010_ = lean_box(0);
v___x_1011_ = l_instInhabitedOfMonad___redArg(v___x_1009_, v___x_1010_);
v___x_4525__overap_1012_ = lean_panic_fn_borrowed(v___x_1011_, v_msg_953_);
lean_dec(v___x_1011_);
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
lean_inc(v___y_956_);
lean_inc_ref(v___y_955_);
lean_inc(v___y_954_);
v___x_1013_ = lean_apply_6(v___x_4525__overap_1012_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, lean_box(0));
return v___x_1013_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0___boxed(lean_object* v_msg_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v_msg_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
return v_res_1033_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1035_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1036_ = lean_unsigned_to_nat(11u);
v___x_1037_ = lean_unsigned_to_nat(124u);
v___x_1038_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__0));
v___x_1039_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1040_ = l_mkPanicMessageWithDecl(v___x_1039_, v___x_1038_, v___x_1037_, v___x_1036_, v___x_1035_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(lean_object* v_upperBound_1041_, lean_object* v_a_1042_, lean_object* v_b_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_a_1051_; uint8_t v___x_1055_; 
v___x_1055_ = lean_nat_dec_lt(v_a_1042_, v_upperBound_1041_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; 
lean_dec(v_a_1042_);
v___x_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1056_, 0, v_b_1043_);
return v___x_1056_;
}
else
{
if (lean_obj_tag(v_b_1043_) == 7)
{
lean_object* v_body_1057_; 
v_body_1057_ = lean_ctor_get(v_b_1043_, 2);
lean_inc_ref(v_body_1057_);
lean_dec_ref_known(v_b_1043_, 3);
v_a_1051_ = v_body_1057_;
goto v___jp_1050_;
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1);
v___x_1059_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v___x_1058_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_dec_ref_known(v___x_1059_, 1);
v_a_1051_ = v_b_1043_;
goto v___jp_1050_;
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec_ref(v_b_1043_);
lean_dec(v_a_1042_);
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1059_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
v___jp_1050_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_unsigned_to_nat(1u);
v___x_1053_ = lean_nat_add(v_a_1042_, v___x_1052_);
lean_dec(v_a_1042_);
v_a_1042_ = v___x_1053_;
v_b_1043_ = v_a_1051_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___boxed(lean_object* v_upperBound_1068_, lean_object* v_a_1069_, lean_object* v_b_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_upperBound_1068_, v_a_1069_, v_b_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec(v_upperBound_1068_);
return v_res_1077_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1078_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1079_ = lean_unsigned_to_nat(11u);
v___x_1080_ = lean_unsigned_to_nat(132u);
v___x_1081_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__0));
v___x_1082_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1083_ = l_mkPanicMessageWithDecl(v___x_1082_, v___x_1081_, v___x_1080_, v___x_1079_, v___x_1078_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(lean_object* v_upperBound_1084_, lean_object* v_a_1085_, lean_object* v_b_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_a_1094_; uint8_t v___x_1098_; 
v___x_1098_ = lean_nat_dec_lt(v_a_1085_, v_upperBound_1084_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; 
lean_dec(v_a_1085_);
v___x_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1099_, 0, v_b_1086_);
return v___x_1099_;
}
else
{
lean_object* v_fst_1100_; 
v_fst_1100_ = lean_ctor_get(v_b_1086_, 0);
lean_inc(v_fst_1100_);
if (lean_obj_tag(v_fst_1100_) == 7)
{
lean_object* v_snd_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1134_; 
v_snd_1101_ = lean_ctor_get(v_b_1086_, 1);
v_isSharedCheck_1134_ = !lean_is_exclusive(v_b_1086_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; 
v_unused_1135_ = lean_ctor_get(v_b_1086_, 0);
lean_dec(v_unused_1135_);
v___x_1103_ = v_b_1086_;
v_isShared_1104_ = v_isSharedCheck_1134_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_snd_1101_);
lean_dec(v_b_1086_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1134_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v_binderName_1105_; lean_object* v_binderType_1106_; lean_object* v_body_1107_; lean_object* v___x_1108_; 
v_binderName_1105_ = lean_ctor_get(v_fst_1100_, 0);
lean_inc(v_binderName_1105_);
v_binderType_1106_ = lean_ctor_get(v_fst_1100_, 1);
lean_inc_ref(v_binderType_1106_);
v_body_1107_ = lean_ctor_get(v_fst_1100_, 2);
lean_inc_ref(v_body_1107_);
lean_dec_ref_known(v_fst_1100_, 3);
v___x_1108_ = l_Lean_Compiler_LCNF_toMonoType(v_binderType_1106_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; uint8_t v___x_1110_; uint8_t v___x_1111_; lean_object* v___x_1112_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1109_);
lean_dec_ref_known(v___x_1108_, 1);
v___x_1110_ = 0;
v___x_1111_ = 0;
v___x_1112_ = l_Lean_Compiler_LCNF_mkParam(v___x_1110_, v_binderName_1105_, v_a_1109_, v___x_1111_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1114_; lean_object* v___x_1116_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v___x_1112_, 1);
v___x_1114_ = lean_array_push(v_snd_1101_, v_a_1113_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 1, v___x_1114_);
lean_ctor_set(v___x_1103_, 0, v_body_1107_);
v___x_1116_ = v___x_1103_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_body_1107_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
v_a_1094_ = v___x_1116_;
goto v___jp_1093_;
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec_ref(v_body_1107_);
lean_del_object(v___x_1103_);
lean_dec(v_snd_1101_);
lean_dec(v_a_1085_);
v_a_1118_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1112_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1112_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec_ref(v_body_1107_);
lean_dec(v_binderName_1105_);
lean_del_object(v___x_1103_);
lean_dec(v_snd_1101_);
lean_dec(v_a_1085_);
v_a_1126_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1108_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1108_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
else
{
lean_object* v_snd_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1153_; 
v_snd_1136_ = lean_ctor_get(v_b_1086_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_b_1086_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; 
v_unused_1154_ = lean_ctor_get(v_b_1086_, 0);
lean_dec(v_unused_1154_);
v___x_1138_ = v_b_1086_;
v_isShared_1139_ = v_isSharedCheck_1153_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_snd_1136_);
lean_dec(v_b_1086_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1153_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0);
v___x_1141_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v___x_1140_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v___x_1143_; 
lean_dec_ref_known(v___x_1141_, 1);
if (v_isShared_1139_ == 0)
{
v___x_1143_ = v___x_1138_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_fst_1100_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_snd_1136_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
v_a_1094_ = v___x_1143_;
goto v___jp_1093_;
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_del_object(v___x_1138_);
lean_dec(v_snd_1136_);
lean_dec(v_fst_1100_);
lean_dec(v_a_1085_);
v_a_1145_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1141_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1141_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
}
v___jp_1093_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = lean_unsigned_to_nat(1u);
v___x_1096_ = lean_nat_add(v_a_1085_, v___x_1095_);
lean_dec(v_a_1085_);
v_a_1085_ = v___x_1096_;
v_b_1086_ = v_a_1094_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___boxed(lean_object* v_upperBound_1155_, lean_object* v_a_1156_, lean_object* v_b_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_upperBound_1155_, v_a_1156_, v_b_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec(v_upperBound_1155_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(lean_object* v_ctorType_1165_, lean_object* v_numParams_1166_, lean_object* v_numNewFields_1167_, lean_object* v_oldFields_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_numParams_1166_, v___x_1175_, v_ctorType_1165_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v___x_1176_, 1);
v___x_1178_ = lean_array_get_size(v_oldFields_1168_);
v___x_1179_ = lean_nat_add(v___x_1178_, v_numNewFields_1167_);
v___x_1180_ = lean_mk_empty_array_with_capacity(v___x_1179_);
lean_dec(v___x_1179_);
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v_a_1177_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_numNewFields_1167_, v___x_1175_, v___x_1181_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1192_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1192_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1192_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_snd_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
v_snd_1187_ = lean_ctor_get(v_a_1183_, 1);
lean_inc(v_snd_1187_);
lean_dec(v_a_1183_);
v___x_1188_ = l_Array_append___redArg(v_snd_1187_, v_oldFields_1168_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1188_);
v___x_1190_ = v___x_1185_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
v_a_1193_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1182_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1182_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
v_a_1201_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1176_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1176_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields___boxed(lean_object* v_ctorType_1209_, lean_object* v_numParams_1210_, lean_object* v_numNewFields_1211_, lean_object* v_oldFields_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(v_ctorType_1209_, v_numParams_1210_, v_numNewFields_1211_, v_oldFields_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
lean_dec_ref(v_a_1214_);
lean_dec(v_a_1213_);
lean_dec_ref(v_oldFields_1212_);
lean_dec(v_numNewFields_1211_);
lean_dec(v_numParams_1210_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1(lean_object* v_upperBound_1220_, lean_object* v_inst_1221_, lean_object* v_R_1222_, lean_object* v_a_1223_, lean_object* v_b_1224_, lean_object* v_c_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_upperBound_1220_, v_a_1223_, v_b_1224_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___boxed(lean_object* v_upperBound_1233_, lean_object* v_inst_1234_, lean_object* v_R_1235_, lean_object* v_a_1236_, lean_object* v_b_1237_, lean_object* v_c_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1(v_upperBound_1233_, v_inst_1234_, v_R_1235_, v_a_1236_, v_b_1237_, v_c_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec(v_upperBound_1233_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2(lean_object* v_upperBound_1246_, lean_object* v_inst_1247_, lean_object* v_R_1248_, lean_object* v_a_1249_, lean_object* v_b_1250_, lean_object* v_c_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_upperBound_1246_, v_a_1249_, v_b_1250_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___boxed(lean_object* v_upperBound_1259_, lean_object* v_inst_1260_, lean_object* v_R_1261_, lean_object* v_a_1262_, lean_object* v_b_1263_, lean_object* v_c_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2(v_upperBound_1259_, v_inst_1260_, v_R_1261_, v_a_1262_, v_b_1263_, v_c_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec(v_upperBound_1259_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(size_t v_sz_1272_, size_t v_i_1273_, lean_object* v_bs_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
uint8_t v___x_1280_; 
v___x_1280_ = lean_usize_dec_lt(v_i_1273_, v_sz_1272_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; 
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v_bs_1274_);
return v___x_1281_;
}
else
{
lean_object* v_v_1282_; lean_object* v___x_1283_; 
v_v_1282_ = lean_array_uget_borrowed(v_bs_1274_, v_i_1273_);
lean_inc(v_v_1282_);
v___x_1283_ = l_Lean_Compiler_LCNF_Param_toMono___redArg(v_v_1282_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1285_; lean_object* v_bs_x27_1286_; size_t v___x_1287_; size_t v___x_1288_; lean_object* v___x_1289_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1283_, 1);
v___x_1285_ = lean_unsigned_to_nat(0u);
v_bs_x27_1286_ = lean_array_uset(v_bs_1274_, v_i_1273_, v___x_1285_);
v___x_1287_ = ((size_t)1ULL);
v___x_1288_ = lean_usize_add(v_i_1273_, v___x_1287_);
v___x_1289_ = lean_array_uset(v_bs_x27_1286_, v_i_1273_, v_a_1284_);
v_i_1273_ = v___x_1288_;
v_bs_1274_ = v___x_1289_;
goto _start;
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec_ref(v_bs_1274_);
v_a_1291_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1283_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1283_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg___boxed(lean_object* v_sz_1299_, lean_object* v_i_1300_, lean_object* v_bs_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
size_t v_sz_boxed_1307_; size_t v_i_boxed_1308_; lean_object* v_res_1309_; 
v_sz_boxed_1307_ = lean_unbox_usize(v_sz_1299_);
lean_dec(v_sz_1299_);
v_i_boxed_1308_ = lean_unbox_usize(v_i_1300_);
lean_dec(v_i_1300_);
v_res_1309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_boxed_1307_, v_i_boxed_1308_, v_bs_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec(v___y_1302_);
return v_res_1309_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0(void){
_start:
{
uint8_t v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = 0;
v___x_1311_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(lean_object* v_msg_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v_toApplicative_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1383_; 
v___x_1319_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1320_ = l_StateRefT_x27_instMonad___redArg(v___x_1319_);
v_toApplicative_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1383_ == 0)
{
lean_object* v_unused_1384_; 
v_unused_1384_ = lean_ctor_get(v___x_1320_, 1);
lean_dec(v_unused_1384_);
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1383_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_toApplicative_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1383_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v_toFunctor_1325_; lean_object* v_toSeq_1326_; lean_object* v_toSeqLeft_1327_; lean_object* v_toSeqRight_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1381_; 
v_toFunctor_1325_ = lean_ctor_get(v_toApplicative_1321_, 0);
v_toSeq_1326_ = lean_ctor_get(v_toApplicative_1321_, 2);
v_toSeqLeft_1327_ = lean_ctor_get(v_toApplicative_1321_, 3);
v_toSeqRight_1328_ = lean_ctor_get(v_toApplicative_1321_, 4);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_toApplicative_1321_);
if (v_isSharedCheck_1381_ == 0)
{
lean_object* v_unused_1382_; 
v_unused_1382_ = lean_ctor_get(v_toApplicative_1321_, 1);
lean_dec(v_unused_1382_);
v___x_1330_ = v_toApplicative_1321_;
v_isShared_1331_ = v_isSharedCheck_1381_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_toSeqRight_1328_);
lean_inc(v_toSeqLeft_1327_);
lean_inc(v_toSeq_1326_);
lean_inc(v_toFunctor_1325_);
lean_dec(v_toApplicative_1321_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1381_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___f_1332_; lean_object* v___f_1333_; lean_object* v___f_1334_; lean_object* v___f_1335_; lean_object* v___x_1336_; lean_object* v___f_1337_; lean_object* v___f_1338_; lean_object* v___f_1339_; lean_object* v___x_1341_; 
v___f_1332_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1333_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1325_);
v___f_1334_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1334_, 0, v_toFunctor_1325_);
v___f_1335_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1335_, 0, v_toFunctor_1325_);
v___x_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___f_1334_);
lean_ctor_set(v___x_1336_, 1, v___f_1335_);
v___f_1337_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1337_, 0, v_toSeqRight_1328_);
v___f_1338_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1338_, 0, v_toSeqLeft_1327_);
v___f_1339_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1339_, 0, v_toSeq_1326_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 4, v___f_1337_);
lean_ctor_set(v___x_1330_, 3, v___f_1338_);
lean_ctor_set(v___x_1330_, 2, v___f_1339_);
lean_ctor_set(v___x_1330_, 1, v___f_1332_);
lean_ctor_set(v___x_1330_, 0, v___x_1336_);
v___x_1341_ = v___x_1330_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v___f_1332_);
lean_ctor_set(v_reuseFailAlloc_1380_, 2, v___f_1339_);
lean_ctor_set(v_reuseFailAlloc_1380_, 3, v___f_1338_);
lean_ctor_set(v_reuseFailAlloc_1380_, 4, v___f_1337_);
v___x_1341_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1343_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 1, v___f_1333_);
lean_ctor_set(v___x_1323_, 0, v___x_1341_);
v___x_1343_ = v___x_1323_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1341_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v___f_1333_);
v___x_1343_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1344_; lean_object* v_toApplicative_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1377_; 
v___x_1344_ = l_StateRefT_x27_instMonad___redArg(v___x_1343_);
v_toApplicative_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1377_ == 0)
{
lean_object* v_unused_1378_; 
v_unused_1378_ = lean_ctor_get(v___x_1344_, 1);
lean_dec(v_unused_1378_);
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1377_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_toApplicative_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1377_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v_toFunctor_1349_; lean_object* v_toSeq_1350_; lean_object* v_toSeqLeft_1351_; lean_object* v_toSeqRight_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1375_; 
v_toFunctor_1349_ = lean_ctor_get(v_toApplicative_1345_, 0);
v_toSeq_1350_ = lean_ctor_get(v_toApplicative_1345_, 2);
v_toSeqLeft_1351_ = lean_ctor_get(v_toApplicative_1345_, 3);
v_toSeqRight_1352_ = lean_ctor_get(v_toApplicative_1345_, 4);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_toApplicative_1345_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; 
v_unused_1376_ = lean_ctor_get(v_toApplicative_1345_, 1);
lean_dec(v_unused_1376_);
v___x_1354_ = v_toApplicative_1345_;
v_isShared_1355_ = v_isSharedCheck_1375_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_toSeqRight_1352_);
lean_inc(v_toSeqLeft_1351_);
lean_inc(v_toSeq_1350_);
lean_inc(v_toFunctor_1349_);
lean_dec(v_toApplicative_1345_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1375_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___f_1356_; lean_object* v___f_1357_; lean_object* v___f_1358_; lean_object* v___f_1359_; lean_object* v___x_1360_; lean_object* v___f_1361_; lean_object* v___f_1362_; lean_object* v___f_1363_; lean_object* v___x_1365_; 
v___f_1356_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1357_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1349_);
v___f_1358_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1358_, 0, v_toFunctor_1349_);
v___f_1359_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1359_, 0, v_toFunctor_1349_);
v___x_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___f_1358_);
lean_ctor_set(v___x_1360_, 1, v___f_1359_);
v___f_1361_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1361_, 0, v_toSeqRight_1352_);
v___f_1362_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1362_, 0, v_toSeqLeft_1351_);
v___f_1363_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1363_, 0, v_toSeq_1350_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 4, v___f_1361_);
lean_ctor_set(v___x_1354_, 3, v___f_1362_);
lean_ctor_set(v___x_1354_, 2, v___f_1363_);
lean_ctor_set(v___x_1354_, 1, v___f_1356_);
lean_ctor_set(v___x_1354_, 0, v___x_1360_);
v___x_1365_ = v___x_1354_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v___f_1356_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v___f_1363_);
lean_ctor_set(v_reuseFailAlloc_1374_, 3, v___f_1362_);
lean_ctor_set(v_reuseFailAlloc_1374_, 4, v___f_1361_);
v___x_1365_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1367_; 
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 1, v___f_1357_);
lean_ctor_set(v___x_1347_, 0, v___x_1365_);
v___x_1367_ = v___x_1347_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v___f_1357_);
v___x_1367_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_30686__overap_1371_; lean_object* v___x_1372_; 
v___x_1368_ = l_StateRefT_x27_instMonad___redArg(v___x_1367_);
v___x_1369_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0);
v___x_1370_ = l_instInhabitedOfMonad___redArg(v___x_1368_, v___x_1369_);
v___x_30686__overap_1371_ = lean_panic_fn_borrowed(v___x_1370_, v_msg_1312_);
lean_dec(v___x_1370_);
lean_inc(v___y_1317_);
lean_inc_ref(v___y_1316_);
lean_inc(v___y_1315_);
lean_inc_ref(v___y_1314_);
lean_inc(v___y_1313_);
v___x_1372_ = lean_apply_6(v___x_30686__overap_1371_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, lean_box(0));
return v___x_1372_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___boxed(lean_object* v_msg_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v_msg_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__2(lean_object* v_msg_1393_){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0);
v___x_1395_ = lean_panic_fn_borrowed(v___x_1394_, v_msg_1393_);
return v___x_1395_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0(void){
_start:
{
uint8_t v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = 0;
v___x_1397_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(lean_object* v_msg_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v_toApplicative_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1469_; 
v___x_1405_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1406_ = l_StateRefT_x27_instMonad___redArg(v___x_1405_);
v_toApplicative_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; 
v_unused_1470_ = lean_ctor_get(v___x_1406_, 1);
lean_dec(v_unused_1470_);
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1469_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_toApplicative_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1469_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v_toFunctor_1411_; lean_object* v_toSeq_1412_; lean_object* v_toSeqLeft_1413_; lean_object* v_toSeqRight_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1467_; 
v_toFunctor_1411_ = lean_ctor_get(v_toApplicative_1407_, 0);
v_toSeq_1412_ = lean_ctor_get(v_toApplicative_1407_, 2);
v_toSeqLeft_1413_ = lean_ctor_get(v_toApplicative_1407_, 3);
v_toSeqRight_1414_ = lean_ctor_get(v_toApplicative_1407_, 4);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_toApplicative_1407_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; 
v_unused_1468_ = lean_ctor_get(v_toApplicative_1407_, 1);
lean_dec(v_unused_1468_);
v___x_1416_ = v_toApplicative_1407_;
v_isShared_1417_ = v_isSharedCheck_1467_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_toSeqRight_1414_);
lean_inc(v_toSeqLeft_1413_);
lean_inc(v_toSeq_1412_);
lean_inc(v_toFunctor_1411_);
lean_dec(v_toApplicative_1407_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1467_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___f_1418_; lean_object* v___f_1419_; lean_object* v___f_1420_; lean_object* v___f_1421_; lean_object* v___x_1422_; lean_object* v___f_1423_; lean_object* v___f_1424_; lean_object* v___f_1425_; lean_object* v___x_1427_; 
v___f_1418_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1419_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1411_);
v___f_1420_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1420_, 0, v_toFunctor_1411_);
v___f_1421_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1421_, 0, v_toFunctor_1411_);
v___x_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___f_1420_);
lean_ctor_set(v___x_1422_, 1, v___f_1421_);
v___f_1423_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1423_, 0, v_toSeqRight_1414_);
v___f_1424_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1424_, 0, v_toSeqLeft_1413_);
v___f_1425_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1425_, 0, v_toSeq_1412_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 4, v___f_1423_);
lean_ctor_set(v___x_1416_, 3, v___f_1424_);
lean_ctor_set(v___x_1416_, 2, v___f_1425_);
lean_ctor_set(v___x_1416_, 1, v___f_1418_);
lean_ctor_set(v___x_1416_, 0, v___x_1422_);
v___x_1427_ = v___x_1416_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v___f_1418_);
lean_ctor_set(v_reuseFailAlloc_1466_, 2, v___f_1425_);
lean_ctor_set(v_reuseFailAlloc_1466_, 3, v___f_1424_);
lean_ctor_set(v_reuseFailAlloc_1466_, 4, v___f_1423_);
v___x_1427_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1429_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 1, v___f_1419_);
lean_ctor_set(v___x_1409_, 0, v___x_1427_);
v___x_1429_ = v___x_1409_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v___f_1419_);
v___x_1429_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v_toApplicative_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1463_; 
v___x_1430_ = l_StateRefT_x27_instMonad___redArg(v___x_1429_);
v_toApplicative_1431_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v___x_1430_, 1);
lean_dec(v_unused_1464_);
v___x_1433_ = v___x_1430_;
v_isShared_1434_ = v_isSharedCheck_1463_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_toApplicative_1431_);
lean_dec(v___x_1430_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1463_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v_toFunctor_1435_; lean_object* v_toSeq_1436_; lean_object* v_toSeqLeft_1437_; lean_object* v_toSeqRight_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1461_; 
v_toFunctor_1435_ = lean_ctor_get(v_toApplicative_1431_, 0);
v_toSeq_1436_ = lean_ctor_get(v_toApplicative_1431_, 2);
v_toSeqLeft_1437_ = lean_ctor_get(v_toApplicative_1431_, 3);
v_toSeqRight_1438_ = lean_ctor_get(v_toApplicative_1431_, 4);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_toApplicative_1431_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v_toApplicative_1431_, 1);
lean_dec(v_unused_1462_);
v___x_1440_ = v_toApplicative_1431_;
v_isShared_1441_ = v_isSharedCheck_1461_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_toSeqRight_1438_);
lean_inc(v_toSeqLeft_1437_);
lean_inc(v_toSeq_1436_);
lean_inc(v_toFunctor_1435_);
lean_dec(v_toApplicative_1431_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1461_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___f_1442_; lean_object* v___f_1443_; lean_object* v___f_1444_; lean_object* v___f_1445_; lean_object* v___x_1446_; lean_object* v___f_1447_; lean_object* v___f_1448_; lean_object* v___f_1449_; lean_object* v___x_1451_; 
v___f_1442_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1443_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1435_);
v___f_1444_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1444_, 0, v_toFunctor_1435_);
v___f_1445_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1445_, 0, v_toFunctor_1435_);
v___x_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___f_1444_);
lean_ctor_set(v___x_1446_, 1, v___f_1445_);
v___f_1447_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1447_, 0, v_toSeqRight_1438_);
v___f_1448_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1448_, 0, v_toSeqLeft_1437_);
v___f_1449_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1449_, 0, v_toSeq_1436_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 4, v___f_1447_);
lean_ctor_set(v___x_1440_, 3, v___f_1448_);
lean_ctor_set(v___x_1440_, 2, v___f_1449_);
lean_ctor_set(v___x_1440_, 1, v___f_1442_);
lean_ctor_set(v___x_1440_, 0, v___x_1446_);
v___x_1451_ = v___x_1440_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v___f_1442_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v___f_1449_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v___f_1448_);
lean_ctor_set(v_reuseFailAlloc_1460_, 4, v___f_1447_);
v___x_1451_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1453_; 
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 1, v___f_1443_);
lean_ctor_set(v___x_1433_, 0, v___x_1451_);
v___x_1453_ = v___x_1433_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v___f_1443_);
v___x_1453_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_30701__overap_1457_; lean_object* v___x_1458_; 
v___x_1454_ = l_StateRefT_x27_instMonad___redArg(v___x_1453_);
v___x_1455_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_1456_ = l_instInhabitedOfMonad___redArg(v___x_1454_, v___x_1455_);
v___x_30701__overap_1457_ = lean_panic_fn_borrowed(v___x_1456_, v_msg_1398_);
lean_dec(v___x_1456_);
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
lean_inc(v___y_1401_);
lean_inc_ref(v___y_1400_);
lean_inc(v___y_1399_);
v___x_1458_ = lean_apply_6(v___x_30701__overap_1457_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, lean_box(0));
return v___x_1458_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___boxed(lean_object* v_msg_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(v_msg_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
return v_res_1478_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__2(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1481_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1482_ = lean_unsigned_to_nat(9u);
v___x_1483_ = lean_unsigned_to_nat(650u);
v___x_1484_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__1));
v___x_1485_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__0));
v___x_1486_ = l_mkPanicMessageWithDecl(v___x_1485_, v___x_1484_, v___x_1483_, v___x_1482_, v___x_1481_);
return v___x_1486_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__4(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1489_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__3));
v___x_1490_ = lean_unsigned_to_nat(66u);
v___x_1491_ = lean_unsigned_to_nat(363u);
v___x_1492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_1493_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1494_ = l_mkPanicMessageWithDecl(v___x_1493_, v___x_1492_, v___x_1491_, v___x_1490_, v___x_1489_);
return v___x_1494_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__5(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1495_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1496_ = lean_unsigned_to_nat(27u);
v___x_1497_ = lean_unsigned_to_nat(319u);
v___x_1498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_1499_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1500_ = l_mkPanicMessageWithDecl(v___x_1499_, v___x_1498_, v___x_1497_, v___x_1496_, v___x_1495_);
return v___x_1500_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__1(void){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1555_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_1556_ = lean_unsigned_to_nat(2u);
v___x_1557_ = lean_unsigned_to_nat(302u);
v___x_1558_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1559_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1560_ = l_mkPanicMessageWithDecl(v___x_1559_, v___x_1558_, v___x_1557_, v___x_1556_, v___x_1555_);
return v___x_1560_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3(void){
_start:
{
uint8_t v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = 0;
v___x_1562_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_1561_);
return v___x_1562_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__3(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1564_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__2));
v___x_1565_ = lean_unsigned_to_nat(2u);
v___x_1566_ = lean_unsigned_to_nat(304u);
v___x_1567_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1568_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1569_ = l_mkPanicMessageWithDecl(v___x_1568_, v___x_1567_, v___x_1566_, v___x_1565_, v___x_1564_);
return v___x_1569_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__5(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1571_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__4));
v___x_1572_ = lean_unsigned_to_nat(2u);
v___x_1573_ = lean_unsigned_to_nat(305u);
v___x_1574_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1575_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1576_ = l_mkPanicMessageWithDecl(v___x_1575_, v___x_1574_, v___x_1573_, v___x_1572_, v___x_1571_);
return v___x_1576_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__6(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1577_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1578_ = lean_unsigned_to_nat(41u);
v___x_1579_ = lean_unsigned_to_nat(303u);
v___x_1580_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1581_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1582_ = l_mkPanicMessageWithDecl(v___x_1581_, v___x_1580_, v___x_1579_, v___x_1578_, v___x_1577_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono(lean_object* v_info_1583_, lean_object* v_c_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_){
_start:
{
lean_object* v_discr_1591_; lean_object* v_alts_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1670_; 
v_discr_1591_ = lean_ctor_get(v_c_1584_, 2);
v_alts_1592_ = lean_ctor_get(v_c_1584_, 3);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_c_1584_);
if (v_isSharedCheck_1670_ == 0)
{
lean_object* v_unused_1671_; lean_object* v_unused_1672_; 
v_unused_1671_ = lean_ctor_get(v_c_1584_, 1);
lean_dec(v_unused_1671_);
v_unused_1672_ = lean_ctor_get(v_c_1584_, 0);
lean_dec(v_unused_1672_);
v___x_1594_ = v_c_1584_;
v_isShared_1595_ = v_isSharedCheck_1670_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_alts_1592_);
lean_inc(v_discr_1591_);
lean_dec(v_c_1584_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1670_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1596_ = lean_array_get_size(v_alts_1592_);
v___x_1597_ = lean_unsigned_to_nat(1u);
v___x_1598_ = lean_nat_dec_eq(v___x_1596_, v___x_1597_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
lean_del_object(v___x_1594_);
lean_dec_ref(v_alts_1592_);
lean_dec(v_discr_1591_);
v___x_1599_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__1, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__1_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__1);
v___x_1600_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1599_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
return v___x_1600_;
}
else
{
uint8_t v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1601_ = 0;
v___x_1602_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_1603_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_1604_ = lean_unsigned_to_nat(0u);
v___x_1605_ = lean_array_get(v___x_1603_, v_alts_1592_, v___x_1604_);
lean_dec_ref(v_alts_1592_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_ctorName_1606_; lean_object* v_params_1607_; lean_object* v_code_1608_; lean_object* v_ctorName_1609_; lean_object* v_fieldIdx_1610_; uint8_t v___x_1611_; 
v_ctorName_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_ctorName_1606_);
v_params_1607_ = lean_ctor_get(v___x_1605_, 1);
lean_inc_ref(v_params_1607_);
v_code_1608_ = lean_ctor_get(v___x_1605_, 2);
lean_inc_ref(v_code_1608_);
lean_dec_ref_known(v___x_1605_, 3);
v_ctorName_1609_ = lean_ctor_get(v_info_1583_, 0);
v_fieldIdx_1610_ = lean_ctor_get(v_info_1583_, 2);
v___x_1611_ = lean_name_eq(v_ctorName_1606_, v_ctorName_1609_);
lean_dec(v_ctorName_1606_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_dec_ref(v_code_1608_);
lean_dec_ref(v_params_1607_);
lean_del_object(v___x_1594_);
lean_dec(v_discr_1591_);
v___x_1612_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__3, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__3_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__3);
v___x_1613_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1612_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
return v___x_1613_;
}
else
{
lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1614_ = lean_array_get_size(v_params_1607_);
v___x_1615_ = lean_nat_dec_lt(v_fieldIdx_1610_, v___x_1614_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec_ref(v_code_1608_);
lean_dec_ref(v_params_1607_);
lean_del_object(v___x_1594_);
lean_dec(v_discr_1591_);
v___x_1616_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__5, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__5_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__5);
v___x_1617_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1616_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
return v___x_1617_;
}
else
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1601_, v_params_1607_, v_a_1587_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_p_1619_; lean_object* v_fvarId_1620_; lean_object* v_binderName_1621_; lean_object* v_type_1622_; lean_object* v___x_1623_; 
lean_dec_ref_known(v___x_1618_, 1);
v_p_1619_ = lean_array_get(v___x_1602_, v_params_1607_, v_fieldIdx_1610_);
lean_dec_ref(v_params_1607_);
v_fvarId_1620_ = lean_ctor_get(v_p_1619_, 0);
lean_inc(v_fvarId_1620_);
v_binderName_1621_ = lean_ctor_get(v_p_1619_, 1);
lean_inc(v_binderName_1621_);
v_type_1622_ = lean_ctor_get(v_p_1619_, 2);
lean_inc_ref(v_type_1622_);
lean_dec(v_p_1619_);
v___x_1623_ = l_Lean_Compiler_LCNF_toMonoType(v_type_1622_, v_a_1588_, v_a_1589_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1625_; lean_object* v_lctx_1626_; lean_object* v_nextIdx_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1651_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1623_, 1);
v___x_1625_ = lean_st_ref_take(v_a_1587_);
v_lctx_1626_ = lean_ctor_get(v___x_1625_, 0);
v_nextIdx_1627_ = lean_ctor_get(v___x_1625_, 1);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1629_ = v___x_1625_;
v_isShared_1630_ = v_isSharedCheck_1651_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_nextIdx_1627_);
lean_inc(v_lctx_1626_);
lean_dec(v___x_1625_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1651_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
v___x_1631_ = ((lean_object*)(l_Lean_Compiler_LCNF_ctorAppToMono___closed__0));
v___x_1632_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1632_, 0, v_discr_1591_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 3, v___x_1632_);
lean_ctor_set(v___x_1594_, 2, v_a_1624_);
lean_ctor_set(v___x_1594_, 1, v_binderName_1621_);
lean_ctor_set(v___x_1594_, 0, v_fvarId_1620_);
v___x_1634_ = v___x_1594_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_fvarId_1620_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_binderName_1621_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_a_1624_);
lean_ctor_set(v_reuseFailAlloc_1650_, 3, v___x_1632_);
v___x_1634_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1635_; lean_object* v___x_1637_; 
lean_inc_ref(v___x_1634_);
v___x_1635_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1601_, v_lctx_1626_, v___x_1634_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v___x_1635_);
v___x_1637_ = v___x_1629_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_nextIdx_1627_);
v___x_1637_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = lean_st_ref_put(v_a_1587_, v___x_1637_);
v___x_1639_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1608_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1648_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1648_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1648_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1634_);
lean_ctor_set(v___x_1644_, 1, v_a_1640_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1644_);
v___x_1646_ = v___x_1642_;
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
else
{
lean_dec_ref(v___x_1634_);
return v___x_1639_;
}
}
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec(v_binderName_1621_);
lean_dec(v_fvarId_1620_);
lean_dec_ref(v_code_1608_);
lean_del_object(v___x_1594_);
lean_dec(v_discr_1591_);
v_a_1652_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1623_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1623_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec_ref(v_code_1608_);
lean_dec_ref(v_params_1607_);
lean_del_object(v___x_1594_);
lean_dec(v_discr_1591_);
v_a_1660_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1618_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1618_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec(v___x_1605_);
lean_del_object(v___x_1594_);
lean_dec(v_discr_1591_);
v___x_1668_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__6, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__6_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__6);
v___x_1669_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1668_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
return v___x_1669_;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__1));
v___x_1675_ = lean_unsigned_to_nat(70u);
v___x_1676_ = lean_unsigned_to_nat(373u);
v___x_1677_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_1678_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1679_ = l_mkPanicMessageWithDecl(v___x_1678_, v___x_1677_, v___x_1676_, v___x_1675_, v___x_1674_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(lean_object* v___x_1683_, uint8_t v___x_1684_, size_t v_sz_1685_, size_t v_i_1686_, lean_object* v_bs_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
uint8_t v___x_1694_; 
v___x_1694_ = lean_usize_dec_lt(v_i_1686_, v_sz_1685_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; 
lean_dec_ref(v___x_1683_);
v___x_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1695_, 0, v_bs_1687_);
return v___x_1695_;
}
else
{
lean_object* v_v_1696_; lean_object* v___x_1697_; lean_object* v_bs_x27_1698_; lean_object* v_a_1700_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; 
v_v_1696_ = lean_array_uget(v_bs_1687_, v_i_1686_);
v___x_1697_ = lean_unsigned_to_nat(0u);
v_bs_x27_1698_ = lean_array_uset(v_bs_1687_, v_i_1686_, v___x_1697_);
if (lean_obj_tag(v_v_1696_) == 0)
{
lean_object* v_ctorName_1722_; lean_object* v_params_1723_; lean_object* v_code_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1762_; 
v_ctorName_1722_ = lean_ctor_get(v_v_1696_, 0);
v_params_1723_ = lean_ctor_get(v_v_1696_, 1);
v_code_1724_ = lean_ctor_get(v_v_1696_, 2);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_v_1696_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1726_ = v_v_1696_;
v_isShared_1727_ = v_isSharedCheck_1762_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_code_1724_);
lean_inc(v_params_1723_);
lean_inc(v_ctorName_1722_);
lean_dec(v_v_1696_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1762_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4));
v___x_1729_ = l_Lean_Name_append(v_ctorName_1722_, v___x_1728_);
lean_inc(v___x_1729_);
lean_inc_ref(v___x_1683_);
v___x_1730_ = l_Lean_Environment_find_x3f(v___x_1683_, v___x_1729_, v___x_1684_);
if (lean_obj_tag(v___x_1730_) == 1)
{
lean_object* v_val_1731_; 
v_val_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_val_1731_);
lean_dec_ref_known(v___x_1730_, 1);
if (lean_obj_tag(v_val_1731_) == 6)
{
lean_object* v_val_1732_; lean_object* v_toConstantVal_1733_; lean_object* v_numParams_1734_; lean_object* v_numFields_1735_; lean_object* v_type_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v_val_1732_ = lean_ctor_get(v_val_1731_, 0);
lean_inc_ref(v_val_1732_);
lean_dec_ref_known(v_val_1731_, 1);
v_toConstantVal_1733_ = lean_ctor_get(v_val_1732_, 0);
lean_inc_ref(v_toConstantVal_1733_);
v_numParams_1734_ = lean_ctor_get(v_val_1732_, 3);
lean_inc(v_numParams_1734_);
v_numFields_1735_ = lean_ctor_get(v_val_1732_, 4);
lean_inc(v_numFields_1735_);
lean_dec_ref(v_val_1732_);
v_type_1736_ = lean_ctor_get(v_toConstantVal_1733_, 2);
lean_inc_ref(v_type_1736_);
lean_dec_ref(v_toConstantVal_1733_);
v___x_1737_ = lean_array_get_size(v_params_1723_);
v___x_1738_ = lean_nat_sub(v_numFields_1735_, v___x_1737_);
lean_dec(v_numFields_1735_);
v___x_1739_ = l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(v_type_1736_, v_numParams_1734_, v___x_1738_, v_params_1723_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec_ref(v_params_1723_);
lean_dec(v___x_1738_);
lean_dec(v_numParams_1734_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1741_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v___x_1741_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1724_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___x_1744_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref_known(v___x_1741_, 1);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 2, v_a_1742_);
lean_ctor_set(v___x_1726_, 1, v_a_1740_);
lean_ctor_set(v___x_1726_, 0, v___x_1729_);
v___x_1744_ = v___x_1726_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_a_1740_);
lean_ctor_set(v_reuseFailAlloc_1745_, 2, v_a_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
v_a_1700_ = v___x_1744_;
goto v___jp_1699_;
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec(v_a_1740_);
lean_dec(v___x_1729_);
lean_del_object(v___x_1726_);
lean_dec_ref(v_bs_x27_1698_);
lean_dec_ref(v___x_1683_);
v_a_1746_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1741_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1741_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec(v___x_1729_);
lean_del_object(v___x_1726_);
lean_dec_ref(v_code_1724_);
lean_dec_ref(v_bs_x27_1698_);
lean_dec_ref(v___x_1683_);
v_a_1754_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1739_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1739_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
else
{
lean_dec(v_val_1731_);
lean_dec(v___x_1729_);
lean_del_object(v___x_1726_);
lean_dec_ref(v_code_1724_);
lean_dec_ref(v_params_1723_);
v___y_1706_ = v___y_1688_;
v___y_1707_ = v___y_1689_;
v___y_1708_ = v___y_1690_;
v___y_1709_ = v___y_1691_;
v___y_1710_ = v___y_1692_;
goto v___jp_1705_;
}
}
else
{
lean_dec(v___x_1730_);
lean_dec(v___x_1729_);
lean_del_object(v___x_1726_);
lean_dec_ref(v_code_1724_);
lean_dec_ref(v_params_1723_);
v___y_1706_ = v___y_1688_;
v___y_1707_ = v___y_1689_;
v___y_1708_ = v___y_1690_;
v___y_1709_ = v___y_1691_;
v___y_1710_ = v___y_1692_;
goto v___jp_1705_;
}
}
}
else
{
lean_object* v_code_1763_; lean_object* v___x_1764_; 
v_code_1763_ = lean_ctor_get(v_v_1696_, 0);
lean_inc_ref(v_code_1763_);
v___x_1764_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1763_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v___x_1766_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_1696_, v_a_1765_);
v_a_1700_ = v___x_1766_;
goto v___jp_1699_;
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec_ref_known(v_v_1696_, 1);
lean_dec_ref(v_bs_x27_1698_);
lean_dec_ref(v___x_1683_);
v_a_1767_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1764_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1764_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
v___jp_1699_:
{
size_t v___x_1701_; size_t v___x_1702_; lean_object* v___x_1703_; 
v___x_1701_ = ((size_t)1ULL);
v___x_1702_ = lean_usize_add(v_i_1686_, v___x_1701_);
v___x_1703_ = lean_array_uset(v_bs_x27_1698_, v_i_1686_, v_a_1700_);
v_i_1686_ = v___x_1702_;
v_bs_1687_ = v___x_1703_;
goto _start;
}
v___jp_1705_:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2);
v___x_1712_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(v___x_1711_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___x_1712_, 1);
v_a_1700_ = v_a_1713_;
goto v___jp_1699_;
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec_ref(v_bs_x27_1698_);
lean_dec_ref(v___x_1683_);
v_a_1714_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1712_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1712_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(size_t v_sz_1775_, size_t v_i_1776_, lean_object* v_bs_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
uint8_t v___x_1784_; 
v___x_1784_ = lean_usize_dec_lt(v_i_1776_, v_sz_1775_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; 
v___x_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1785_, 0, v_bs_1777_);
return v___x_1785_;
}
else
{
lean_object* v_v_1786_; lean_object* v___x_1787_; lean_object* v_bs_x27_1788_; lean_object* v_a_1790_; 
v_v_1786_ = lean_array_uget(v_bs_1777_, v_i_1776_);
v___x_1787_ = lean_unsigned_to_nat(0u);
v_bs_x27_1788_ = lean_array_uset(v_bs_1777_, v_i_1776_, v___x_1787_);
if (lean_obj_tag(v_v_1786_) == 0)
{
lean_object* v_params_1795_; lean_object* v_code_1796_; size_t v_sz_1797_; size_t v___x_1798_; lean_object* v___x_1799_; 
v_params_1795_ = lean_ctor_get(v_v_1786_, 1);
v_code_1796_ = lean_ctor_get(v_v_1786_, 2);
v_sz_1797_ = lean_array_size(v_params_1795_);
v___x_1798_ = ((size_t)0ULL);
lean_inc_ref(v_params_1795_);
v___x_1799_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_1797_, v___x_1798_, v_params_1795_, v___y_1778_, v___y_1780_, v___y_1781_, v___y_1782_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1801_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1800_);
lean_dec_ref_known(v___x_1799_, 1);
lean_inc_ref(v_code_1796_);
v___x_1801_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1796_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; uint8_t v___x_1803_; lean_object* v___x_1804_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
lean_dec_ref_known(v___x_1801_, 1);
v___x_1803_ = 0;
v___x_1804_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v___x_1803_, v_v_1786_, v_a_1800_, v_a_1802_);
v_a_1790_ = v___x_1804_;
goto v___jp_1789_;
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
lean_dec(v_a_1800_);
lean_dec_ref_known(v_v_1786_, 3);
lean_dec_ref(v_bs_x27_1788_);
v_a_1805_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1801_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1801_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
else
{
lean_dec_ref_known(v_v_1786_, 3);
lean_dec_ref(v_bs_x27_1788_);
return v___x_1799_;
}
}
else
{
lean_object* v_code_1813_; lean_object* v___x_1814_; 
v_code_1813_ = lean_ctor_get(v_v_1786_, 0);
lean_inc_ref(v_code_1813_);
v___x_1814_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1813_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1816_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
lean_dec_ref_known(v___x_1814_, 1);
v___x_1816_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_1786_, v_a_1815_);
v_a_1790_ = v___x_1816_;
goto v___jp_1789_;
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_dec_ref_known(v_v_1786_, 1);
lean_dec_ref(v_bs_x27_1788_);
v_a_1817_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1814_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1814_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
v___jp_1789_:
{
size_t v___x_1791_; size_t v___x_1792_; lean_object* v___x_1793_; 
v___x_1791_ = ((size_t)1ULL);
v___x_1792_ = lean_usize_add(v_i_1776_, v___x_1791_);
v___x_1793_ = lean_array_uset(v_bs_x27_1788_, v_i_1776_, v_a_1790_);
v_i_1776_ = v___x_1792_;
v_bs_1777_ = v___x_1793_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1826_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_1827_ = lean_unsigned_to_nat(2u);
v___x_1828_ = lean_unsigned_to_nat(291u);
v___x_1829_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0));
v___x_1830_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1831_ = l_mkPanicMessageWithDecl(v___x_1830_, v___x_1829_, v___x_1828_, v___x_1827_, v___x_1826_);
return v___x_1831_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1836_ = lean_box(0);
v___x_1837_ = lean_unsigned_to_nat(2u);
v___x_1838_ = lean_mk_empty_array_with_capacity(v___x_1837_);
v___x_1839_ = lean_array_push(v___x_1838_, v___x_1836_);
return v___x_1839_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1840_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1841_ = lean_unsigned_to_nat(34u);
v___x_1842_ = lean_unsigned_to_nat(292u);
v___x_1843_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0));
v___x_1844_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1845_ = l_mkPanicMessageWithDecl(v___x_1844_, v___x_1843_, v___x_1842_, v___x_1841_, v___x_1840_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg(lean_object* v_c_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v_discr_1853_; lean_object* v_alts_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1923_; 
v_discr_1853_ = lean_ctor_get(v_c_1846_, 2);
v_alts_1854_ = lean_ctor_get(v_c_1846_, 3);
v_isSharedCheck_1923_ = !lean_is_exclusive(v_c_1846_);
if (v_isSharedCheck_1923_ == 0)
{
lean_object* v_unused_1924_; lean_object* v_unused_1925_; 
v_unused_1924_ = lean_ctor_get(v_c_1846_, 1);
lean_dec(v_unused_1924_);
v_unused_1925_ = lean_ctor_get(v_c_1846_, 0);
lean_dec(v_unused_1925_);
v___x_1856_ = v_c_1846_;
v_isShared_1857_ = v_isSharedCheck_1923_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_alts_1854_);
lean_inc(v_discr_1853_);
lean_dec(v_c_1846_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1923_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; uint8_t v___x_1860_; 
v___x_1858_ = lean_array_get_size(v_alts_1854_);
v___x_1859_ = lean_unsigned_to_nat(1u);
v___x_1860_ = lean_nat_dec_eq(v___x_1858_, v___x_1859_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
lean_del_object(v___x_1856_);
lean_dec_ref(v_alts_1854_);
lean_dec(v_discr_1853_);
v___x_1861_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1);
v___x_1862_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1861_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
return v___x_1862_;
}
else
{
uint8_t v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1863_ = 0;
v___x_1864_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_1865_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_1866_ = lean_unsigned_to_nat(0u);
v___x_1867_ = lean_array_get(v___x_1865_, v_alts_1854_, v___x_1866_);
lean_dec_ref(v_alts_1854_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_params_1868_; lean_object* v_code_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1919_; 
v_params_1868_ = lean_ctor_get(v___x_1867_, 1);
v_code_1869_ = lean_ctor_get(v___x_1867_, 2);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1919_ == 0)
{
lean_object* v_unused_1920_; 
v_unused_1920_ = lean_ctor_get(v___x_1867_, 0);
lean_dec(v_unused_1920_);
v___x_1871_ = v___x_1867_;
v_isShared_1872_ = v_isSharedCheck_1919_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_code_1869_);
lean_inc(v_params_1868_);
lean_dec(v___x_1867_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1919_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1863_, v_params_1868_, v_a_1849_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v_fvarId_1876_; lean_object* v_binderName_1877_; lean_object* v_lctx_1878_; lean_object* v_nextIdx_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1910_; 
lean_dec_ref_known(v___x_1873_, 1);
v___x_1874_ = lean_st_ref_take(v_a_1849_);
v___x_1875_ = lean_array_get(v___x_1864_, v_params_1868_, v___x_1866_);
lean_dec_ref(v_params_1868_);
v_fvarId_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_fvarId_1876_);
v_binderName_1877_ = lean_ctor_get(v___x_1875_, 1);
lean_inc(v_binderName_1877_);
lean_dec(v___x_1875_);
v_lctx_1878_ = lean_ctor_get(v___x_1874_, 0);
v_nextIdx_1879_ = lean_ctor_get(v___x_1874_, 1);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1881_ = v___x_1874_;
v_isShared_1882_ = v_isSharedCheck_1910_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_nextIdx_1879_);
lean_inc(v_lctx_1878_);
lean_dec(v___x_1874_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1910_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1883_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__4));
v___x_1884_ = lean_box(0);
v___x_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1885_, 0, v_discr_1853_);
v___x_1886_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_1887_ = lean_array_push(v___x_1886_, v___x_1885_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set_tag(v___x_1871_, 3);
lean_ctor_set(v___x_1871_, 2, v___x_1887_);
lean_ctor_set(v___x_1871_, 1, v___x_1884_);
lean_ctor_set(v___x_1871_, 0, v___x_1883_);
v___x_1889_ = v___x_1871_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v___x_1884_);
lean_ctor_set(v_reuseFailAlloc_1909_, 2, v___x_1887_);
v___x_1889_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1890_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 3, v___x_1889_);
lean_ctor_set(v___x_1856_, 2, v___x_1890_);
lean_ctor_set(v___x_1856_, 1, v_binderName_1877_);
lean_ctor_set(v___x_1856_, 0, v_fvarId_1876_);
v___x_1892_ = v___x_1856_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_fvarId_1876_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_binderName_1877_);
lean_ctor_set(v_reuseFailAlloc_1908_, 2, v___x_1890_);
lean_ctor_set(v_reuseFailAlloc_1908_, 3, v___x_1889_);
v___x_1892_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
lean_inc_ref(v___x_1892_);
v___x_1893_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1863_, v_lctx_1878_, v___x_1892_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v___x_1893_);
v___x_1895_ = v___x_1881_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1893_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_nextIdx_1879_);
v___x_1895_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_st_ref_put(v_a_1849_, v___x_1895_);
v___x_1897_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1869_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1906_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1900_ = v___x_1897_;
v_isShared_1901_ = v_isSharedCheck_1906_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1897_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1906_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1902_; lean_object* v___x_1904_; 
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1892_);
lean_ctor_set(v___x_1902_, 1, v_a_1898_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 0, v___x_1902_);
v___x_1904_ = v___x_1900_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1902_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
else
{
lean_dec_ref(v___x_1892_);
return v___x_1897_;
}
}
}
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_del_object(v___x_1871_);
lean_dec_ref(v_code_1869_);
lean_dec_ref(v_params_1868_);
lean_del_object(v___x_1856_);
lean_dec(v_discr_1853_);
v_a_1911_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1873_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1873_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
}
else
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
lean_dec(v___x_1867_);
lean_del_object(v___x_1856_);
lean_dec(v_discr_1853_);
v___x_1921_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5);
v___x_1922_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1921_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
return v___x_1922_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1927_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_1928_ = lean_unsigned_to_nat(2u);
v___x_1929_ = lean_unsigned_to_nat(271u);
v___x_1930_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0));
v___x_1931_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1932_ = l_mkPanicMessageWithDecl(v___x_1931_, v___x_1930_, v___x_1929_, v___x_1928_, v___x_1927_);
return v___x_1932_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8(void){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1939_ = lean_box(0);
v___x_1940_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__7));
v___x_1941_ = l_Lean_Expr_const___override(v___x_1940_, v___x_1939_);
return v___x_1941_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9(void){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1942_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1943_ = lean_unsigned_to_nat(34u);
v___x_1944_ = lean_unsigned_to_nat(272u);
v___x_1945_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0));
v___x_1946_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1947_ = l_mkPanicMessageWithDecl(v___x_1946_, v___x_1945_, v___x_1944_, v___x_1943_, v___x_1942_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg(lean_object* v_c_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v_discr_1955_; lean_object* v_alts_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v_discr_1955_ = lean_ctor_get(v_c_1948_, 2);
v_alts_1956_ = lean_ctor_get(v_c_1948_, 3);
v___x_1957_ = lean_array_get_size(v_alts_1956_);
v___x_1958_ = lean_unsigned_to_nat(1u);
v___x_1959_ = lean_nat_dec_eq(v___x_1957_, v___x_1958_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1);
v___x_1961_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1960_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
return v___x_1961_;
}
else
{
uint8_t v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1962_ = 0;
v___x_1963_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_1964_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_1965_ = lean_unsigned_to_nat(0u);
v___x_1966_ = lean_array_get(v___x_1964_, v_alts_1956_, v___x_1965_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_params_1967_; lean_object* v_code_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_2064_; 
v_params_1967_ = lean_ctor_get(v___x_1966_, 1);
v_code_1968_ = lean_ctor_get(v___x_1966_, 2);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; 
v_unused_2065_ = lean_ctor_get(v___x_1966_, 0);
lean_dec(v_unused_2065_);
v___x_1970_ = v___x_1966_;
v_isShared_1971_ = v_isSharedCheck_2064_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_code_1968_);
lean_inc(v_params_1967_);
lean_dec(v___x_1966_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_2064_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1962_, v_params_1967_, v_a_1951_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_dec_ref_known(v___x_1972_, 1);
v___x_1973_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3));
v___x_1974_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1973_, v_a_1951_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1982_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref_known(v___x_1974_, 1);
lean_inc(v_discr_1955_);
v___x_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1976_, 0, v_discr_1955_);
v___x_1977_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5));
v___x_1978_ = lean_box(0);
v___x_1979_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_1980_ = lean_array_push(v___x_1979_, v___x_1976_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set_tag(v___x_1970_, 3);
lean_ctor_set(v___x_1970_, 2, v___x_1980_);
lean_ctor_set(v___x_1970_, 1, v___x_1978_);
lean_ctor_set(v___x_1970_, 0, v___x_1977_);
v___x_1982_ = v___x_1970_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_2047_, 2, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_2047_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_1984_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1962_, v_a_1975_, v___x_1983_, v___x_1982_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; lean_object* v___x_1988_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1984_, 1);
v___x_1986_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8);
v___x_1987_ = 0;
v___x_1988_ = l_Lean_Compiler_LCNF_mkAuxParam(v___x_1962_, v___x_1986_, v___x_1987_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1990_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___x_1988_, 1);
v___x_1990_ = l_Lean_mkArrow(v___x_1986_, v___x_1983_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v_fvarId_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v_fvarId_1995_; lean_object* v_binderName_1996_; lean_object* v_lctx_1997_; lean_object* v_nextIdx_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2022_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1990_, 1);
v_fvarId_1992_ = lean_ctor_get(v_a_1985_, 0);
v___x_1993_ = lean_st_ref_take(v_a_1951_);
v___x_1994_ = lean_array_get(v___x_1963_, v_params_1967_, v___x_1965_);
lean_dec_ref(v_params_1967_);
v_fvarId_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_fvarId_1995_);
v_binderName_1996_ = lean_ctor_get(v___x_1994_, 1);
lean_inc(v_binderName_1996_);
lean_dec(v___x_1994_);
v_lctx_1997_ = lean_ctor_get(v___x_1993_, 0);
v_nextIdx_1998_ = lean_ctor_get(v___x_1993_, 1);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2000_ = v___x_1993_;
v_isShared_2001_ = v_isSharedCheck_2022_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_nextIdx_1998_);
lean_inc(v_lctx_1997_);
lean_dec(v___x_1993_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2022_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2009_; 
lean_inc(v_fvarId_1992_);
v___x_2002_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2002_, 0, v_fvarId_1992_);
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v_a_1985_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v___x_2004_ = lean_mk_empty_array_with_capacity(v___x_1958_);
v___x_2005_ = lean_array_push(v___x_2004_, v_a_1989_);
v___x_2006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2006_, 0, v_fvarId_1995_);
lean_ctor_set(v___x_2006_, 1, v_binderName_1996_);
lean_ctor_set(v___x_2006_, 2, v___x_2005_);
lean_ctor_set(v___x_2006_, 3, v_a_1991_);
lean_ctor_set(v___x_2006_, 4, v___x_2003_);
lean_inc_ref(v___x_2006_);
v___x_2007_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_1962_, v_lctx_1997_, v___x_2006_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2007_);
v___x_2009_ = v___x_2000_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_nextIdx_1998_);
v___x_2009_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_st_ref_put(v_a_1951_, v___x_2009_);
v___x_2011_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1968_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2020_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2006_);
lean_ctor_set(v___x_2016_, 1, v_a_2012_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2016_);
v___x_2018_ = v___x_2014_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
else
{
lean_dec_ref_known(v___x_2006_, 5);
return v___x_2011_;
}
}
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec(v_a_1989_);
lean_dec(v_a_1985_);
lean_dec_ref(v_code_1968_);
lean_dec_ref(v_params_1967_);
v_a_2023_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_1990_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_1990_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec(v_a_1985_);
lean_dec_ref(v_code_1968_);
lean_dec_ref(v_params_1967_);
v_a_2031_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_1988_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_1988_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec_ref(v_code_1968_);
lean_dec_ref(v_params_1967_);
v_a_2039_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_1984_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_1984_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_del_object(v___x_1970_);
lean_dec_ref(v_code_1968_);
lean_dec_ref(v_params_1967_);
v_a_2048_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_1974_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_1974_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_del_object(v___x_1970_);
lean_dec_ref(v_code_1968_);
lean_dec_ref(v_params_1967_);
v_a_2056_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_1972_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_1972_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
lean_dec(v___x_1966_);
v___x_2066_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9);
v___x_2067_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2066_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
return v___x_2067_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2069_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2070_ = lean_unsigned_to_nat(2u);
v___x_2071_ = lean_unsigned_to_nat(260u);
v___x_2072_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0));
v___x_2073_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2074_ = l_mkPanicMessageWithDecl(v___x_2073_, v___x_2072_, v___x_2071_, v___x_2070_, v___x_2069_);
return v___x_2074_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2079_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2080_ = lean_unsigned_to_nat(34u);
v___x_2081_ = lean_unsigned_to_nat(261u);
v___x_2082_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0));
v___x_2083_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2084_ = l_mkPanicMessageWithDecl(v___x_2083_, v___x_2082_, v___x_2081_, v___x_2080_, v___x_2079_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(lean_object* v_c_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_){
_start:
{
lean_object* v_discr_2092_; lean_object* v_alts_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2162_; 
v_discr_2092_ = lean_ctor_get(v_c_2085_, 2);
v_alts_2093_ = lean_ctor_get(v_c_2085_, 3);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_c_2085_);
if (v_isSharedCheck_2162_ == 0)
{
lean_object* v_unused_2163_; lean_object* v_unused_2164_; 
v_unused_2163_ = lean_ctor_get(v_c_2085_, 1);
lean_dec(v_unused_2163_);
v_unused_2164_ = lean_ctor_get(v_c_2085_, 0);
lean_dec(v_unused_2164_);
v___x_2095_ = v_c_2085_;
v_isShared_2096_ = v_isSharedCheck_2162_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_alts_2093_);
lean_inc(v_discr_2092_);
lean_dec(v_c_2085_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2162_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v___x_2097_ = lean_array_get_size(v_alts_2093_);
v___x_2098_ = lean_unsigned_to_nat(1u);
v___x_2099_ = lean_nat_dec_eq(v___x_2097_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
lean_del_object(v___x_2095_);
lean_dec_ref(v_alts_2093_);
lean_dec(v_discr_2092_);
v___x_2100_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1);
v___x_2101_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2100_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
return v___x_2101_;
}
else
{
uint8_t v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2102_ = 0;
v___x_2103_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2104_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2105_ = lean_unsigned_to_nat(0u);
v___x_2106_ = lean_array_get(v___x_2104_, v_alts_2093_, v___x_2105_);
lean_dec_ref(v_alts_2093_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_params_2107_; lean_object* v_code_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2158_; 
v_params_2107_ = lean_ctor_get(v___x_2106_, 1);
v_code_2108_ = lean_ctor_get(v___x_2106_, 2);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2158_ == 0)
{
lean_object* v_unused_2159_; 
v_unused_2159_ = lean_ctor_get(v___x_2106_, 0);
lean_dec(v_unused_2159_);
v___x_2110_ = v___x_2106_;
v_isShared_2111_ = v_isSharedCheck_2158_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_code_2108_);
lean_inc(v_params_2107_);
lean_dec(v___x_2106_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2158_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2102_, v_params_2107_, v_a_2088_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v_fvarId_2115_; lean_object* v_binderName_2116_; lean_object* v_lctx_2117_; lean_object* v_nextIdx_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2149_; 
lean_dec_ref_known(v___x_2112_, 1);
v___x_2113_ = lean_st_ref_take(v_a_2088_);
v___x_2114_ = lean_array_get(v___x_2103_, v_params_2107_, v___x_2105_);
lean_dec_ref(v_params_2107_);
v_fvarId_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_fvarId_2115_);
v_binderName_2116_ = lean_ctor_get(v___x_2114_, 1);
lean_inc(v_binderName_2116_);
lean_dec(v___x_2114_);
v_lctx_2117_ = lean_ctor_get(v___x_2113_, 0);
v_nextIdx_2118_ = lean_ctor_get(v___x_2113_, 1);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2120_ = v___x_2113_;
v_isShared_2121_ = v_isSharedCheck_2149_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_nextIdx_2118_);
lean_inc(v_lctx_2117_);
lean_dec(v___x_2113_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2149_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2122_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__4));
v___x_2123_ = lean_box(0);
v___x_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2124_, 0, v_discr_2092_);
v___x_2125_ = lean_mk_empty_array_with_capacity(v___x_2098_);
v___x_2126_ = lean_array_push(v___x_2125_, v___x_2124_);
if (v_isShared_2111_ == 0)
{
lean_ctor_set_tag(v___x_2110_, 3);
lean_ctor_set(v___x_2110_, 2, v___x_2126_);
lean_ctor_set(v___x_2110_, 1, v___x_2123_);
lean_ctor_set(v___x_2110_, 0, v___x_2122_);
v___x_2128_ = v___x_2110_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v___x_2123_);
lean_ctor_set(v_reuseFailAlloc_2148_, 2, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2129_; lean_object* v___x_2131_; 
v___x_2129_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 3, v___x_2128_);
lean_ctor_set(v___x_2095_, 2, v___x_2129_);
lean_ctor_set(v___x_2095_, 1, v_binderName_2116_);
lean_ctor_set(v___x_2095_, 0, v_fvarId_2115_);
v___x_2131_ = v___x_2095_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_fvarId_2115_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_binderName_2116_);
lean_ctor_set(v_reuseFailAlloc_2147_, 2, v___x_2129_);
lean_ctor_set(v_reuseFailAlloc_2147_, 3, v___x_2128_);
v___x_2131_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2132_; lean_object* v___x_2134_; 
lean_inc_ref(v___x_2131_);
v___x_2132_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2102_, v_lctx_2117_, v___x_2131_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2132_);
v___x_2134_ = v___x_2120_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_nextIdx_2118_);
v___x_2134_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = lean_st_ref_put(v_a_2088_, v___x_2134_);
v___x_2136_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2108_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2145_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2139_ = v___x_2136_;
v_isShared_2140_ = v_isSharedCheck_2145_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2136_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2145_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2131_);
lean_ctor_set(v___x_2141_, 1, v_a_2137_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2141_);
v___x_2143_ = v___x_2139_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
else
{
lean_dec_ref(v___x_2131_);
return v___x_2136_;
}
}
}
}
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_del_object(v___x_2110_);
lean_dec_ref(v_code_2108_);
lean_dec_ref(v_params_2107_);
lean_del_object(v___x_2095_);
lean_dec(v_discr_2092_);
v_a_2150_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2112_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2112_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
}
else
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
lean_dec(v___x_2106_);
lean_del_object(v___x_2095_);
lean_dec(v_discr_2092_);
v___x_2160_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5);
v___x_2161_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2160_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
return v___x_2161_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2166_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2167_ = lean_unsigned_to_nat(2u);
v___x_2168_ = lean_unsigned_to_nat(249u);
v___x_2169_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0));
v___x_2170_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2171_ = l_mkPanicMessageWithDecl(v___x_2170_, v___x_2169_, v___x_2168_, v___x_2167_, v___x_2166_);
return v___x_2171_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2175_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2176_ = lean_unsigned_to_nat(34u);
v___x_2177_ = lean_unsigned_to_nat(250u);
v___x_2178_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0));
v___x_2179_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2180_ = l_mkPanicMessageWithDecl(v___x_2179_, v___x_2178_, v___x_2177_, v___x_2176_, v___x_2175_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg(lean_object* v_c_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_){
_start:
{
lean_object* v_discr_2188_; lean_object* v_alts_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2258_; 
v_discr_2188_ = lean_ctor_get(v_c_2181_, 2);
v_alts_2189_ = lean_ctor_get(v_c_2181_, 3);
v_isSharedCheck_2258_ = !lean_is_exclusive(v_c_2181_);
if (v_isSharedCheck_2258_ == 0)
{
lean_object* v_unused_2259_; lean_object* v_unused_2260_; 
v_unused_2259_ = lean_ctor_get(v_c_2181_, 1);
lean_dec(v_unused_2259_);
v_unused_2260_ = lean_ctor_get(v_c_2181_, 0);
lean_dec(v_unused_2260_);
v___x_2191_ = v_c_2181_;
v_isShared_2192_ = v_isSharedCheck_2258_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_alts_2189_);
lean_inc(v_discr_2188_);
lean_dec(v_c_2181_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2258_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
v___x_2193_ = lean_array_get_size(v_alts_2189_);
v___x_2194_ = lean_unsigned_to_nat(1u);
v___x_2195_ = lean_nat_dec_eq(v___x_2193_, v___x_2194_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_del_object(v___x_2191_);
lean_dec_ref(v_alts_2189_);
lean_dec(v_discr_2188_);
v___x_2196_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1);
v___x_2197_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2196_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_);
return v___x_2197_;
}
else
{
uint8_t v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2198_ = 0;
v___x_2199_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2200_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2201_ = lean_unsigned_to_nat(0u);
v___x_2202_ = lean_array_get(v___x_2200_, v_alts_2189_, v___x_2201_);
lean_dec_ref(v_alts_2189_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_params_2203_; lean_object* v_code_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2254_; 
v_params_2203_ = lean_ctor_get(v___x_2202_, 1);
v_code_2204_ = lean_ctor_get(v___x_2202_, 2);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2254_ == 0)
{
lean_object* v_unused_2255_; 
v_unused_2255_ = lean_ctor_get(v___x_2202_, 0);
lean_dec(v_unused_2255_);
v___x_2206_ = v___x_2202_;
v_isShared_2207_ = v_isSharedCheck_2254_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_code_2204_);
lean_inc(v_params_2203_);
lean_dec(v___x_2202_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2254_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2198_, v_params_2203_, v_a_2184_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v_fvarId_2211_; lean_object* v_binderName_2212_; lean_object* v_lctx_2213_; lean_object* v_nextIdx_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2245_; 
lean_dec_ref_known(v___x_2208_, 1);
v___x_2209_ = lean_st_ref_take(v_a_2184_);
v___x_2210_ = lean_array_get(v___x_2199_, v_params_2203_, v___x_2201_);
lean_dec_ref(v_params_2203_);
v_fvarId_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_fvarId_2211_);
v_binderName_2212_ = lean_ctor_get(v___x_2210_, 1);
lean_inc(v_binderName_2212_);
lean_dec(v___x_2210_);
v_lctx_2213_ = lean_ctor_get(v___x_2209_, 0);
v_nextIdx_2214_ = lean_ctor_get(v___x_2209_, 1);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2216_ = v___x_2209_;
v_isShared_2217_ = v_isSharedCheck_2245_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_nextIdx_2214_);
lean_inc(v_lctx_2213_);
lean_dec(v___x_2209_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2245_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2218_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__3));
v___x_2219_ = lean_box(0);
v___x_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2220_, 0, v_discr_2188_);
v___x_2221_ = lean_mk_empty_array_with_capacity(v___x_2194_);
v___x_2222_ = lean_array_push(v___x_2221_, v___x_2220_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set_tag(v___x_2206_, 3);
lean_ctor_set(v___x_2206_, 2, v___x_2222_);
lean_ctor_set(v___x_2206_, 1, v___x_2219_);
lean_ctor_set(v___x_2206_, 0, v___x_2218_);
v___x_2224_ = v___x_2206_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2218_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2244_, 2, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2225_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 3, v___x_2224_);
lean_ctor_set(v___x_2191_, 2, v___x_2225_);
lean_ctor_set(v___x_2191_, 1, v_binderName_2212_);
lean_ctor_set(v___x_2191_, 0, v_fvarId_2211_);
v___x_2227_ = v___x_2191_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_fvarId_2211_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_binderName_2212_);
lean_ctor_set(v_reuseFailAlloc_2243_, 2, v___x_2225_);
lean_ctor_set(v_reuseFailAlloc_2243_, 3, v___x_2224_);
v___x_2227_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2228_; lean_object* v___x_2230_; 
lean_inc_ref(v___x_2227_);
v___x_2228_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2198_, v_lctx_2213_, v___x_2227_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 0, v___x_2228_);
v___x_2230_ = v___x_2216_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v_nextIdx_2214_);
v___x_2230_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = lean_st_ref_put(v_a_2184_, v___x_2230_);
v___x_2232_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2204_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2241_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2235_ = v___x_2232_;
v_isShared_2236_ = v_isSharedCheck_2241_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2232_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2241_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2227_);
lean_ctor_set(v___x_2237_, 1, v_a_2233_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 0, v___x_2237_);
v___x_2239_ = v___x_2235_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
else
{
lean_dec_ref(v___x_2227_);
return v___x_2232_;
}
}
}
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_del_object(v___x_2206_);
lean_dec_ref(v_code_2204_);
lean_dec_ref(v_params_2203_);
lean_del_object(v___x_2191_);
lean_dec(v_discr_2188_);
v_a_2246_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2208_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2208_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
lean_dec(v___x_2202_);
lean_del_object(v___x_2191_);
lean_dec(v_discr_2188_);
v___x_2256_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4);
v___x_2257_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2256_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_);
return v___x_2257_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2262_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2263_ = lean_unsigned_to_nat(2u);
v___x_2264_ = lean_unsigned_to_nat(238u);
v___x_2265_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0));
v___x_2266_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2267_ = l_mkPanicMessageWithDecl(v___x_2266_, v___x_2265_, v___x_2264_, v___x_2263_, v___x_2262_);
return v___x_2267_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2272_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2273_ = lean_unsigned_to_nat(34u);
v___x_2274_ = lean_unsigned_to_nat(239u);
v___x_2275_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0));
v___x_2276_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2277_ = l_mkPanicMessageWithDecl(v___x_2276_, v___x_2275_, v___x_2274_, v___x_2273_, v___x_2272_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg(lean_object* v_c_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v_discr_2285_; lean_object* v_alts_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2355_; 
v_discr_2285_ = lean_ctor_get(v_c_2278_, 2);
v_alts_2286_ = lean_ctor_get(v_c_2278_, 3);
v_isSharedCheck_2355_ = !lean_is_exclusive(v_c_2278_);
if (v_isSharedCheck_2355_ == 0)
{
lean_object* v_unused_2356_; lean_object* v_unused_2357_; 
v_unused_2356_ = lean_ctor_get(v_c_2278_, 1);
lean_dec(v_unused_2356_);
v_unused_2357_ = lean_ctor_get(v_c_2278_, 0);
lean_dec(v_unused_2357_);
v___x_2288_ = v_c_2278_;
v_isShared_2289_ = v_isSharedCheck_2355_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_alts_2286_);
lean_inc(v_discr_2285_);
lean_dec(v_c_2278_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2355_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; uint8_t v___x_2292_; 
v___x_2290_ = lean_array_get_size(v_alts_2286_);
v___x_2291_ = lean_unsigned_to_nat(1u);
v___x_2292_ = lean_nat_dec_eq(v___x_2290_, v___x_2291_);
if (v___x_2292_ == 0)
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
lean_del_object(v___x_2288_);
lean_dec_ref(v_alts_2286_);
lean_dec(v_discr_2285_);
v___x_2293_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1);
v___x_2294_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2293_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_2294_;
}
else
{
uint8_t v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2295_ = 0;
v___x_2296_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2297_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2298_ = lean_unsigned_to_nat(0u);
v___x_2299_ = lean_array_get(v___x_2297_, v_alts_2286_, v___x_2298_);
lean_dec_ref(v_alts_2286_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_params_2300_; lean_object* v_code_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2351_; 
v_params_2300_ = lean_ctor_get(v___x_2299_, 1);
v_code_2301_ = lean_ctor_get(v___x_2299_, 2);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2351_ == 0)
{
lean_object* v_unused_2352_; 
v_unused_2352_ = lean_ctor_get(v___x_2299_, 0);
lean_dec(v_unused_2352_);
v___x_2303_ = v___x_2299_;
v_isShared_2304_ = v_isSharedCheck_2351_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_code_2301_);
lean_inc(v_params_2300_);
lean_dec(v___x_2299_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2351_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2295_, v_params_2300_, v_a_2281_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v_fvarId_2308_; lean_object* v_binderName_2309_; lean_object* v_lctx_2310_; lean_object* v_nextIdx_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2342_; 
lean_dec_ref_known(v___x_2305_, 1);
v___x_2306_ = lean_st_ref_take(v_a_2281_);
v___x_2307_ = lean_array_get(v___x_2296_, v_params_2300_, v___x_2298_);
lean_dec_ref(v_params_2300_);
v_fvarId_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_fvarId_2308_);
v_binderName_2309_ = lean_ctor_get(v___x_2307_, 1);
lean_inc(v_binderName_2309_);
lean_dec(v___x_2307_);
v_lctx_2310_ = lean_ctor_get(v___x_2306_, 0);
v_nextIdx_2311_ = lean_ctor_get(v___x_2306_, 1);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2313_ = v___x_2306_;
v_isShared_2314_ = v_isSharedCheck_2342_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_nextIdx_2311_);
lean_inc(v_lctx_2310_);
lean_dec(v___x_2306_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2342_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2321_; 
v___x_2315_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__4));
v___x_2316_ = lean_box(0);
v___x_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2317_, 0, v_discr_2285_);
v___x_2318_ = lean_mk_empty_array_with_capacity(v___x_2291_);
v___x_2319_ = lean_array_push(v___x_2318_, v___x_2317_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set_tag(v___x_2303_, 3);
lean_ctor_set(v___x_2303_, 2, v___x_2319_);
lean_ctor_set(v___x_2303_, 1, v___x_2316_);
lean_ctor_set(v___x_2303_, 0, v___x_2315_);
v___x_2321_ = v___x_2303_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2315_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v___x_2316_);
lean_ctor_set(v_reuseFailAlloc_2341_, 2, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
lean_object* v___x_2322_; lean_object* v___x_2324_; 
v___x_2322_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 3, v___x_2321_);
lean_ctor_set(v___x_2288_, 2, v___x_2322_);
lean_ctor_set(v___x_2288_, 1, v_binderName_2309_);
lean_ctor_set(v___x_2288_, 0, v_fvarId_2308_);
v___x_2324_ = v___x_2288_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_fvarId_2308_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_binderName_2309_);
lean_ctor_set(v_reuseFailAlloc_2340_, 2, v___x_2322_);
lean_ctor_set(v_reuseFailAlloc_2340_, 3, v___x_2321_);
v___x_2324_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2325_; lean_object* v___x_2327_; 
lean_inc_ref(v___x_2324_);
v___x_2325_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2295_, v_lctx_2310_, v___x_2324_);
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 0, v___x_2325_);
v___x_2327_ = v___x_2313_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2325_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v_nextIdx_2311_);
v___x_2327_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = lean_st_ref_put(v_a_2281_, v___x_2327_);
v___x_2329_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2301_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2338_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2338_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2338_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; lean_object* v___x_2336_; 
v___x_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2324_);
lean_ctor_set(v___x_2334_, 1, v_a_2330_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2334_);
v___x_2336_ = v___x_2332_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2334_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
else
{
lean_dec_ref(v___x_2324_);
return v___x_2329_;
}
}
}
}
}
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_del_object(v___x_2303_);
lean_dec_ref(v_code_2301_);
lean_dec_ref(v_params_2300_);
lean_del_object(v___x_2288_);
lean_dec(v_discr_2285_);
v_a_2343_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2305_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2305_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
else
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
lean_dec(v___x_2299_);
lean_del_object(v___x_2288_);
lean_dec(v_discr_2285_);
v___x_2353_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5);
v___x_2354_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2353_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_2354_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2359_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2360_ = lean_unsigned_to_nat(2u);
v___x_2361_ = lean_unsigned_to_nat(227u);
v___x_2362_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0));
v___x_2363_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2364_ = l_mkPanicMessageWithDecl(v___x_2363_, v___x_2362_, v___x_2361_, v___x_2360_, v___x_2359_);
return v___x_2364_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2369_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2370_ = lean_unsigned_to_nat(34u);
v___x_2371_ = lean_unsigned_to_nat(228u);
v___x_2372_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0));
v___x_2373_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2374_ = l_mkPanicMessageWithDecl(v___x_2373_, v___x_2372_, v___x_2371_, v___x_2370_, v___x_2369_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(lean_object* v_c_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v_discr_2382_; lean_object* v_alts_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2452_; 
v_discr_2382_ = lean_ctor_get(v_c_2375_, 2);
v_alts_2383_ = lean_ctor_get(v_c_2375_, 3);
v_isSharedCheck_2452_ = !lean_is_exclusive(v_c_2375_);
if (v_isSharedCheck_2452_ == 0)
{
lean_object* v_unused_2453_; lean_object* v_unused_2454_; 
v_unused_2453_ = lean_ctor_get(v_c_2375_, 1);
lean_dec(v_unused_2453_);
v_unused_2454_ = lean_ctor_get(v_c_2375_, 0);
lean_dec(v_unused_2454_);
v___x_2385_ = v_c_2375_;
v_isShared_2386_ = v_isSharedCheck_2452_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_alts_2383_);
lean_inc(v_discr_2382_);
lean_dec(v_c_2375_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2452_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; uint8_t v___x_2389_; 
v___x_2387_ = lean_array_get_size(v_alts_2383_);
v___x_2388_ = lean_unsigned_to_nat(1u);
v___x_2389_ = lean_nat_dec_eq(v___x_2387_, v___x_2388_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
lean_del_object(v___x_2385_);
lean_dec_ref(v_alts_2383_);
lean_dec(v_discr_2382_);
v___x_2390_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1);
v___x_2391_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2390_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
return v___x_2391_;
}
else
{
uint8_t v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2392_ = 0;
v___x_2393_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2394_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2395_ = lean_unsigned_to_nat(0u);
v___x_2396_ = lean_array_get(v___x_2394_, v_alts_2383_, v___x_2395_);
lean_dec_ref(v_alts_2383_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_params_2397_; lean_object* v_code_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2448_; 
v_params_2397_ = lean_ctor_get(v___x_2396_, 1);
v_code_2398_ = lean_ctor_get(v___x_2396_, 2);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2448_ == 0)
{
lean_object* v_unused_2449_; 
v_unused_2449_ = lean_ctor_get(v___x_2396_, 0);
lean_dec(v_unused_2449_);
v___x_2400_ = v___x_2396_;
v_isShared_2401_ = v_isSharedCheck_2448_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_code_2398_);
lean_inc(v_params_2397_);
lean_dec(v___x_2396_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2448_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; 
v___x_2402_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2392_, v_params_2397_, v_a_2378_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v_fvarId_2405_; lean_object* v_binderName_2406_; lean_object* v_lctx_2407_; lean_object* v_nextIdx_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2439_; 
lean_dec_ref_known(v___x_2402_, 1);
v___x_2403_ = lean_st_ref_take(v_a_2378_);
v___x_2404_ = lean_array_get(v___x_2393_, v_params_2397_, v___x_2395_);
lean_dec_ref(v_params_2397_);
v_fvarId_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_fvarId_2405_);
v_binderName_2406_ = lean_ctor_get(v___x_2404_, 1);
lean_inc(v_binderName_2406_);
lean_dec(v___x_2404_);
v_lctx_2407_ = lean_ctor_get(v___x_2403_, 0);
v_nextIdx_2408_ = lean_ctor_get(v___x_2403_, 1);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2410_ = v___x_2403_;
v_isShared_2411_ = v_isSharedCheck_2439_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_nextIdx_2408_);
lean_inc(v_lctx_2407_);
lean_dec(v___x_2403_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2439_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2418_; 
v___x_2412_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__3));
v___x_2413_ = lean_box(0);
v___x_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2414_, 0, v_discr_2382_);
v___x_2415_ = lean_mk_empty_array_with_capacity(v___x_2388_);
v___x_2416_ = lean_array_push(v___x_2415_, v___x_2414_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set_tag(v___x_2400_, 3);
lean_ctor_set(v___x_2400_, 2, v___x_2416_);
lean_ctor_set(v___x_2400_, 1, v___x_2413_);
lean_ctor_set(v___x_2400_, 0, v___x_2412_);
v___x_2418_ = v___x_2400_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2438_, 2, v___x_2416_);
v___x_2418_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
lean_object* v___x_2419_; lean_object* v___x_2421_; 
v___x_2419_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 3, v___x_2418_);
lean_ctor_set(v___x_2385_, 2, v___x_2419_);
lean_ctor_set(v___x_2385_, 1, v_binderName_2406_);
lean_ctor_set(v___x_2385_, 0, v_fvarId_2405_);
v___x_2421_ = v___x_2385_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_fvarId_2405_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_binderName_2406_);
lean_ctor_set(v_reuseFailAlloc_2437_, 2, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2437_, 3, v___x_2418_);
v___x_2421_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2422_; lean_object* v___x_2424_; 
lean_inc_ref(v___x_2421_);
v___x_2422_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2392_, v_lctx_2407_, v___x_2421_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v___x_2422_);
v___x_2424_ = v___x_2410_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2422_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v_nextIdx_2408_);
v___x_2424_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = lean_st_ref_put(v_a_2378_, v___x_2424_);
v___x_2426_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2398_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2435_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2429_ = v___x_2426_;
v_isShared_2430_ = v_isSharedCheck_2435_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2426_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2435_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2421_);
lean_ctor_set(v___x_2431_, 1, v_a_2427_);
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 0, v___x_2431_);
v___x_2433_ = v___x_2429_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
else
{
lean_dec_ref(v___x_2421_);
return v___x_2426_;
}
}
}
}
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_del_object(v___x_2400_);
lean_dec_ref(v_code_2398_);
lean_dec_ref(v_params_2397_);
lean_del_object(v___x_2385_);
lean_dec(v_discr_2382_);
v_a_2440_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2402_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2402_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
else
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
lean_dec(v___x_2396_);
lean_del_object(v___x_2385_);
lean_dec(v_discr_2382_);
v___x_2450_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4);
v___x_2451_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2450_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
return v___x_2451_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2456_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2457_ = lean_unsigned_to_nat(2u);
v___x_2458_ = lean_unsigned_to_nat(215u);
v___x_2459_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0));
v___x_2460_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2461_ = l_mkPanicMessageWithDecl(v___x_2460_, v___x_2459_, v___x_2458_, v___x_2457_, v___x_2456_);
return v___x_2461_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2465_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2466_ = lean_unsigned_to_nat(34u);
v___x_2467_ = lean_unsigned_to_nat(216u);
v___x_2468_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0));
v___x_2469_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2470_ = l_mkPanicMessageWithDecl(v___x_2469_, v___x_2468_, v___x_2467_, v___x_2466_, v___x_2465_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(lean_object* v_c_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v_discr_2478_; lean_object* v_alts_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2548_; 
v_discr_2478_ = lean_ctor_get(v_c_2471_, 2);
v_alts_2479_ = lean_ctor_get(v_c_2471_, 3);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_c_2471_);
if (v_isSharedCheck_2548_ == 0)
{
lean_object* v_unused_2549_; lean_object* v_unused_2550_; 
v_unused_2549_ = lean_ctor_get(v_c_2471_, 1);
lean_dec(v_unused_2549_);
v_unused_2550_ = lean_ctor_get(v_c_2471_, 0);
lean_dec(v_unused_2550_);
v___x_2481_ = v_c_2471_;
v_isShared_2482_ = v_isSharedCheck_2548_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_alts_2479_);
lean_inc(v_discr_2478_);
lean_dec(v_c_2471_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2548_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; uint8_t v___x_2485_; 
v___x_2483_ = lean_array_get_size(v_alts_2479_);
v___x_2484_ = lean_unsigned_to_nat(1u);
v___x_2485_ = lean_nat_dec_eq(v___x_2483_, v___x_2484_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
lean_del_object(v___x_2481_);
lean_dec_ref(v_alts_2479_);
lean_dec(v_discr_2478_);
v___x_2486_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1);
v___x_2487_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2486_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
return v___x_2487_;
}
else
{
uint8_t v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2488_ = 0;
v___x_2489_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2490_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2491_ = lean_unsigned_to_nat(0u);
v___x_2492_ = lean_array_get(v___x_2490_, v_alts_2479_, v___x_2491_);
lean_dec_ref(v_alts_2479_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_params_2493_; lean_object* v_code_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2544_; 
v_params_2493_ = lean_ctor_get(v___x_2492_, 1);
v_code_2494_ = lean_ctor_get(v___x_2492_, 2);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2544_ == 0)
{
lean_object* v_unused_2545_; 
v_unused_2545_ = lean_ctor_get(v___x_2492_, 0);
lean_dec(v_unused_2545_);
v___x_2496_ = v___x_2492_;
v_isShared_2497_ = v_isSharedCheck_2544_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_code_2494_);
lean_inc(v_params_2493_);
lean_dec(v___x_2492_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2544_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2488_, v_params_2493_, v_a_2474_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v_fvarId_2501_; lean_object* v_binderName_2502_; lean_object* v_lctx_2503_; lean_object* v_nextIdx_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2535_; 
lean_dec_ref_known(v___x_2498_, 1);
v___x_2499_ = lean_st_ref_take(v_a_2474_);
v___x_2500_ = lean_array_get(v___x_2489_, v_params_2493_, v___x_2491_);
lean_dec_ref(v_params_2493_);
v_fvarId_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_fvarId_2501_);
v_binderName_2502_ = lean_ctor_get(v___x_2500_, 1);
lean_inc(v_binderName_2502_);
lean_dec(v___x_2500_);
v_lctx_2503_ = lean_ctor_get(v___x_2499_, 0);
v_nextIdx_2504_ = lean_ctor_get(v___x_2499_, 1);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2506_ = v___x_2499_;
v_isShared_2507_ = v_isSharedCheck_2535_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_nextIdx_2504_);
lean_inc(v_lctx_2503_);
lean_dec(v___x_2499_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2535_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2514_; 
v___x_2508_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__4));
v___x_2509_ = lean_box(0);
v___x_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2510_, 0, v_discr_2478_);
v___x_2511_ = lean_mk_empty_array_with_capacity(v___x_2484_);
v___x_2512_ = lean_array_push(v___x_2511_, v___x_2510_);
if (v_isShared_2497_ == 0)
{
lean_ctor_set_tag(v___x_2496_, 3);
lean_ctor_set(v___x_2496_, 2, v___x_2512_);
lean_ctor_set(v___x_2496_, 1, v___x_2509_);
lean_ctor_set(v___x_2496_, 0, v___x_2508_);
v___x_2514_ = v___x_2496_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v___x_2509_);
lean_ctor_set(v_reuseFailAlloc_2534_, 2, v___x_2512_);
v___x_2514_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2515_; lean_object* v___x_2517_; 
v___x_2515_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 3, v___x_2514_);
lean_ctor_set(v___x_2481_, 2, v___x_2515_);
lean_ctor_set(v___x_2481_, 1, v_binderName_2502_);
lean_ctor_set(v___x_2481_, 0, v_fvarId_2501_);
v___x_2517_ = v___x_2481_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_fvarId_2501_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v_binderName_2502_);
lean_ctor_set(v_reuseFailAlloc_2533_, 2, v___x_2515_);
lean_ctor_set(v_reuseFailAlloc_2533_, 3, v___x_2514_);
v___x_2517_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
lean_object* v___x_2518_; lean_object* v___x_2520_; 
lean_inc_ref(v___x_2517_);
v___x_2518_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2488_, v_lctx_2503_, v___x_2517_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v___x_2518_);
v___x_2520_ = v___x_2506_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_nextIdx_2504_);
v___x_2520_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = lean_st_ref_put(v_a_2474_, v___x_2520_);
v___x_2522_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2494_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2531_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2525_ = v___x_2522_;
v_isShared_2526_ = v_isSharedCheck_2531_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2522_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2531_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2517_);
lean_ctor_set(v___x_2527_, 1, v_a_2523_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v___x_2527_);
v___x_2529_ = v___x_2525_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
else
{
lean_dec_ref(v___x_2517_);
return v___x_2522_;
}
}
}
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_del_object(v___x_2496_);
lean_dec_ref(v_code_2494_);
lean_dec_ref(v_params_2493_);
lean_del_object(v___x_2481_);
lean_dec(v_discr_2478_);
v_a_2536_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2498_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2498_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
}
else
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
lean_dec(v___x_2492_);
lean_del_object(v___x_2481_);
lean_dec(v_discr_2478_);
v___x_2546_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5);
v___x_2547_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2546_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
return v___x_2547_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2552_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2553_ = lean_unsigned_to_nat(2u);
v___x_2554_ = lean_unsigned_to_nat(203u);
v___x_2555_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0));
v___x_2556_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2557_ = l_mkPanicMessageWithDecl(v___x_2556_, v___x_2555_, v___x_2554_, v___x_2553_, v___x_2552_);
return v___x_2557_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6(void){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2562_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2563_ = lean_unsigned_to_nat(34u);
v___x_2564_ = lean_unsigned_to_nat(204u);
v___x_2565_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0));
v___x_2566_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2567_ = l_mkPanicMessageWithDecl(v___x_2566_, v___x_2565_, v___x_2564_, v___x_2563_, v___x_2562_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg(lean_object* v_c_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_){
_start:
{
lean_object* v_discr_2575_; lean_object* v_alts_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2645_; 
v_discr_2575_ = lean_ctor_get(v_c_2568_, 2);
v_alts_2576_ = lean_ctor_get(v_c_2568_, 3);
v_isSharedCheck_2645_ = !lean_is_exclusive(v_c_2568_);
if (v_isSharedCheck_2645_ == 0)
{
lean_object* v_unused_2646_; lean_object* v_unused_2647_; 
v_unused_2646_ = lean_ctor_get(v_c_2568_, 1);
lean_dec(v_unused_2646_);
v_unused_2647_ = lean_ctor_get(v_c_2568_, 0);
lean_dec(v_unused_2647_);
v___x_2578_ = v_c_2568_;
v_isShared_2579_ = v_isSharedCheck_2645_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_alts_2576_);
lean_inc(v_discr_2575_);
lean_dec(v_c_2568_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2645_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; uint8_t v___x_2582_; 
v___x_2580_ = lean_array_get_size(v_alts_2576_);
v___x_2581_ = lean_unsigned_to_nat(1u);
v___x_2582_ = lean_nat_dec_eq(v___x_2580_, v___x_2581_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
lean_del_object(v___x_2578_);
lean_dec_ref(v_alts_2576_);
lean_dec(v_discr_2575_);
v___x_2583_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1);
v___x_2584_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2583_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
return v___x_2584_;
}
else
{
uint8_t v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2585_ = 0;
v___x_2586_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2587_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2588_ = lean_unsigned_to_nat(0u);
v___x_2589_ = lean_array_get(v___x_2587_, v_alts_2576_, v___x_2588_);
lean_dec_ref(v_alts_2576_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_params_2590_; lean_object* v_code_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2641_; 
v_params_2590_ = lean_ctor_get(v___x_2589_, 1);
v_code_2591_ = lean_ctor_get(v___x_2589_, 2);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2641_ == 0)
{
lean_object* v_unused_2642_; 
v_unused_2642_ = lean_ctor_get(v___x_2589_, 0);
lean_dec(v_unused_2642_);
v___x_2593_ = v___x_2589_;
v_isShared_2594_ = v_isSharedCheck_2641_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_code_2591_);
lean_inc(v_params_2590_);
lean_dec(v___x_2589_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2641_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; 
v___x_2595_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2585_, v_params_2590_, v_a_2571_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v_fvarId_2598_; lean_object* v_binderName_2599_; lean_object* v_lctx_2600_; lean_object* v_nextIdx_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref_known(v___x_2595_, 1);
v___x_2596_ = lean_st_ref_take(v_a_2571_);
v___x_2597_ = lean_array_get(v___x_2586_, v_params_2590_, v___x_2588_);
lean_dec_ref(v_params_2590_);
v_fvarId_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_fvarId_2598_);
v_binderName_2599_ = lean_ctor_get(v___x_2597_, 1);
lean_inc(v_binderName_2599_);
lean_dec(v___x_2597_);
v_lctx_2600_ = lean_ctor_get(v___x_2596_, 0);
v_nextIdx_2601_ = lean_ctor_get(v___x_2596_, 1);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2603_ = v___x_2596_;
v_isShared_2604_ = v_isSharedCheck_2632_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_nextIdx_2601_);
lean_inc(v_lctx_2600_);
lean_dec(v___x_2596_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2632_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2611_; 
v___x_2605_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__4));
v___x_2606_ = lean_box(0);
v___x_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2607_, 0, v_discr_2575_);
v___x_2608_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_2609_ = lean_array_push(v___x_2608_, v___x_2607_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set_tag(v___x_2593_, 3);
lean_ctor_set(v___x_2593_, 2, v___x_2609_);
lean_ctor_set(v___x_2593_, 1, v___x_2606_);
lean_ctor_set(v___x_2593_, 0, v___x_2605_);
v___x_2611_ = v___x_2593_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2605_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v___x_2606_);
lean_ctor_set(v_reuseFailAlloc_2631_, 2, v___x_2609_);
v___x_2611_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2612_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 3, v___x_2611_);
lean_ctor_set(v___x_2578_, 2, v___x_2612_);
lean_ctor_set(v___x_2578_, 1, v_binderName_2599_);
lean_ctor_set(v___x_2578_, 0, v_fvarId_2598_);
v___x_2614_ = v___x_2578_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_fvarId_2598_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v_binderName_2599_);
lean_ctor_set(v_reuseFailAlloc_2630_, 2, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2630_, 3, v___x_2611_);
v___x_2614_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
lean_object* v___x_2615_; lean_object* v___x_2617_; 
lean_inc_ref(v___x_2614_);
v___x_2615_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2585_, v_lctx_2600_, v___x_2614_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2615_);
v___x_2617_ = v___x_2603_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2615_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v_nextIdx_2601_);
v___x_2617_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = lean_st_ref_put(v_a_2571_, v___x_2617_);
v___x_2619_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2591_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2628_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2622_ = v___x_2619_;
v_isShared_2623_ = v_isSharedCheck_2628_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2628_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2614_);
lean_ctor_set(v___x_2624_, 1, v_a_2620_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 0, v___x_2624_);
v___x_2626_ = v___x_2622_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
else
{
lean_dec_ref(v___x_2614_);
return v___x_2619_;
}
}
}
}
}
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_del_object(v___x_2593_);
lean_dec_ref(v_code_2591_);
lean_dec_ref(v_params_2590_);
lean_del_object(v___x_2578_);
lean_dec(v_discr_2575_);
v_a_2633_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2595_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2595_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
}
else
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
lean_dec(v___x_2589_);
lean_del_object(v___x_2578_);
lean_dec(v_discr_2575_);
v___x_2643_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6);
v___x_2644_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2643_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
return v___x_2644_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2(void){
_start:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2649_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2650_ = lean_unsigned_to_nat(2u);
v___x_2651_ = lean_unsigned_to_nat(192u);
v___x_2652_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0));
v___x_2653_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2654_ = l_mkPanicMessageWithDecl(v___x_2653_, v___x_2652_, v___x_2651_, v___x_2650_, v___x_2649_);
return v___x_2654_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2656_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2657_ = lean_unsigned_to_nat(34u);
v___x_2658_ = lean_unsigned_to_nat(193u);
v___x_2659_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0));
v___x_2660_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2661_ = l_mkPanicMessageWithDecl(v___x_2660_, v___x_2659_, v___x_2658_, v___x_2657_, v___x_2656_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg(lean_object* v_c_2662_, lean_object* v_uintName_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v_discr_2670_; lean_object* v_alts_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2741_; 
v_discr_2670_ = lean_ctor_get(v_c_2662_, 2);
v_alts_2671_ = lean_ctor_get(v_c_2662_, 3);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_c_2662_);
if (v_isSharedCheck_2741_ == 0)
{
lean_object* v_unused_2742_; lean_object* v_unused_2743_; 
v_unused_2742_ = lean_ctor_get(v_c_2662_, 1);
lean_dec(v_unused_2742_);
v_unused_2743_ = lean_ctor_get(v_c_2662_, 0);
lean_dec(v_unused_2743_);
v___x_2673_ = v_c_2662_;
v_isShared_2674_ = v_isSharedCheck_2741_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_alts_2671_);
lean_inc(v_discr_2670_);
lean_dec(v_c_2662_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2741_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___x_2675_ = lean_array_get_size(v_alts_2671_);
v___x_2676_ = lean_unsigned_to_nat(1u);
v___x_2677_ = lean_nat_dec_eq(v___x_2675_, v___x_2676_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
lean_del_object(v___x_2673_);
lean_dec_ref(v_alts_2671_);
lean_dec(v_discr_2670_);
lean_dec(v_uintName_2663_);
v___x_2678_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2);
v___x_2679_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2678_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
return v___x_2679_;
}
else
{
uint8_t v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2680_ = 0;
v___x_2681_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2682_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2683_ = lean_unsigned_to_nat(0u);
v___x_2684_ = lean_array_get(v___x_2682_, v_alts_2671_, v___x_2683_);
lean_dec_ref(v_alts_2671_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_params_2685_; lean_object* v_code_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2737_; 
v_params_2685_ = lean_ctor_get(v___x_2684_, 1);
v_code_2686_ = lean_ctor_get(v___x_2684_, 2);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2737_ == 0)
{
lean_object* v_unused_2738_; 
v_unused_2738_ = lean_ctor_get(v___x_2684_, 0);
lean_dec(v_unused_2738_);
v___x_2688_ = v___x_2684_;
v_isShared_2689_ = v_isSharedCheck_2737_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_code_2686_);
lean_inc(v_params_2685_);
lean_dec(v___x_2684_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2737_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2680_, v_params_2685_, v_a_2666_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v_fvarId_2693_; lean_object* v_binderName_2694_; lean_object* v_lctx_2695_; lean_object* v_nextIdx_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2728_; 
lean_dec_ref_known(v___x_2690_, 1);
v___x_2691_ = lean_st_ref_take(v_a_2666_);
v___x_2692_ = lean_array_get(v___x_2681_, v_params_2685_, v___x_2683_);
lean_dec_ref(v_params_2685_);
v_fvarId_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_fvarId_2693_);
v_binderName_2694_ = lean_ctor_get(v___x_2692_, 1);
lean_inc(v_binderName_2694_);
lean_dec(v___x_2692_);
v_lctx_2695_ = lean_ctor_get(v___x_2691_, 0);
v_nextIdx_2696_ = lean_ctor_get(v___x_2691_, 1);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2698_ = v___x_2691_;
v_isShared_2699_ = v_isSharedCheck_2728_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_nextIdx_2696_);
lean_inc(v_lctx_2695_);
lean_dec(v___x_2691_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2728_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2707_; 
v___x_2700_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4));
v___x_2701_ = l_Lean_Name_str___override(v_uintName_2663_, v___x_2700_);
v___x_2702_ = lean_box(0);
v___x_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2703_, 0, v_discr_2670_);
v___x_2704_ = lean_mk_empty_array_with_capacity(v___x_2676_);
v___x_2705_ = lean_array_push(v___x_2704_, v___x_2703_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set_tag(v___x_2688_, 3);
lean_ctor_set(v___x_2688_, 2, v___x_2705_);
lean_ctor_set(v___x_2688_, 1, v___x_2702_);
lean_ctor_set(v___x_2688_, 0, v___x_2701_);
v___x_2707_ = v___x_2688_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2701_);
lean_ctor_set(v_reuseFailAlloc_2727_, 1, v___x_2702_);
lean_ctor_set(v_reuseFailAlloc_2727_, 2, v___x_2705_);
v___x_2707_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2708_; lean_object* v___x_2710_; 
v___x_2708_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 3, v___x_2707_);
lean_ctor_set(v___x_2673_, 2, v___x_2708_);
lean_ctor_set(v___x_2673_, 1, v_binderName_2694_);
lean_ctor_set(v___x_2673_, 0, v_fvarId_2693_);
v___x_2710_ = v___x_2673_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_fvarId_2693_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_binderName_2694_);
lean_ctor_set(v_reuseFailAlloc_2726_, 2, v___x_2708_);
lean_ctor_set(v_reuseFailAlloc_2726_, 3, v___x_2707_);
v___x_2710_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
lean_object* v___x_2711_; lean_object* v___x_2713_; 
lean_inc_ref(v___x_2710_);
v___x_2711_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2680_, v_lctx_2695_, v___x_2710_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 0, v___x_2711_);
v___x_2713_ = v___x_2698_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2711_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v_nextIdx_2696_);
v___x_2713_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = lean_st_ref_put(v_a_2666_, v___x_2713_);
v___x_2715_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2686_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2724_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2724_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2724_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2720_; lean_object* v___x_2722_; 
v___x_2720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2710_);
lean_ctor_set(v___x_2720_, 1, v_a_2716_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v___x_2720_);
v___x_2722_ = v___x_2718_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
else
{
lean_dec_ref(v___x_2710_);
return v___x_2715_;
}
}
}
}
}
}
else
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2736_; 
lean_del_object(v___x_2688_);
lean_dec_ref(v_code_2686_);
lean_dec_ref(v_params_2685_);
lean_del_object(v___x_2673_);
lean_dec(v_discr_2670_);
lean_dec(v_uintName_2663_);
v_a_2729_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2731_ = v___x_2690_;
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2690_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2734_; 
if (v_isShared_2732_ == 0)
{
v___x_2734_ = v___x_2731_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2729_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
}
else
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
lean_dec(v___x_2684_);
lean_del_object(v___x_2673_);
lean_dec(v_discr_2670_);
lean_dec(v_uintName_2663_);
v___x_2739_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__5);
v___x_2740_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2739_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
return v___x_2740_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2744_ = lean_box(0);
v___x_2745_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0));
v___x_2746_ = l_Lean_mkConst(v___x_2745_, v___x_2744_);
return v___x_2746_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2753_ = lean_box(0);
v___x_2754_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3));
v___x_2755_ = l_Lean_mkConst(v___x_2754_, v___x_2753_);
return v___x_2755_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7(void){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2766_ = lean_box(0);
v___x_2767_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6));
v___x_2768_ = l_Lean_mkConst(v___x_2767_, v___x_2766_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(lean_object* v___x_2801_, size_t v_sz_2802_, size_t v_i_2803_, lean_object* v_bs_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
uint8_t v___x_2811_; 
v___x_2811_ = lean_usize_dec_lt(v_i_2803_, v_sz_2802_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; 
lean_dec(v___x_2801_);
v___x_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2812_, 0, v_bs_2804_);
return v___x_2812_;
}
else
{
lean_object* v_v_2813_; lean_object* v___x_2814_; lean_object* v_bs_x27_2815_; lean_object* v_a_2817_; 
v_v_2813_ = lean_array_uget(v_bs_2804_, v_i_2803_);
v___x_2814_ = lean_unsigned_to_nat(0u);
v_bs_x27_2815_ = lean_array_uset(v_bs_2804_, v_i_2803_, v___x_2814_);
if (lean_obj_tag(v_v_2813_) == 0)
{
lean_object* v_ctorName_2822_; lean_object* v_params_2823_; lean_object* v_code_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2951_; 
v_ctorName_2822_ = lean_ctor_get(v_v_2813_, 0);
v_params_2823_ = lean_ctor_get(v_v_2813_, 1);
v_code_2824_ = lean_ctor_get(v_v_2813_, 2);
v_isSharedCheck_2951_ = !lean_is_exclusive(v_v_2813_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2826_ = v_v_2813_;
v_isShared_2827_ = v_isSharedCheck_2951_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_code_2824_);
lean_inc(v_params_2823_);
lean_inc(v_ctorName_2822_);
lean_dec(v_v_2813_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2951_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
uint8_t v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2828_ = 0;
v___x_2829_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2830_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2828_, v_params_2823_, v___y_2807_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; 
lean_dec_ref_known(v___x_2830_, 1);
v___x_2831_ = lean_box(0);
v___x_2832_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_2833_ = lean_array_get(v___x_2829_, v_params_2823_, v___x_2814_);
lean_dec_ref(v_params_2823_);
v___x_2834_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__1));
v___x_2835_ = lean_name_eq(v_ctorName_2822_, v___x_2834_);
lean_dec(v_ctorName_2822_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; lean_object* v_fvarId_2837_; lean_object* v_binderName_2838_; lean_object* v_lctx_2839_; lean_object* v_nextIdx_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2871_; 
v___x_2836_ = lean_st_ref_take(v___y_2807_);
v_fvarId_2837_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_fvarId_2837_);
v_binderName_2838_ = lean_ctor_get(v___x_2833_, 1);
lean_inc(v_binderName_2838_);
lean_dec(v___x_2833_);
v_lctx_2839_ = lean_ctor_get(v___x_2836_, 0);
v_nextIdx_2840_ = lean_ctor_get(v___x_2836_, 1);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2842_ = v___x_2836_;
v_isShared_2843_ = v_isSharedCheck_2871_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_nextIdx_2840_);
lean_inc(v_lctx_2839_);
lean_dec(v___x_2836_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2871_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2852_; 
v___x_2844_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__3));
v___x_2845_ = lean_unsigned_to_nat(1u);
v___x_2846_ = lean_mk_empty_array_with_capacity(v___x_2845_);
lean_inc(v___x_2801_);
v___x_2847_ = lean_array_push(v___x_2846_, v___x_2801_);
v___x_2848_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2844_);
lean_ctor_set(v___x_2848_, 1, v___x_2831_);
lean_ctor_set(v___x_2848_, 2, v___x_2847_);
v___x_2849_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2849_, 0, v_fvarId_2837_);
lean_ctor_set(v___x_2849_, 1, v_binderName_2838_);
lean_ctor_set(v___x_2849_, 2, v___x_2832_);
lean_ctor_set(v___x_2849_, 3, v___x_2848_);
lean_inc_ref(v___x_2849_);
v___x_2850_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2828_, v_lctx_2839_, v___x_2849_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_2850_);
v___x_2852_ = v___x_2842_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2850_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_nextIdx_2840_);
v___x_2852_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = lean_st_ref_put(v___y_2807_, v___x_2852_);
v___x_2854_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2824_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2860_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2854_, 1);
v___x_2856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__10));
v___x_2857_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2));
v___x_2858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2849_);
lean_ctor_set(v___x_2858_, 1, v_a_2855_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 2, v___x_2858_);
lean_ctor_set(v___x_2826_, 1, v___x_2857_);
lean_ctor_set(v___x_2826_, 0, v___x_2856_);
v___x_2860_ = v___x_2826_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2856_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v___x_2857_);
lean_ctor_set(v_reuseFailAlloc_2861_, 2, v___x_2858_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
v_a_2817_ = v___x_2860_;
goto v___jp_2816_;
}
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
lean_dec_ref_known(v___x_2849_, 4);
lean_del_object(v___x_2826_);
lean_dec_ref(v_bs_x27_2815_);
lean_dec(v___x_2801_);
v_a_2862_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2854_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2854_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
}
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__5));
v___x_2873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__3));
v___x_2874_ = lean_unsigned_to_nat(1u);
v___x_2875_ = lean_mk_empty_array_with_capacity(v___x_2874_);
lean_inc(v___x_2801_);
v___x_2876_ = lean_array_push(v___x_2875_, v___x_2801_);
v___x_2877_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2873_);
lean_ctor_set(v___x_2877_, 1, v___x_2831_);
lean_ctor_set(v___x_2877_, 2, v___x_2876_);
v___x_2878_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2828_, v___x_2872_, v___x_2832_, v___x_2877_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2879_);
lean_dec_ref_known(v___x_2878_, 1);
v___x_2880_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__4));
v___x_2881_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6));
v___x_2882_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2828_, v___x_2880_, v___x_2832_, v___x_2881_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v_fvarId_2884_; lean_object* v_fvarId_2885_; lean_object* v___x_2886_; lean_object* v_fvarId_2887_; lean_object* v_binderName_2888_; lean_object* v_lctx_2889_; lean_object* v_nextIdx_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2926_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref_known(v___x_2882_, 1);
v_fvarId_2884_ = lean_ctor_get(v_a_2879_, 0);
v_fvarId_2885_ = lean_ctor_get(v_a_2883_, 0);
v___x_2886_ = lean_st_ref_take(v___y_2807_);
v_fvarId_2887_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_fvarId_2887_);
v_binderName_2888_ = lean_ctor_get(v___x_2833_, 1);
lean_inc(v_binderName_2888_);
lean_dec(v___x_2833_);
v_lctx_2889_ = lean_ctor_get(v___x_2886_, 0);
v_nextIdx_2890_ = lean_ctor_get(v___x_2886_, 1);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2892_ = v___x_2886_;
v_isShared_2893_ = v_isSharedCheck_2926_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_nextIdx_2890_);
lean_inc(v_lctx_2889_);
lean_dec(v___x_2886_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2926_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2905_; 
v___x_2894_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__8));
lean_inc(v_fvarId_2884_);
v___x_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2895_, 0, v_fvarId_2884_);
lean_inc(v_fvarId_2885_);
v___x_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2896_, 0, v_fvarId_2885_);
v___x_2897_ = lean_unsigned_to_nat(2u);
v___x_2898_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___x_2899_ = lean_array_push(v___x_2898_, v___x_2895_);
v___x_2900_ = lean_array_push(v___x_2899_, v___x_2896_);
v___x_2901_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2894_);
lean_ctor_set(v___x_2901_, 1, v___x_2831_);
lean_ctor_set(v___x_2901_, 2, v___x_2900_);
v___x_2902_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2902_, 0, v_fvarId_2887_);
lean_ctor_set(v___x_2902_, 1, v_binderName_2888_);
lean_ctor_set(v___x_2902_, 2, v___x_2832_);
lean_ctor_set(v___x_2902_, 3, v___x_2901_);
lean_inc_ref(v___x_2902_);
v___x_2903_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2828_, v_lctx_2889_, v___x_2902_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v___x_2903_);
v___x_2905_ = v___x_2892_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2903_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_nextIdx_2890_);
v___x_2905_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2906_ = lean_st_ref_put(v___y_2807_, v___x_2905_);
v___x_2907_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2824_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2915_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2908_);
lean_dec_ref_known(v___x_2907_, 1);
v___x_2909_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1));
v___x_2910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2));
v___x_2911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2902_);
lean_ctor_set(v___x_2911_, 1, v_a_2908_);
v___x_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2912_, 0, v_a_2883_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
v___x_2913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2913_, 0, v_a_2879_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 2, v___x_2913_);
lean_ctor_set(v___x_2826_, 1, v___x_2910_);
lean_ctor_set(v___x_2826_, 0, v___x_2909_);
v___x_2915_ = v___x_2826_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2909_);
lean_ctor_set(v_reuseFailAlloc_2916_, 1, v___x_2910_);
lean_ctor_set(v_reuseFailAlloc_2916_, 2, v___x_2913_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
v_a_2817_ = v___x_2915_;
goto v___jp_2816_;
}
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec_ref_known(v___x_2902_, 4);
lean_dec(v_a_2883_);
lean_dec(v_a_2879_);
lean_del_object(v___x_2826_);
lean_dec_ref(v_bs_x27_2815_);
lean_dec(v___x_2801_);
v_a_2917_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2907_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2907_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec(v_a_2879_);
lean_dec(v___x_2833_);
lean_del_object(v___x_2826_);
lean_dec_ref(v_code_2824_);
lean_dec_ref(v_bs_x27_2815_);
lean_dec(v___x_2801_);
v_a_2927_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2882_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2882_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
else
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
lean_dec(v___x_2833_);
lean_del_object(v___x_2826_);
lean_dec_ref(v_code_2824_);
lean_dec_ref(v_bs_x27_2815_);
lean_dec(v___x_2801_);
v_a_2935_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2878_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2878_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_del_object(v___x_2826_);
lean_dec_ref(v_code_2824_);
lean_dec_ref(v_params_2823_);
lean_dec(v_ctorName_2822_);
lean_dec_ref(v_bs_x27_2815_);
lean_dec(v___x_2801_);
v_a_2943_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2830_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2830_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
}
else
{
lean_object* v_code_2952_; lean_object* v___x_2953_; 
v_code_2952_ = lean_ctor_get(v_v_2813_, 0);
lean_inc_ref(v_code_2952_);
v___x_2953_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2952_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v___x_2955_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2953_, 1);
v___x_2955_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_2813_, v_a_2954_);
v_a_2817_ = v___x_2955_;
goto v___jp_2816_;
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
lean_dec_ref_known(v_v_2813_, 1);
lean_dec_ref(v_bs_x27_2815_);
lean_dec(v___x_2801_);
v_a_2956_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2953_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2953_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
v___jp_2816_:
{
size_t v___x_2818_; size_t v___x_2819_; lean_object* v___x_2820_; 
v___x_2818_ = ((size_t)1ULL);
v___x_2819_ = lean_usize_add(v_i_2803_, v___x_2818_);
v___x_2820_ = lean_array_uset(v_bs_x27_2815_, v_i_2803_, v_a_2817_);
v_i_2803_ = v___x_2819_;
v_bs_2804_ = v___x_2820_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg(lean_object* v_c_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_){
_start:
{
lean_object* v_resultType_2971_; lean_object* v_discr_2972_; lean_object* v_alts_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_3070_; 
v_resultType_2971_ = lean_ctor_get(v_c_2964_, 1);
v_discr_2972_ = lean_ctor_get(v_c_2964_, 2);
v_alts_2973_ = lean_ctor_get(v_c_2964_, 3);
v_isSharedCheck_3070_ = !lean_is_exclusive(v_c_2964_);
if (v_isSharedCheck_3070_ == 0)
{
lean_object* v_unused_3071_; 
v_unused_3071_ = lean_ctor_get(v_c_2964_, 0);
lean_dec(v_unused_3071_);
v___x_2975_ = v_c_2964_;
v_isShared_2976_ = v_isSharedCheck_3070_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_alts_2973_);
lean_inc(v_discr_2972_);
lean_inc(v_resultType_2971_);
lean_dec(v_c_2964_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_3070_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2977_; 
v___x_2977_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_2971_, v_a_2968_, v_a_2969_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; uint8_t v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref_known(v___x_2977_, 1);
v___x_2979_ = 0;
v___x_2980_ = lean_box(0);
v___x_2981_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_2982_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__1));
v___x_2983_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__15));
v___x_2984_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2979_, v___x_2982_, v___x_2981_, v___x_2983_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v_a_2985_; lean_object* v_fvarId_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
lean_inc(v_a_2985_);
lean_dec_ref_known(v___x_2984_, 1);
v_fvarId_2986_ = lean_ctor_get(v_a_2985_, 0);
v___x_2987_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__5));
v___x_2988_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6, &l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6);
v___x_2989_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__8));
lean_inc(v_fvarId_2986_);
v___x_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2990_, 0, v_fvarId_2986_);
v___x_2991_ = lean_unsigned_to_nat(1u);
v___x_2992_ = lean_mk_empty_array_with_capacity(v___x_2991_);
v___x_2993_ = lean_array_push(v___x_2992_, v___x_2990_);
v___x_2994_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2989_);
lean_ctor_set(v___x_2994_, 1, v___x_2980_);
lean_ctor_set(v___x_2994_, 2, v___x_2993_);
v___x_2995_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2979_, v___x_2987_, v___x_2988_, v___x_2994_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v_fvarId_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref_known(v___x_2995_, 1);
v_fvarId_2997_ = lean_ctor_get(v_a_2996_, 0);
v___x_2998_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__10));
v___x_2999_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6));
v___x_3000_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7);
v___x_3001_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12));
v___x_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3002_, 0, v_discr_2972_);
lean_inc(v_fvarId_2997_);
v___x_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3003_, 0, v_fvarId_2997_);
v___x_3004_ = lean_unsigned_to_nat(2u);
v___x_3005_ = lean_mk_empty_array_with_capacity(v___x_3004_);
lean_inc_ref(v___x_3002_);
v___x_3006_ = lean_array_push(v___x_3005_, v___x_3002_);
v___x_3007_ = lean_array_push(v___x_3006_, v___x_3003_);
v___x_3008_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3001_);
lean_ctor_set(v___x_3008_, 1, v___x_2980_);
lean_ctor_set(v___x_3008_, 2, v___x_3007_);
v___x_3009_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2979_, v___x_2998_, v___x_3000_, v___x_3008_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; size_t v_sz_3011_; size_t v___x_3012_; lean_object* v___x_3013_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref_known(v___x_3009_, 1);
v_sz_3011_ = lean_array_size(v_alts_2973_);
v___x_3012_ = ((size_t)0ULL);
v___x_3013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(v___x_3002_, v_sz_3011_, v___x_3012_, v_alts_2973_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3029_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3016_ = v___x_3013_;
v_isShared_3017_ = v_isSharedCheck_3029_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3013_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3029_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v_fvarId_3018_; lean_object* v___x_3020_; 
v_fvarId_3018_ = lean_ctor_get(v_a_3010_, 0);
lean_inc(v_fvarId_3018_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 3, v_a_3014_);
lean_ctor_set(v___x_2975_, 2, v_fvarId_3018_);
lean_ctor_set(v___x_2975_, 1, v_a_2978_);
lean_ctor_set(v___x_2975_, 0, v___x_2999_);
v___x_3020_ = v___x_2975_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_2999_);
lean_ctor_set(v_reuseFailAlloc_3028_, 1, v_a_2978_);
lean_ctor_set(v_reuseFailAlloc_3028_, 2, v_fvarId_3018_);
lean_ctor_set(v_reuseFailAlloc_3028_, 3, v_a_3014_);
v___x_3020_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3026_; 
v___x_3021_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3020_);
v___x_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3022_, 0, v_a_3010_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
v___x_3023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3023_, 0, v_a_2996_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
v___x_3024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3024_, 0, v_a_2985_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3024_);
v___x_3026_ = v___x_3016_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3024_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_dec(v_a_3010_);
lean_dec(v_a_2996_);
lean_dec(v_a_2985_);
lean_dec(v_a_2978_);
lean_del_object(v___x_2975_);
v_a_3030_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_3013_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_3013_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec_ref_known(v___x_3002_, 1);
lean_dec(v_a_2996_);
lean_dec(v_a_2985_);
lean_dec(v_a_2978_);
lean_del_object(v___x_2975_);
lean_dec_ref(v_alts_2973_);
v_a_3038_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3009_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3009_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
else
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
lean_dec(v_a_2985_);
lean_dec(v_a_2978_);
lean_del_object(v___x_2975_);
lean_dec_ref(v_alts_2973_);
lean_dec(v_discr_2972_);
v_a_3046_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___x_2995_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_2995_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_dec(v_a_2978_);
lean_del_object(v___x_2975_);
lean_dec_ref(v_alts_2973_);
lean_dec(v_discr_2972_);
v_a_3054_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_2984_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_2984_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_del_object(v___x_2975_);
lean_dec_ref(v_alts_2973_);
lean_dec(v_discr_2972_);
v_a_3062_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_2977_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_2977_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_a_3062_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(lean_object* v___x_3081_, size_t v_sz_3082_, size_t v_i_3083_, lean_object* v_bs_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
uint8_t v___x_3091_; 
v___x_3091_ = lean_usize_dec_lt(v_i_3083_, v_sz_3082_);
if (v___x_3091_ == 0)
{
lean_object* v___x_3092_; 
lean_dec(v___x_3081_);
v___x_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3092_, 0, v_bs_3084_);
return v___x_3092_;
}
else
{
lean_object* v_v_3093_; lean_object* v___x_3094_; lean_object* v_bs_x27_3095_; lean_object* v_a_3097_; 
v_v_3093_ = lean_array_uget(v_bs_3084_, v_i_3083_);
v___x_3094_ = lean_unsigned_to_nat(0u);
v_bs_x27_3095_ = lean_array_uset(v_bs_3084_, v_i_3083_, v___x_3094_);
if (lean_obj_tag(v_v_3093_) == 0)
{
lean_object* v_ctorName_3102_; lean_object* v_params_3103_; lean_object* v_code_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3191_; 
v_ctorName_3102_ = lean_ctor_get(v_v_3093_, 0);
v_params_3103_ = lean_ctor_get(v_v_3093_, 1);
v_code_3104_ = lean_ctor_get(v_v_3093_, 2);
v_isSharedCheck_3191_ = !lean_is_exclusive(v_v_3093_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3106_ = v_v_3093_;
v_isShared_3107_ = v_isSharedCheck_3191_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_code_3104_);
lean_inc(v_params_3103_);
lean_inc(v_ctorName_3102_);
lean_dec(v_v_3093_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3191_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
uint8_t v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3108_ = 0;
v___x_3109_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_3110_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3108_, v_params_3103_, v___y_3087_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v___x_3111_; uint8_t v___x_3112_; 
lean_dec_ref_known(v___x_3110_, 1);
v___x_3111_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__9));
v___x_3112_ = lean_name_eq(v_ctorName_3102_, v___x_3111_);
lean_dec(v_ctorName_3102_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; 
lean_dec_ref(v_params_3103_);
v___x_3113_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3104_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3118_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3114_);
lean_dec_ref_known(v___x_3113_, 1);
v___x_3115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1));
v___x_3116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2));
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 2, v_a_3114_);
lean_ctor_set(v___x_3106_, 1, v___x_3116_);
lean_ctor_set(v___x_3106_, 0, v___x_3115_);
v___x_3118_ = v___x_3106_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3115_);
lean_ctor_set(v_reuseFailAlloc_3119_, 1, v___x_3116_);
lean_ctor_set(v_reuseFailAlloc_3119_, 2, v_a_3114_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
v_a_3097_ = v___x_3118_;
goto v___jp_3096_;
}
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_del_object(v___x_3106_);
lean_dec_ref(v_bs_x27_3095_);
lean_dec(v___x_3081_);
v_a_3120_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3113_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3113_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
else
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3128_ = lean_box(0);
v___x_3129_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3130_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__4));
v___x_3131_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6));
v___x_3132_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3108_, v___x_3130_, v___x_3129_, v___x_3131_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; lean_object* v_fvarId_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v_fvarId_3137_; lean_object* v_binderName_3138_; lean_object* v_lctx_3139_; lean_object* v_nextIdx_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3174_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_a_3133_);
lean_dec_ref_known(v___x_3132_, 1);
v_fvarId_3134_ = lean_ctor_get(v_a_3133_, 0);
v___x_3135_ = lean_st_ref_take(v___y_3087_);
v___x_3136_ = lean_array_get(v___x_3109_, v_params_3103_, v___x_3094_);
lean_dec_ref(v_params_3103_);
v_fvarId_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc(v_fvarId_3137_);
v_binderName_3138_ = lean_ctor_get(v___x_3136_, 1);
lean_inc(v_binderName_3138_);
lean_dec(v___x_3136_);
v_lctx_3139_ = lean_ctor_get(v___x_3135_, 0);
v_nextIdx_3140_ = lean_ctor_get(v___x_3135_, 1);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3142_ = v___x_3135_;
v_isShared_3143_ = v_isSharedCheck_3174_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_nextIdx_3140_);
lean_inc(v_lctx_3139_);
lean_dec(v___x_3135_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3174_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3154_; 
v___x_3144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__8));
lean_inc(v_fvarId_3134_);
v___x_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3145_, 0, v_fvarId_3134_);
v___x_3146_ = lean_unsigned_to_nat(2u);
v___x_3147_ = lean_mk_empty_array_with_capacity(v___x_3146_);
lean_inc(v___x_3081_);
v___x_3148_ = lean_array_push(v___x_3147_, v___x_3081_);
v___x_3149_ = lean_array_push(v___x_3148_, v___x_3145_);
v___x_3150_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3144_);
lean_ctor_set(v___x_3150_, 1, v___x_3128_);
lean_ctor_set(v___x_3150_, 2, v___x_3149_);
v___x_3151_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3151_, 0, v_fvarId_3137_);
lean_ctor_set(v___x_3151_, 1, v_binderName_3138_);
lean_ctor_set(v___x_3151_, 2, v___x_3129_);
lean_ctor_set(v___x_3151_, 3, v___x_3150_);
lean_inc_ref(v___x_3151_);
v___x_3152_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3108_, v_lctx_3139_, v___x_3151_);
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 0, v___x_3152_);
v___x_3154_ = v___x_3142_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_3152_);
lean_ctor_set(v_reuseFailAlloc_3173_, 1, v_nextIdx_3140_);
v___x_3154_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3155_ = lean_st_ref_put(v___y_3087_, v___x_3154_);
v___x_3156_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3104_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v_a_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3163_; 
v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
lean_inc(v_a_3157_);
lean_dec_ref_known(v___x_3156_, 1);
v___x_3158_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__10));
v___x_3159_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2));
v___x_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3151_);
lean_ctor_set(v___x_3160_, 1, v_a_3157_);
v___x_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3161_, 0, v_a_3133_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 2, v___x_3161_);
lean_ctor_set(v___x_3106_, 1, v___x_3159_);
lean_ctor_set(v___x_3106_, 0, v___x_3158_);
v___x_3163_ = v___x_3106_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3158_);
lean_ctor_set(v_reuseFailAlloc_3164_, 1, v___x_3159_);
lean_ctor_set(v_reuseFailAlloc_3164_, 2, v___x_3161_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
v_a_3097_ = v___x_3163_;
goto v___jp_3096_;
}
}
else
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
lean_dec_ref_known(v___x_3151_, 4);
lean_dec(v_a_3133_);
lean_del_object(v___x_3106_);
lean_dec_ref(v_bs_x27_3095_);
lean_dec(v___x_3081_);
v_a_3165_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3156_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3156_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
if (v_isShared_3168_ == 0)
{
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3165_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
}
}
}
else
{
lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3182_; 
lean_del_object(v___x_3106_);
lean_dec_ref(v_code_3104_);
lean_dec_ref(v_params_3103_);
lean_dec_ref(v_bs_x27_3095_);
lean_dec(v___x_3081_);
v_a_3175_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3177_ = v___x_3132_;
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3132_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3180_; 
if (v_isShared_3178_ == 0)
{
v___x_3180_ = v___x_3177_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_a_3175_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
}
else
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
lean_del_object(v___x_3106_);
lean_dec_ref(v_code_3104_);
lean_dec_ref(v_params_3103_);
lean_dec(v_ctorName_3102_);
lean_dec_ref(v_bs_x27_3095_);
lean_dec(v___x_3081_);
v_a_3183_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v___x_3110_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3110_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
}
else
{
lean_object* v_code_3192_; lean_object* v___x_3193_; 
v_code_3192_ = lean_ctor_get(v_v_3093_, 0);
lean_inc_ref(v_code_3192_);
v___x_3193_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3192_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_a_3194_; lean_object* v___x_3195_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc(v_a_3194_);
lean_dec_ref_known(v___x_3193_, 1);
v___x_3195_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_3093_, v_a_3194_);
v_a_3097_ = v___x_3195_;
goto v___jp_3096_;
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
lean_dec_ref_known(v_v_3093_, 1);
lean_dec_ref(v_bs_x27_3095_);
lean_dec(v___x_3081_);
v_a_3196_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3193_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3193_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
v___jp_3096_:
{
size_t v___x_3098_; size_t v___x_3099_; lean_object* v___x_3100_; 
v___x_3098_ = ((size_t)1ULL);
v___x_3099_ = lean_usize_add(v_i_3083_, v___x_3098_);
v___x_3100_ = lean_array_uset(v_bs_x27_3095_, v_i_3083_, v_a_3097_);
v_i_3083_ = v___x_3099_;
v_bs_3084_ = v___x_3100_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg(lean_object* v_c_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_){
_start:
{
lean_object* v_resultType_3211_; lean_object* v_discr_3212_; lean_object* v_alts_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3290_; 
v_resultType_3211_ = lean_ctor_get(v_c_3204_, 1);
v_discr_3212_ = lean_ctor_get(v_c_3204_, 2);
v_alts_3213_ = lean_ctor_get(v_c_3204_, 3);
v_isSharedCheck_3290_ = !lean_is_exclusive(v_c_3204_);
if (v_isSharedCheck_3290_ == 0)
{
lean_object* v_unused_3291_; 
v_unused_3291_ = lean_ctor_get(v_c_3204_, 0);
lean_dec(v_unused_3291_);
v___x_3215_ = v_c_3204_;
v_isShared_3216_ = v_isSharedCheck_3290_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_alts_3213_);
lean_inc(v_discr_3212_);
lean_inc(v_resultType_3211_);
lean_dec(v_c_3204_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3290_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3217_; 
v___x_3217_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3211_, v_a_3208_, v_a_3209_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; uint8_t v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref_known(v___x_3217_, 1);
v___x_3219_ = 0;
v___x_3220_ = lean_box(0);
v___x_3221_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3222_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__2));
v___x_3223_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__15));
v___x_3224_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3219_, v___x_3222_, v___x_3221_, v___x_3223_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; lean_object* v_fvarId_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3225_);
lean_dec_ref_known(v___x_3224_, 1);
v_fvarId_3226_ = lean_ctor_get(v_a_3225_, 0);
v___x_3227_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__4));
v___x_3228_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6));
v___x_3229_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7);
v___x_3230_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__9));
v___x_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3231_, 0, v_discr_3212_);
lean_inc(v_fvarId_3226_);
v___x_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3232_, 0, v_fvarId_3226_);
v___x_3233_ = lean_unsigned_to_nat(2u);
v___x_3234_ = lean_mk_empty_array_with_capacity(v___x_3233_);
lean_inc_ref(v___x_3231_);
v___x_3235_ = lean_array_push(v___x_3234_, v___x_3231_);
v___x_3236_ = lean_array_push(v___x_3235_, v___x_3232_);
v___x_3237_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3230_);
lean_ctor_set(v___x_3237_, 1, v___x_3220_);
lean_ctor_set(v___x_3237_, 2, v___x_3236_);
v___x_3238_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3219_, v___x_3227_, v___x_3229_, v___x_3237_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; size_t v_sz_3240_; size_t v___x_3241_; lean_object* v___x_3242_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
lean_inc(v_a_3239_);
lean_dec_ref_known(v___x_3238_, 1);
v_sz_3240_ = lean_array_size(v_alts_3213_);
v___x_3241_ = ((size_t)0ULL);
v___x_3242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(v___x_3231_, v_sz_3240_, v___x_3241_, v_alts_3213_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3257_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3245_ = v___x_3242_;
v_isShared_3246_ = v_isSharedCheck_3257_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3242_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3257_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v_fvarId_3247_; lean_object* v___x_3249_; 
v_fvarId_3247_ = lean_ctor_get(v_a_3239_, 0);
lean_inc(v_fvarId_3247_);
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 3, v_a_3243_);
lean_ctor_set(v___x_3215_, 2, v_fvarId_3247_);
lean_ctor_set(v___x_3215_, 1, v_a_3218_);
lean_ctor_set(v___x_3215_, 0, v___x_3228_);
v___x_3249_ = v___x_3215_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3228_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_a_3218_);
lean_ctor_set(v_reuseFailAlloc_3256_, 2, v_fvarId_3247_);
lean_ctor_set(v_reuseFailAlloc_3256_, 3, v_a_3243_);
v___x_3249_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3254_; 
v___x_3250_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3249_);
v___x_3251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3251_, 0, v_a_3239_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3252_, 0, v_a_3225_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 0, v___x_3252_);
v___x_3254_ = v___x_3245_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3252_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec(v_a_3239_);
lean_dec(v_a_3225_);
lean_dec(v_a_3218_);
lean_del_object(v___x_3215_);
v_a_3258_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3242_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3242_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
lean_dec_ref_known(v___x_3231_, 1);
lean_dec(v_a_3225_);
lean_dec(v_a_3218_);
lean_del_object(v___x_3215_);
lean_dec_ref(v_alts_3213_);
v_a_3266_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_3238_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3238_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
else
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
lean_dec(v_a_3218_);
lean_del_object(v___x_3215_);
lean_dec_ref(v_alts_3213_);
lean_dec(v_discr_3212_);
v_a_3274_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___x_3224_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3224_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
else
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
lean_del_object(v___x_3215_);
lean_dec_ref(v_alts_3213_);
lean_dec(v_discr_3212_);
v_a_3282_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3284_ = v___x_3217_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3217_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3282_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono(lean_object* v_code_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_){
_start:
{
lean_object* v_decl_3300_; lean_object* v_k_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; 
switch(lean_obj_tag(v_code_3292_))
{
case 0:
{
lean_object* v_decl_3416_; lean_object* v_k_3417_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v_value_3473_; 
v_decl_3416_ = lean_ctor_get(v_code_3292_, 0);
v_k_3417_ = lean_ctor_get(v_code_3292_, 1);
v_value_3473_ = lean_ctor_get(v_decl_3416_, 3);
lean_inc(v_value_3473_);
if (lean_obj_tag(v_value_3473_) == 3)
{
lean_object* v_declName_3474_; 
v_declName_3474_ = lean_ctor_get(v_value_3473_, 0);
lean_inc(v_declName_3474_);
if (lean_obj_tag(v_declName_3474_) == 1)
{
lean_object* v_pre_3475_; 
v_pre_3475_ = lean_ctor_get(v_declName_3474_, 0);
lean_inc(v_pre_3475_);
if (lean_obj_tag(v_pre_3475_) == 1)
{
lean_object* v_pre_3476_; 
v_pre_3476_ = lean_ctor_get(v_pre_3475_, 0);
if (lean_obj_tag(v_pre_3476_) == 0)
{
lean_object* v_type_3477_; lean_object* v_args_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3548_; 
v_type_3477_ = lean_ctor_get(v_decl_3416_, 2);
v_args_3478_ = lean_ctor_get(v_value_3473_, 2);
v_isSharedCheck_3548_ = !lean_is_exclusive(v_value_3473_);
if (v_isSharedCheck_3548_ == 0)
{
lean_object* v_unused_3549_; lean_object* v_unused_3550_; 
v_unused_3549_ = lean_ctor_get(v_value_3473_, 1);
lean_dec(v_unused_3549_);
v_unused_3550_ = lean_ctor_get(v_value_3473_, 0);
lean_dec(v_unused_3550_);
v___x_3480_ = v_value_3473_;
v_isShared_3481_ = v_isSharedCheck_3548_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_args_3478_);
lean_dec(v_value_3473_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3548_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v_str_3482_; lean_object* v_str_3483_; lean_object* v___x_3484_; uint8_t v___x_3485_; 
v_str_3482_ = lean_ctor_get(v_declName_3474_, 1);
lean_inc_ref(v_str_3482_);
lean_dec_ref_known(v_declName_3474_, 2);
v_str_3483_ = lean_ctor_get(v_pre_3475_, 1);
lean_inc_ref(v_str_3483_);
lean_dec_ref_known(v_pre_3475_, 2);
v___x_3484_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__5));
v___x_3485_ = lean_string_dec_eq(v_str_3483_, v___x_3484_);
lean_dec_ref(v_str_3483_);
if (v___x_3485_ == 0)
{
lean_dec_ref(v_str_3482_);
lean_del_object(v___x_3480_);
lean_dec_ref(v_args_3478_);
v___y_3419_ = v_a_3293_;
v___y_3420_ = v_a_3294_;
v___y_3421_ = v_a_3295_;
v___y_3422_ = v_a_3296_;
v___y_3423_ = v_a_3297_;
goto v___jp_3418_;
}
else
{
lean_object* v___x_3486_; uint8_t v___x_3487_; 
v___x_3486_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__8));
v___x_3487_ = lean_string_dec_eq(v_str_3482_, v___x_3486_);
lean_dec_ref(v_str_3482_);
if (v___x_3487_ == 0)
{
lean_del_object(v___x_3480_);
lean_dec_ref(v_args_3478_);
v___y_3419_ = v_a_3293_;
v___y_3420_ = v_a_3294_;
v___y_3421_ = v_a_3295_;
v___y_3422_ = v_a_3296_;
v___y_3423_ = v_a_3297_;
goto v___jp_3418_;
}
else
{
lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3545_; 
lean_inc_ref(v_type_3477_);
lean_inc_ref(v_k_3417_);
lean_inc_ref(v_decl_3416_);
v_isSharedCheck_3545_ = !lean_is_exclusive(v_code_3292_);
if (v_isSharedCheck_3545_ == 0)
{
lean_object* v_unused_3546_; lean_object* v_unused_3547_; 
v_unused_3546_ = lean_ctor_get(v_code_3292_, 1);
lean_dec(v_unused_3546_);
v_unused_3547_ = lean_ctor_get(v_code_3292_, 0);
lean_dec(v_unused_3547_);
v___x_3489_ = v_code_3292_;
v_isShared_3490_ = v_isSharedCheck_3545_;
goto v_resetjp_3488_;
}
else
{
lean_dec(v_code_3292_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3545_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; uint8_t v___x_3493_; 
v___x_3491_ = lean_array_get_size(v_args_3478_);
v___x_3492_ = lean_unsigned_to_nat(1u);
v___x_3493_ = lean_nat_dec_eq(v___x_3491_, v___x_3492_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
lean_del_object(v___x_3489_);
lean_del_object(v___x_3480_);
lean_dec_ref(v_args_3478_);
lean_dec_ref(v_type_3477_);
lean_dec_ref(v_k_3417_);
lean_dec_ref(v_decl_3416_);
v___x_3494_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__5, &l_Lean_Compiler_LCNF_Code_toMono___closed__5_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__5);
v___x_3495_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3494_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
return v___x_3495_;
}
else
{
uint8_t v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3496_ = 0;
v___x_3497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6));
v___x_3498_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3));
v___x_3499_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_3496_, v___x_3497_, v___x_3498_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v_fvarId_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3512_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3500_);
lean_dec_ref_known(v___x_3499_, 1);
v_fvarId_3501_ = lean_ctor_get(v_a_3500_, 0);
v___x_3502_ = lean_unsigned_to_nat(0u);
v___x_3503_ = lean_array_fget(v_args_3478_, v___x_3502_);
lean_dec_ref(v_args_3478_);
v___x_3504_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__7));
v___x_3505_ = lean_box(0);
lean_inc(v_fvarId_3501_);
v___x_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3506_, 0, v_fvarId_3501_);
v___x_3507_ = lean_unsigned_to_nat(2u);
v___x_3508_ = lean_mk_empty_array_with_capacity(v___x_3507_);
v___x_3509_ = lean_array_push(v___x_3508_, v___x_3503_);
v___x_3510_ = lean_array_push(v___x_3509_, v___x_3506_);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 2, v___x_3510_);
lean_ctor_set(v___x_3480_, 1, v___x_3505_);
lean_ctor_set(v___x_3480_, 0, v___x_3504_);
v___x_3512_ = v___x_3480_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3504_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v___x_3505_);
lean_ctor_set(v_reuseFailAlloc_3536_, 2, v___x_3510_);
v___x_3512_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
lean_object* v___x_3513_; 
v___x_3513_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_3496_, v_decl_3416_, v_type_3477_, v___x_3512_, v_a_3295_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___x_3513_, 1);
v___x_3515_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3417_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3527_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3518_ = v___x_3515_;
v_isShared_3519_ = v_isSharedCheck_3527_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3515_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3527_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 1, v_a_3516_);
lean_ctor_set(v___x_3489_, 0, v_a_3514_);
v___x_3521_ = v___x_3489_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3514_);
lean_ctor_set(v_reuseFailAlloc_3526_, 1, v_a_3516_);
v___x_3521_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
lean_object* v___x_3522_; lean_object* v___x_3524_; 
v___x_3522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3522_, 0, v_a_3500_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v___x_3522_);
v___x_3524_ = v___x_3518_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3522_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
else
{
lean_dec(v_a_3514_);
lean_dec(v_a_3500_);
lean_del_object(v___x_3489_);
return v___x_3515_;
}
}
else
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
lean_dec(v_a_3500_);
lean_del_object(v___x_3489_);
lean_dec_ref(v_k_3417_);
v_a_3528_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_3513_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3513_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3528_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
}
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
lean_del_object(v___x_3489_);
lean_del_object(v___x_3480_);
lean_dec_ref(v_args_3478_);
lean_dec_ref(v_type_3477_);
lean_dec_ref(v_k_3417_);
lean_dec_ref(v_decl_3416_);
v_a_3537_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3499_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3499_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
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
lean_dec_ref_known(v_pre_3475_, 2);
lean_dec_ref_known(v_declName_3474_, 2);
lean_dec_ref_known(v_value_3473_, 3);
v___y_3419_ = v_a_3293_;
v___y_3420_ = v_a_3294_;
v___y_3421_ = v_a_3295_;
v___y_3422_ = v_a_3296_;
v___y_3423_ = v_a_3297_;
goto v___jp_3418_;
}
}
else
{
lean_dec_ref_known(v_declName_3474_, 2);
lean_dec(v_pre_3475_);
lean_dec_ref_known(v_value_3473_, 3);
v___y_3419_ = v_a_3293_;
v___y_3420_ = v_a_3294_;
v___y_3421_ = v_a_3295_;
v___y_3422_ = v_a_3296_;
v___y_3423_ = v_a_3297_;
goto v___jp_3418_;
}
}
else
{
lean_dec(v_declName_3474_);
lean_dec_ref_known(v_value_3473_, 3);
v___y_3419_ = v_a_3293_;
v___y_3420_ = v_a_3294_;
v___y_3421_ = v_a_3295_;
v___y_3422_ = v_a_3296_;
v___y_3423_ = v_a_3297_;
goto v___jp_3418_;
}
}
else
{
lean_dec(v_value_3473_);
v___y_3419_ = v_a_3293_;
v___y_3420_ = v_a_3294_;
v___y_3421_ = v_a_3295_;
v___y_3422_ = v_a_3296_;
v___y_3423_ = v_a_3297_;
goto v___jp_3418_;
}
v___jp_3418_:
{
lean_object* v___x_3424_; 
lean_inc_ref(v_decl_3416_);
v___x_3424_ = l_Lean_Compiler_LCNF_LetDecl_toMono(v_decl_3416_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; lean_object* v___x_3426_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref_known(v___x_3424_, 1);
lean_inc_ref(v_k_3417_);
v___x_3426_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3417_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3464_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3429_ = v___x_3426_;
v_isShared_3430_ = v_isSharedCheck_3464_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3426_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3464_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
size_t v___x_3431_; size_t v___x_3432_; uint8_t v___x_3433_; 
v___x_3431_ = lean_ptr_addr(v_k_3417_);
v___x_3432_ = lean_ptr_addr(v_a_3427_);
v___x_3433_ = lean_usize_dec_eq(v___x_3431_, v___x_3432_);
if (v___x_3433_ == 0)
{
lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3443_; 
v_isSharedCheck_3443_ = !lean_is_exclusive(v_code_3292_);
if (v_isSharedCheck_3443_ == 0)
{
lean_object* v_unused_3444_; lean_object* v_unused_3445_; 
v_unused_3444_ = lean_ctor_get(v_code_3292_, 1);
lean_dec(v_unused_3444_);
v_unused_3445_ = lean_ctor_get(v_code_3292_, 0);
lean_dec(v_unused_3445_);
v___x_3435_ = v_code_3292_;
v_isShared_3436_ = v_isSharedCheck_3443_;
goto v_resetjp_3434_;
}
else
{
lean_dec(v_code_3292_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3443_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 1, v_a_3427_);
lean_ctor_set(v___x_3435_, 0, v_a_3425_);
v___x_3438_ = v___x_3435_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3425_);
lean_ctor_set(v_reuseFailAlloc_3442_, 1, v_a_3427_);
v___x_3438_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
lean_object* v___x_3440_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3438_);
v___x_3440_ = v___x_3429_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3438_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
else
{
size_t v___x_3446_; size_t v___x_3447_; uint8_t v___x_3448_; 
v___x_3446_ = lean_ptr_addr(v_decl_3416_);
v___x_3447_ = lean_ptr_addr(v_a_3425_);
v___x_3448_ = lean_usize_dec_eq(v___x_3446_, v___x_3447_);
if (v___x_3448_ == 0)
{
lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3458_; 
v_isSharedCheck_3458_ = !lean_is_exclusive(v_code_3292_);
if (v_isSharedCheck_3458_ == 0)
{
lean_object* v_unused_3459_; lean_object* v_unused_3460_; 
v_unused_3459_ = lean_ctor_get(v_code_3292_, 1);
lean_dec(v_unused_3459_);
v_unused_3460_ = lean_ctor_get(v_code_3292_, 0);
lean_dec(v_unused_3460_);
v___x_3450_ = v_code_3292_;
v_isShared_3451_ = v_isSharedCheck_3458_;
goto v_resetjp_3449_;
}
else
{
lean_dec(v_code_3292_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3458_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 1, v_a_3427_);
lean_ctor_set(v___x_3450_, 0, v_a_3425_);
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3425_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_a_3427_);
v___x_3453_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
lean_object* v___x_3455_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3453_);
v___x_3455_ = v___x_3429_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
else
{
lean_object* v___x_3462_; 
lean_dec(v_a_3427_);
lean_dec(v_a_3425_);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v_code_3292_);
v___x_3462_ = v___x_3429_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_code_3292_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
}
else
{
lean_dec(v_a_3425_);
lean_dec_ref_known(v_code_3292_, 2);
return v___x_3426_;
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_dec_ref_known(v_code_3292_, 2);
v_a_3465_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3424_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3424_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_3551_; lean_object* v_args_3552_; size_t v_sz_3553_; size_t v___x_3554_; lean_object* v___x_3555_; 
v_fvarId_3551_ = lean_ctor_get(v_code_3292_, 0);
v_args_3552_ = lean_ctor_get(v_code_3292_, 1);
v_sz_3553_ = lean_array_size(v_args_3552_);
v___x_3554_ = ((size_t)0ULL);
lean_inc_ref(v_args_3552_);
v___x_3555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_3553_, v___x_3554_, v_args_3552_, v_a_3293_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3581_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3558_ = v___x_3555_;
v_isShared_3559_ = v_isSharedCheck_3581_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3555_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3581_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
uint8_t v___y_3561_; uint8_t v___x_3577_; 
v___x_3577_ = l_Lean_instBEqFVarId_beq(v_fvarId_3551_, v_fvarId_3551_);
if (v___x_3577_ == 0)
{
v___y_3561_ = v___x_3577_;
goto v___jp_3560_;
}
else
{
size_t v___x_3578_; size_t v___x_3579_; uint8_t v___x_3580_; 
v___x_3578_ = lean_ptr_addr(v_args_3552_);
v___x_3579_ = lean_ptr_addr(v_a_3556_);
v___x_3580_ = lean_usize_dec_eq(v___x_3578_, v___x_3579_);
v___y_3561_ = v___x_3580_;
goto v___jp_3560_;
}
v___jp_3560_:
{
if (v___y_3561_ == 0)
{
lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3571_; 
lean_inc(v_fvarId_3551_);
v_isSharedCheck_3571_ = !lean_is_exclusive(v_code_3292_);
if (v_isSharedCheck_3571_ == 0)
{
lean_object* v_unused_3572_; lean_object* v_unused_3573_; 
v_unused_3572_ = lean_ctor_get(v_code_3292_, 1);
lean_dec(v_unused_3572_);
v_unused_3573_ = lean_ctor_get(v_code_3292_, 0);
lean_dec(v_unused_3573_);
v___x_3563_ = v_code_3292_;
v_isShared_3564_ = v_isSharedCheck_3571_;
goto v_resetjp_3562_;
}
else
{
lean_dec(v_code_3292_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3571_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 1, v_a_3556_);
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_fvarId_3551_);
lean_ctor_set(v_reuseFailAlloc_3570_, 1, v_a_3556_);
v___x_3566_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
lean_object* v___x_3568_; 
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 0, v___x_3566_);
v___x_3568_ = v___x_3558_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3566_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
else
{
lean_object* v___x_3575_; 
lean_dec(v_a_3556_);
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 0, v_code_3292_);
v___x_3575_ = v___x_3558_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_code_3292_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
}
else
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
lean_dec_ref_known(v_code_3292_, 2);
v_a_3582_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v___x_3555_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3555_);
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
case 4:
{
lean_object* v_cases_3590_; lean_object* v_typeName_3591_; lean_object* v_resultType_3592_; lean_object* v_discr_3593_; lean_object* v_alts_3594_; lean_object* v___x_3595_; uint8_t v___x_3596_; 
v_cases_3590_ = lean_ctor_get(v_code_3292_, 0);
lean_inc_ref(v_cases_3590_);
v_typeName_3591_ = lean_ctor_get(v_cases_3590_, 0);
v_resultType_3592_ = lean_ctor_get(v_cases_3590_, 1);
v_discr_3593_ = lean_ctor_get(v_cases_3590_, 2);
v_alts_3594_ = lean_ctor_get(v_cases_3590_, 3);
v___x_3595_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0));
v___x_3596_ = lean_name_eq(v_typeName_3591_, v___x_3595_);
if (v___x_3596_ == 0)
{
lean_object* v___x_3597_; uint8_t v___x_3598_; 
v___x_3597_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3));
v___x_3598_ = lean_name_eq(v_typeName_3591_, v___x_3597_);
if (v___x_3598_ == 0)
{
lean_object* v___x_3599_; uint8_t v___x_3600_; 
v___x_3599_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__9));
v___x_3600_ = lean_name_eq(v_typeName_3591_, v___x_3599_);
if (v___x_3600_ == 0)
{
lean_object* v___x_3601_; uint8_t v___x_3602_; 
v___x_3601_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__11));
v___x_3602_ = lean_name_eq(v_typeName_3591_, v___x_3601_);
if (v___x_3602_ == 0)
{
lean_object* v___x_3603_; uint8_t v___x_3604_; 
v___x_3603_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__13));
v___x_3604_ = lean_name_eq(v_typeName_3591_, v___x_3603_);
if (v___x_3604_ == 0)
{
lean_object* v___x_3605_; uint8_t v___x_3606_; 
v___x_3605_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__15));
v___x_3606_ = lean_name_eq(v_typeName_3591_, v___x_3605_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; uint8_t v___x_3608_; 
v___x_3607_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__16));
v___x_3608_ = lean_name_eq(v_typeName_3591_, v___x_3607_);
if (v___x_3608_ == 0)
{
lean_object* v___x_3609_; uint8_t v___x_3610_; 
v___x_3609_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__17));
v___x_3610_ = lean_name_eq(v_typeName_3591_, v___x_3609_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3611_; uint8_t v___x_3612_; 
v___x_3611_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__18));
v___x_3612_ = lean_name_eq(v_typeName_3591_, v___x_3611_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3613_; uint8_t v___x_3614_; 
v___x_3613_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__19));
v___x_3614_ = lean_name_eq(v_typeName_3591_, v___x_3613_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3615_; uint8_t v___x_3616_; 
v___x_3615_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__20));
v___x_3616_ = lean_name_eq(v_typeName_3591_, v___x_3615_);
if (v___x_3616_ == 0)
{
lean_object* v___x_3617_; uint8_t v___x_3618_; 
v___x_3617_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__21));
v___x_3618_ = lean_name_eq(v_typeName_3591_, v___x_3617_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3619_; uint8_t v___x_3620_; 
v___x_3619_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__22));
v___x_3620_ = lean_name_eq(v_typeName_3591_, v___x_3619_);
if (v___x_3620_ == 0)
{
lean_object* v___x_3621_; uint8_t v___x_3622_; 
v___x_3621_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__23));
v___x_3622_ = lean_name_eq(v_typeName_3591_, v___x_3621_);
if (v___x_3622_ == 0)
{
lean_object* v___x_3623_; 
lean_inc(v_typeName_3591_);
v___x_3623_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_typeName_3591_, v_a_3296_, v_a_3297_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_a_3624_);
lean_dec_ref_known(v___x_3623_, 1);
if (lean_obj_tag(v_a_3624_) == 1)
{
lean_object* v_val_3625_; lean_object* v___x_3626_; 
lean_dec_ref_known(v_code_3292_, 1);
v_val_3625_ = lean_ctor_get(v_a_3624_, 0);
lean_inc(v_val_3625_);
lean_dec_ref_known(v_a_3624_, 1);
v___x_3626_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_val_3625_, v_cases_3590_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
lean_dec(v_val_3625_);
return v___x_3626_;
}
else
{
lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3717_; 
lean_inc_ref(v_alts_3594_);
lean_inc(v_discr_3593_);
lean_inc_ref(v_resultType_3592_);
lean_inc(v_typeName_3591_);
lean_dec(v_a_3624_);
v_isSharedCheck_3717_ = !lean_is_exclusive(v_cases_3590_);
if (v_isSharedCheck_3717_ == 0)
{
lean_object* v_unused_3718_; lean_object* v_unused_3719_; lean_object* v_unused_3720_; lean_object* v_unused_3721_; 
v_unused_3718_ = lean_ctor_get(v_cases_3590_, 3);
lean_dec(v_unused_3718_);
v_unused_3719_ = lean_ctor_get(v_cases_3590_, 2);
lean_dec(v_unused_3719_);
v_unused_3720_ = lean_ctor_get(v_cases_3590_, 1);
lean_dec(v_unused_3720_);
v_unused_3721_ = lean_ctor_get(v_cases_3590_, 0);
lean_dec(v_unused_3721_);
v___x_3628_ = v_cases_3590_;
v_isShared_3629_ = v_isSharedCheck_3717_;
goto v_resetjp_3627_;
}
else
{
lean_dec(v_cases_3590_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3717_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3630_; 
lean_inc_ref(v_resultType_3592_);
v___x_3630_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3592_, v_a_3296_, v_a_3297_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3708_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3633_ = v___x_3630_;
v_isShared_3634_ = v_isSharedCheck_3708_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3630_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3708_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3635_; lean_object* v_env_3636_; lean_object* v___x_3663_; 
v___x_3635_ = lean_st_ref_get(v_a_3297_);
v_env_3636_ = lean_ctor_get(v___x_3635_, 0);
lean_inc_ref_n(v_env_3636_, 2);
lean_dec(v___x_3635_);
lean_inc(v_typeName_3591_);
v___x_3663_ = l_Lean_Environment_find_x3f(v_env_3636_, v_typeName_3591_, v___x_3622_);
if (lean_obj_tag(v___x_3663_) == 1)
{
lean_object* v_val_3664_; 
v_val_3664_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_val_3664_);
lean_dec_ref_known(v___x_3663_, 1);
if (lean_obj_tag(v_val_3664_) == 5)
{
lean_object* v_val_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3707_; 
v_val_3665_ = lean_ctor_get(v_val_3664_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v_val_3664_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3667_ = v_val_3664_;
v_isShared_3668_ = v_isSharedCheck_3707_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_val_3665_);
lean_dec(v_val_3664_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3707_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v_toConstantVal_3669_; lean_object* v_name_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v_toConstantVal_3669_ = lean_ctor_get(v_val_3665_, 0);
lean_inc_ref(v_toConstantVal_3669_);
lean_dec_ref(v_val_3665_);
v_name_3670_ = lean_ctor_get(v_toConstantVal_3669_, 0);
lean_inc(v_name_3670_);
lean_dec_ref(v_toConstantVal_3669_);
v___x_3671_ = l_Lean_mkCasesOnName(v_name_3670_);
lean_inc_ref(v_env_3636_);
v___x_3672_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_3636_, v___x_3671_);
if (lean_obj_tag(v___x_3672_) == 0)
{
if (v___x_3622_ == 0)
{
size_t v_sz_3673_; size_t v___x_3674_; lean_object* v___x_3675_; 
lean_dec_ref(v_env_3636_);
lean_del_object(v___x_3628_);
v_sz_3673_ = lean_array_size(v_alts_3594_);
v___x_3674_ = ((size_t)0ULL);
lean_inc_ref(v_alts_3594_);
v___x_3675_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v_sz_3673_, v___x_3674_, v_alts_3594_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3698_; 
v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3678_ = v___x_3675_;
v_isShared_3679_ = v_isSharedCheck_3698_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3675_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3698_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
size_t v___x_3688_; size_t v___x_3689_; uint8_t v___x_3690_; 
v___x_3688_ = lean_ptr_addr(v_alts_3594_);
lean_dec_ref(v_alts_3594_);
v___x_3689_ = lean_ptr_addr(v_a_3676_);
v___x_3690_ = lean_usize_dec_eq(v___x_3688_, v___x_3689_);
if (v___x_3690_ == 0)
{
lean_del_object(v___x_3633_);
lean_dec_ref(v_resultType_3592_);
lean_dec_ref_known(v_code_3292_, 1);
goto v___jp_3680_;
}
else
{
size_t v___x_3691_; size_t v___x_3692_; uint8_t v___x_3693_; 
v___x_3691_ = lean_ptr_addr(v_resultType_3592_);
lean_dec_ref(v_resultType_3592_);
v___x_3692_ = lean_ptr_addr(v_a_3631_);
v___x_3693_ = lean_usize_dec_eq(v___x_3691_, v___x_3692_);
if (v___x_3693_ == 0)
{
lean_del_object(v___x_3633_);
lean_dec_ref_known(v_code_3292_, 1);
goto v___jp_3680_;
}
else
{
uint8_t v___x_3694_; 
v___x_3694_ = l_Lean_instBEqFVarId_beq(v_discr_3593_, v_discr_3593_);
if (v___x_3694_ == 0)
{
lean_del_object(v___x_3633_);
lean_dec_ref_known(v_code_3292_, 1);
goto v___jp_3680_;
}
else
{
lean_object* v___x_3696_; 
lean_del_object(v___x_3678_);
lean_dec(v_a_3676_);
lean_del_object(v___x_3667_);
lean_dec(v_a_3631_);
lean_dec(v_discr_3593_);
lean_dec(v_typeName_3591_);
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 0, v_code_3292_);
v___x_3696_ = v___x_3633_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_code_3292_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
v___jp_3680_:
{
lean_object* v___x_3681_; lean_object* v___x_3683_; 
v___x_3681_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3681_, 0, v_typeName_3591_);
lean_ctor_set(v___x_3681_, 1, v_a_3631_);
lean_ctor_set(v___x_3681_, 2, v_discr_3593_);
lean_ctor_set(v___x_3681_, 3, v_a_3676_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set_tag(v___x_3667_, 4);
lean_ctor_set(v___x_3667_, 0, v___x_3681_);
v___x_3683_ = v___x_3667_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3681_);
v___x_3683_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
lean_object* v___x_3685_; 
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 0, v___x_3683_);
v___x_3685_ = v___x_3678_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3683_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
lean_del_object(v___x_3667_);
lean_del_object(v___x_3633_);
lean_dec(v_a_3631_);
lean_dec_ref(v_alts_3594_);
lean_dec(v_discr_3593_);
lean_dec_ref(v_resultType_3592_);
lean_dec(v_typeName_3591_);
lean_dec_ref_known(v_code_3292_, 1);
v_a_3699_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3675_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3675_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
else
{
lean_del_object(v___x_3667_);
lean_del_object(v___x_3633_);
lean_dec_ref(v_resultType_3592_);
lean_dec_ref_known(v_code_3292_, 1);
goto v___jp_3637_;
}
}
else
{
lean_dec_ref_known(v___x_3672_, 1);
lean_del_object(v___x_3667_);
lean_del_object(v___x_3633_);
lean_dec_ref(v_resultType_3592_);
lean_dec_ref_known(v_code_3292_, 1);
goto v___jp_3637_;
}
}
}
else
{
lean_dec(v_val_3664_);
lean_dec_ref(v_env_3636_);
lean_del_object(v___x_3633_);
lean_dec(v_a_3631_);
lean_del_object(v___x_3628_);
lean_dec_ref(v_alts_3594_);
lean_dec(v_discr_3593_);
lean_dec_ref(v_resultType_3592_);
lean_dec(v_typeName_3591_);
lean_dec_ref_known(v_code_3292_, 1);
v___y_3409_ = v_a_3293_;
v___y_3410_ = v_a_3294_;
v___y_3411_ = v_a_3295_;
v___y_3412_ = v_a_3296_;
v___y_3413_ = v_a_3297_;
goto v___jp_3408_;
}
}
else
{
lean_dec(v___x_3663_);
lean_dec_ref(v_env_3636_);
lean_del_object(v___x_3633_);
lean_dec(v_a_3631_);
lean_del_object(v___x_3628_);
lean_dec_ref(v_alts_3594_);
lean_dec(v_discr_3593_);
lean_dec_ref(v_resultType_3592_);
lean_dec(v_typeName_3591_);
lean_dec_ref_known(v_code_3292_, 1);
v___y_3409_ = v_a_3293_;
v___y_3410_ = v_a_3294_;
v___y_3411_ = v_a_3295_;
v___y_3412_ = v_a_3296_;
v___y_3413_ = v_a_3297_;
goto v___jp_3408_;
}
v___jp_3637_:
{
size_t v_sz_3638_; size_t v___x_3639_; lean_object* v___x_3640_; 
v_sz_3638_ = lean_array_size(v_alts_3594_);
v___x_3639_ = ((size_t)0ULL);
v___x_3640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(v_env_3636_, v___x_3622_, v_sz_3638_, v___x_3639_, v_alts_3594_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3654_; 
v_a_3641_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3643_ = v___x_3640_;
v_isShared_3644_ = v_isSharedCheck_3654_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3640_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3654_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3648_; 
v___x_3645_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4));
v___x_3646_ = l_Lean_Name_append(v_typeName_3591_, v___x_3645_);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 3, v_a_3641_);
lean_ctor_set(v___x_3628_, 1, v_a_3631_);
lean_ctor_set(v___x_3628_, 0, v___x_3646_);
v___x_3648_ = v___x_3628_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3646_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v_a_3631_);
lean_ctor_set(v_reuseFailAlloc_3653_, 2, v_discr_3593_);
lean_ctor_set(v_reuseFailAlloc_3653_, 3, v_a_3641_);
v___x_3648_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
lean_object* v___x_3649_; lean_object* v___x_3651_; 
v___x_3649_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3648_);
if (v_isShared_3644_ == 0)
{
lean_ctor_set(v___x_3643_, 0, v___x_3649_);
v___x_3651_ = v___x_3643_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3649_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
else
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
lean_dec(v_a_3631_);
lean_del_object(v___x_3628_);
lean_dec(v_discr_3593_);
lean_dec(v_typeName_3591_);
v_a_3655_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3640_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3640_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3660_; 
if (v_isShared_3658_ == 0)
{
v___x_3660_ = v___x_3657_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3655_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
}
}
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_del_object(v___x_3628_);
lean_dec_ref(v_alts_3594_);
lean_dec(v_discr_3593_);
lean_dec_ref(v_resultType_3592_);
lean_dec(v_typeName_3591_);
lean_dec_ref_known(v_code_3292_, 1);
v_a_3709_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3630_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3630_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
}
}
else
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
lean_dec_ref(v_cases_3590_);
lean_dec_ref_known(v_code_3292_, 1);
v_a_3722_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3623_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3623_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
else
{
lean_object* v___x_3730_; 
lean_dec_ref_known(v_code_3292_, 1);
v___x_3730_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_cases_3590_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
return v___x_3730_;
}
}
else
{
lean_object* v___x_3731_; 
lean_dec_ref_known(v_code_3292_, 1);
v___x_3731_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_cases_3590_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
lean_dec_ref(v_cases_3590_);
return v___x_3731_;
}
}
else
{
lean_object* v___x_3732_; 
lean_dec_ref_known(v_code_3292_, 1);
v___x_3732_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_cases_3590_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
return v___x_3732_;
}
}
else
{
lean_object* v___x_3733_; 
lean_dec_ref_known(v_code_3292_, 1);
v___x_3733_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_cases_3590_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
return v___x_3733_;
}
}
else
{
lean_object* v___x_3734_; 
lean_dec_ref_known(v_code_3292_, 1);
v___x_3734_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_cases_3590_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
return v___x_3734_;
}
}
else
{
lean_object* v___x_3735_; 
lean_dec_ref_known(v_code_3292_, 1);
v___x_3735_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_cases_3590_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
return v___x_3735_;
}
}
else
{
lean_object* v___x_3736_; 
lean_dec_ref_known(v_code_3292_, 1);
v___x_3736_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_cases_3590_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
return v___x_3736_;
}
}
else
{
lean_object* v___x_3737_; 
lean_dec_ref_known(v_code_3292_, 1);
v___x_3737_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_cases_3590_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
return v___x_3737_;
}
}
else
{
lean_object* v___x_3738_; 
lean_dec_ref_known(v_code_3292_, 1);
v___x_3738_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3590_, v___x_3605_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
return v___x_3738_;
}
}
else
{
lean_object* v___x_3739_; 
lean_dec_ref_known(v_code_3292_, 1);
v___x_3739_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3590_, v___x_3603_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
return v___x_3739_;
}
}
else
{
lean_object* v___x_3740_; 
lean_dec_ref_known(v_code_3292_, 1);
v___x_3740_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3590_, v___x_3601_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
return v___x_3740_;
}
}
else
{
lean_object* v___x_3741_; 
lean_dec_ref_known(v_code_3292_, 1);
v___x_3741_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3590_, v___x_3599_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
return v___x_3741_;
}
}
else
{
lean_object* v___x_3742_; 
lean_dec_ref_known(v_code_3292_, 1);
v___x_3742_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_cases_3590_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
return v___x_3742_;
}
}
else
{
lean_object* v___x_3743_; 
lean_dec_ref_known(v_code_3292_, 1);
v___x_3743_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_cases_3590_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
return v___x_3743_;
}
}
case 5:
{
lean_object* v___x_3744_; 
v___x_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3744_, 0, v_code_3292_);
return v___x_3744_;
}
case 6:
{
lean_object* v_type_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3769_; 
v_type_3745_ = lean_ctor_get(v_code_3292_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v_code_3292_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3747_ = v_code_3292_;
v_isShared_3748_ = v_isSharedCheck_3769_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_type_3745_);
lean_dec(v_code_3292_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3769_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3749_; 
v___x_3749_ = l_Lean_Compiler_LCNF_toMonoType(v_type_3745_, v_a_3296_, v_a_3297_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3760_; 
v_a_3750_ = lean_ctor_get(v___x_3749_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3752_ = v___x_3749_;
v_isShared_3753_ = v_isSharedCheck_3760_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3749_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3760_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 0, v_a_3750_);
v___x_3755_ = v___x_3747_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
lean_object* v___x_3757_; 
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 0, v___x_3755_);
v___x_3757_ = v___x_3752_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v___x_3755_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_del_object(v___x_3747_);
v_a_3761_ = lean_ctor_get(v___x_3749_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3749_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3749_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
}
default: 
{
lean_object* v_decl_3770_; lean_object* v_k_3771_; 
v_decl_3770_ = lean_ctor_get(v_code_3292_, 0);
v_k_3771_ = lean_ctor_get(v_code_3292_, 1);
lean_inc_ref(v_k_3771_);
lean_inc_ref(v_decl_3770_);
v_decl_3300_ = v_decl_3770_;
v_k_3301_ = v_k_3771_;
v___y_3302_ = v_a_3293_;
v___y_3303_ = v_a_3294_;
v___y_3304_ = v_a_3295_;
v___y_3305_ = v_a_3296_;
v___y_3306_ = v_a_3297_;
goto v___jp_3299_;
}
}
v___jp_3299_:
{
lean_object* v___x_3307_; 
v___x_3307_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_3300_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; lean_object* v___x_3309_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_a_3308_);
lean_dec_ref_known(v___x_3307_, 1);
v___x_3309_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
if (lean_obj_tag(v___x_3309_) == 0)
{
switch(lean_obj_tag(v_code_3292_))
{
case 1:
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3349_; 
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3312_ = v___x_3309_;
v_isShared_3313_ = v_isSharedCheck_3349_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3309_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3349_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v_decl_3314_; lean_object* v_k_3315_; size_t v___x_3316_; size_t v___x_3317_; uint8_t v___x_3318_; 
v_decl_3314_ = lean_ctor_get(v_code_3292_, 0);
v_k_3315_ = lean_ctor_get(v_code_3292_, 1);
v___x_3316_ = lean_ptr_addr(v_k_3315_);
v___x_3317_ = lean_ptr_addr(v_a_3310_);
v___x_3318_ = lean_usize_dec_eq(v___x_3316_, v___x_3317_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3328_; 
v_isSharedCheck_3328_ = !lean_is_exclusive(v_code_3292_);
if (v_isSharedCheck_3328_ == 0)
{
lean_object* v_unused_3329_; lean_object* v_unused_3330_; 
v_unused_3329_ = lean_ctor_get(v_code_3292_, 1);
lean_dec(v_unused_3329_);
v_unused_3330_ = lean_ctor_get(v_code_3292_, 0);
lean_dec(v_unused_3330_);
v___x_3320_ = v_code_3292_;
v_isShared_3321_ = v_isSharedCheck_3328_;
goto v_resetjp_3319_;
}
else
{
lean_dec(v_code_3292_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3328_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
lean_ctor_set(v___x_3320_, 1, v_a_3310_);
lean_ctor_set(v___x_3320_, 0, v_a_3308_);
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3308_);
lean_ctor_set(v_reuseFailAlloc_3327_, 1, v_a_3310_);
v___x_3323_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
lean_object* v___x_3325_; 
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 0, v___x_3323_);
v___x_3325_ = v___x_3312_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3323_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
else
{
size_t v___x_3331_; size_t v___x_3332_; uint8_t v___x_3333_; 
v___x_3331_ = lean_ptr_addr(v_decl_3314_);
v___x_3332_ = lean_ptr_addr(v_a_3308_);
v___x_3333_ = lean_usize_dec_eq(v___x_3331_, v___x_3332_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3343_; 
v_isSharedCheck_3343_ = !lean_is_exclusive(v_code_3292_);
if (v_isSharedCheck_3343_ == 0)
{
lean_object* v_unused_3344_; lean_object* v_unused_3345_; 
v_unused_3344_ = lean_ctor_get(v_code_3292_, 1);
lean_dec(v_unused_3344_);
v_unused_3345_ = lean_ctor_get(v_code_3292_, 0);
lean_dec(v_unused_3345_);
v___x_3335_ = v_code_3292_;
v_isShared_3336_ = v_isSharedCheck_3343_;
goto v_resetjp_3334_;
}
else
{
lean_dec(v_code_3292_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3343_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 1, v_a_3310_);
lean_ctor_set(v___x_3335_, 0, v_a_3308_);
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_a_3308_);
lean_ctor_set(v_reuseFailAlloc_3342_, 1, v_a_3310_);
v___x_3338_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
lean_object* v___x_3340_; 
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 0, v___x_3338_);
v___x_3340_ = v___x_3312_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3338_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
else
{
lean_object* v___x_3347_; 
lean_dec(v_a_3310_);
lean_dec(v_a_3308_);
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 0, v_code_3292_);
v___x_3347_ = v___x_3312_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_code_3292_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
}
case 2:
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3389_; 
v_a_3350_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3352_ = v___x_3309_;
v_isShared_3353_ = v_isSharedCheck_3389_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3309_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3389_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v_decl_3354_; lean_object* v_k_3355_; size_t v___x_3356_; size_t v___x_3357_; uint8_t v___x_3358_; 
v_decl_3354_ = lean_ctor_get(v_code_3292_, 0);
v_k_3355_ = lean_ctor_get(v_code_3292_, 1);
v___x_3356_ = lean_ptr_addr(v_k_3355_);
v___x_3357_ = lean_ptr_addr(v_a_3350_);
v___x_3358_ = lean_usize_dec_eq(v___x_3356_, v___x_3357_);
if (v___x_3358_ == 0)
{
lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3368_; 
v_isSharedCheck_3368_ = !lean_is_exclusive(v_code_3292_);
if (v_isSharedCheck_3368_ == 0)
{
lean_object* v_unused_3369_; lean_object* v_unused_3370_; 
v_unused_3369_ = lean_ctor_get(v_code_3292_, 1);
lean_dec(v_unused_3369_);
v_unused_3370_ = lean_ctor_get(v_code_3292_, 0);
lean_dec(v_unused_3370_);
v___x_3360_ = v_code_3292_;
v_isShared_3361_ = v_isSharedCheck_3368_;
goto v_resetjp_3359_;
}
else
{
lean_dec(v_code_3292_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3368_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 1, v_a_3350_);
lean_ctor_set(v___x_3360_, 0, v_a_3308_);
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3308_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_a_3350_);
v___x_3363_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3365_; 
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 0, v___x_3363_);
v___x_3365_ = v___x_3352_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3363_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
}
else
{
size_t v___x_3371_; size_t v___x_3372_; uint8_t v___x_3373_; 
v___x_3371_ = lean_ptr_addr(v_decl_3354_);
v___x_3372_ = lean_ptr_addr(v_a_3308_);
v___x_3373_ = lean_usize_dec_eq(v___x_3371_, v___x_3372_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3383_; 
v_isSharedCheck_3383_ = !lean_is_exclusive(v_code_3292_);
if (v_isSharedCheck_3383_ == 0)
{
lean_object* v_unused_3384_; lean_object* v_unused_3385_; 
v_unused_3384_ = lean_ctor_get(v_code_3292_, 1);
lean_dec(v_unused_3384_);
v_unused_3385_ = lean_ctor_get(v_code_3292_, 0);
lean_dec(v_unused_3385_);
v___x_3375_ = v_code_3292_;
v_isShared_3376_ = v_isSharedCheck_3383_;
goto v_resetjp_3374_;
}
else
{
lean_dec(v_code_3292_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3383_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 1, v_a_3350_);
lean_ctor_set(v___x_3375_, 0, v_a_3308_);
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3308_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_a_3350_);
v___x_3378_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
lean_object* v___x_3380_; 
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 0, v___x_3378_);
v___x_3380_ = v___x_3352_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3378_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
else
{
lean_object* v___x_3387_; 
lean_dec(v_a_3350_);
lean_dec(v_a_3308_);
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 0, v_code_3292_);
v___x_3387_ = v___x_3352_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_code_3292_);
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
}
default: 
{
lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3398_; 
lean_dec(v_a_3308_);
lean_dec_ref(v_code_3292_);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3398_ == 0)
{
lean_object* v_unused_3399_; 
v_unused_3399_ = lean_ctor_get(v___x_3309_, 0);
lean_dec(v_unused_3399_);
v___x_3391_ = v___x_3309_;
v_isShared_3392_ = v_isSharedCheck_3398_;
goto v_resetjp_3390_;
}
else
{
lean_dec(v___x_3309_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3398_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3396_; 
v___x_3393_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__2, &l_Lean_Compiler_LCNF_Code_toMono___closed__2_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__2);
v___x_3394_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__2(v___x_3393_);
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 0, v___x_3394_);
v___x_3396_ = v___x_3391_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3394_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
}
else
{
lean_dec(v_a_3308_);
lean_dec_ref(v_code_3292_);
return v___x_3309_;
}
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_dec_ref(v_k_3301_);
lean_dec_ref(v_code_3292_);
v_a_3400_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___x_3307_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3307_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
v___jp_3408_:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__4, &l_Lean_Compiler_LCNF_Code_toMono___closed__4_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__4);
v___x_3415_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3414_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
return v___x_3415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono(lean_object* v_decl_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_){
_start:
{
lean_object* v_params_3779_; lean_object* v_type_3780_; lean_object* v_value_3781_; lean_object* v___x_3782_; 
v_params_3779_ = lean_ctor_get(v_decl_3772_, 2);
v_type_3780_ = lean_ctor_get(v_decl_3772_, 3);
v_value_3781_ = lean_ctor_get(v_decl_3772_, 4);
lean_inc_ref(v_type_3780_);
v___x_3782_ = l_Lean_Compiler_LCNF_toMonoType(v_type_3780_, v_a_3776_, v_a_3777_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; size_t v_sz_3784_; size_t v___x_3785_; lean_object* v___x_3786_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3783_);
lean_dec_ref_known(v___x_3782_, 1);
v_sz_3784_ = lean_array_size(v_params_3779_);
v___x_3785_ = ((size_t)0ULL);
lean_inc_ref(v_params_3779_);
v___x_3786_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_3784_, v___x_3785_, v_params_3779_, v_a_3773_, v_a_3775_, v_a_3776_, v_a_3777_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v___x_3788_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_a_3787_);
lean_dec_ref_known(v___x_3786_, 1);
lean_inc_ref(v_value_3781_);
v___x_3788_ = l_Lean_Compiler_LCNF_Code_toMono(v_value_3781_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; uint8_t v___x_3790_; lean_object* v___x_3791_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_a_3789_);
lean_dec_ref_known(v___x_3788_, 1);
v___x_3790_ = 0;
v___x_3791_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3790_, v_decl_3772_, v_a_3783_, v_a_3787_, v_a_3789_, v_a_3775_);
return v___x_3791_;
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
lean_dec(v_a_3787_);
lean_dec(v_a_3783_);
lean_dec_ref(v_decl_3772_);
v_a_3792_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3788_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3788_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
else
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
lean_dec(v_a_3783_);
lean_dec_ref(v_decl_3772_);
v_a_3800_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3802_ = v___x_3786_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3786_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_dec_ref(v_decl_3772_);
v_a_3808_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3782_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3782_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono___boxed(lean_object* v_decl_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_);
lean_dec(v_a_3821_);
lean_dec_ref(v_a_3820_);
lean_dec(v_a_3819_);
lean_dec_ref(v_a_3818_);
lean_dec(v_a_3817_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___boxed(lean_object* v_sz_3824_, lean_object* v_i_3825_, lean_object* v_bs_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
size_t v_sz_boxed_3833_; size_t v_i_boxed_3834_; lean_object* v_res_3835_; 
v_sz_boxed_3833_ = lean_unbox_usize(v_sz_3824_);
lean_dec(v_sz_3824_);
v_i_boxed_3834_ = lean_unbox_usize(v_i_3825_);
lean_dec(v_i_3825_);
v_res_3835_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v_sz_boxed_3833_, v_i_boxed_3834_, v_bs_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec(v___y_3827_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___boxed(lean_object* v_c_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_);
lean_dec(v_a_3841_);
lean_dec_ref(v_a_3840_);
lean_dec(v_a_3839_);
lean_dec_ref(v_a_3838_);
lean_dec(v_a_3837_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___boxed(lean_object* v_c_3844_, lean_object* v_uintName_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_){
_start:
{
lean_object* v_res_3852_; 
v_res_3852_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_3844_, v_uintName_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_);
lean_dec(v_a_3850_);
lean_dec_ref(v_a_3849_);
lean_dec(v_a_3848_);
lean_dec_ref(v_a_3847_);
lean_dec(v_a_3846_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___boxed(lean_object* v_c_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_);
lean_dec(v_a_3858_);
lean_dec_ref(v_a_3857_);
lean_dec(v_a_3856_);
lean_dec_ref(v_a_3855_);
lean_dec(v_a_3854_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___boxed(lean_object* v_c_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_c_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_);
lean_dec(v_a_3866_);
lean_dec_ref(v_a_3865_);
lean_dec(v_a_3864_);
lean_dec_ref(v_a_3863_);
lean_dec(v_a_3862_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___boxed(lean_object* v_c_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_);
lean_dec(v_a_3874_);
lean_dec_ref(v_a_3873_);
lean_dec(v_a_3872_);
lean_dec_ref(v_a_3871_);
lean_dec(v_a_3870_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg___boxed(lean_object* v_c_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_c_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
lean_dec(v_a_3882_);
lean_dec_ref(v_a_3881_);
lean_dec(v_a_3880_);
lean_dec_ref(v_a_3879_);
lean_dec(v_a_3878_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___boxed(lean_object* v_c_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_);
lean_dec(v_a_3890_);
lean_dec_ref(v_a_3889_);
lean_dec(v_a_3888_);
lean_dec_ref(v_a_3887_);
lean_dec(v_a_3886_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___boxed(lean_object* v___x_3893_, lean_object* v___x_3894_, lean_object* v_sz_3895_, lean_object* v_i_3896_, lean_object* v_bs_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
uint8_t v___x_33924__boxed_3904_; size_t v_sz_boxed_3905_; size_t v_i_boxed_3906_; lean_object* v_res_3907_; 
v___x_33924__boxed_3904_ = lean_unbox(v___x_3894_);
v_sz_boxed_3905_ = lean_unbox_usize(v_sz_3895_);
lean_dec(v_sz_3895_);
v_i_boxed_3906_ = lean_unbox_usize(v_i_3896_);
lean_dec(v_i_3896_);
v_res_3907_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(v___x_3893_, v___x_33924__boxed_3904_, v_sz_boxed_3905_, v_i_boxed_3906_, v_bs_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___boxed(lean_object* v_c_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
lean_dec(v_a_3913_);
lean_dec_ref(v_a_3912_);
lean_dec(v_a_3911_);
lean_dec_ref(v_a_3910_);
lean_dec(v_a_3909_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___boxed(lean_object* v_c_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_){
_start:
{
lean_object* v_res_3923_; 
v_res_3923_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_);
lean_dec(v_a_3921_);
lean_dec_ref(v_a_3920_);
lean_dec(v_a_3919_);
lean_dec_ref(v_a_3918_);
lean_dec(v_a_3917_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___boxed(lean_object* v_c_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_){
_start:
{
lean_object* v_res_3931_; 
v_res_3931_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_);
lean_dec(v_a_3929_);
lean_dec_ref(v_a_3928_);
lean_dec(v_a_3927_);
lean_dec_ref(v_a_3926_);
lean_dec(v_a_3925_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___boxed(lean_object* v_info_3932_, lean_object* v_c_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_){
_start:
{
lean_object* v_res_3940_; 
v_res_3940_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_info_3932_, v_c_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_);
lean_dec(v_a_3938_);
lean_dec_ref(v_a_3937_);
lean_dec(v_a_3936_);
lean_dec_ref(v_a_3935_);
lean_dec(v_a_3934_);
lean_dec_ref(v_info_3932_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___boxed(lean_object* v___x_3941_, lean_object* v_sz_3942_, lean_object* v_i_3943_, lean_object* v_bs_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
size_t v_sz_boxed_3951_; size_t v_i_boxed_3952_; lean_object* v_res_3953_; 
v_sz_boxed_3951_ = lean_unbox_usize(v_sz_3942_);
lean_dec(v_sz_3942_);
v_i_boxed_3952_ = lean_unbox_usize(v_i_3943_);
lean_dec(v_i_3943_);
v_res_3953_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(v___x_3941_, v_sz_boxed_3951_, v_i_boxed_3952_, v_bs_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___boxed(lean_object* v_c_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
lean_dec(v_a_3955_);
lean_dec_ref(v_c_3954_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___boxed(lean_object* v___x_3962_, lean_object* v_sz_3963_, lean_object* v_i_3964_, lean_object* v_bs_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
size_t v_sz_boxed_3972_; size_t v_i_boxed_3973_; lean_object* v_res_3974_; 
v_sz_boxed_3972_ = lean_unbox_usize(v_sz_3963_);
lean_dec(v_sz_3963_);
v_i_boxed_3973_ = lean_unbox_usize(v_i_3964_);
lean_dec(v_i_3964_);
v_res_3974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(v___x_3962_, v_sz_boxed_3972_, v_i_boxed_3973_, v_bs_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono___boxed(lean_object* v_code_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_);
lean_dec(v_a_3980_);
lean_dec_ref(v_a_3979_);
lean_dec(v_a_3978_);
lean_dec_ref(v_a_3977_);
lean_dec(v_a_3976_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono(lean_object* v_c_3983_, lean_object* v_x_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_3983_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___boxed(lean_object* v_c_3992_, lean_object* v_x_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l_Lean_Compiler_LCNF_casesTaskToMono(v_c_3992_, v_x_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
lean_dec(v_a_3998_);
lean_dec_ref(v_a_3997_);
lean_dec(v_a_3996_);
lean_dec_ref(v_a_3995_);
lean_dec(v_a_3994_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono(lean_object* v_c_4001_, lean_object* v_x_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_){
_start:
{
lean_object* v___x_4009_; 
v___x_4009_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_4001_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___boxed(lean_object* v_c_4010_, lean_object* v_x_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_Lean_Compiler_LCNF_casesThunkToMono(v_c_4010_, v_x_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_);
lean_dec(v_a_4016_);
lean_dec_ref(v_a_4015_);
lean_dec(v_a_4014_);
lean_dec_ref(v_a_4013_);
lean_dec(v_a_4012_);
lean_dec_ref(v_c_4010_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono(lean_object* v_c_4019_, lean_object* v_x_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_){
_start:
{
lean_object* v___x_4027_; 
v___x_4027_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_c_4019_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___boxed(lean_object* v_c_4028_, lean_object* v_x_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l_Lean_Compiler_LCNF_casesFloat32ToMono(v_c_4028_, v_x_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
lean_dec(v_a_4034_);
lean_dec_ref(v_a_4033_);
lean_dec(v_a_4032_);
lean_dec_ref(v_a_4031_);
lean_dec(v_a_4030_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono(lean_object* v_c_4037_, lean_object* v_x_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_){
_start:
{
lean_object* v___x_4045_; 
v___x_4045_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_c_4037_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___boxed(lean_object* v_c_4046_, lean_object* v_x_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l_Lean_Compiler_LCNF_casesFloatToMono(v_c_4046_, v_x_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_);
lean_dec(v_a_4052_);
lean_dec_ref(v_a_4051_);
lean_dec(v_a_4050_);
lean_dec_ref(v_a_4049_);
lean_dec(v_a_4048_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono(lean_object* v_c_4055_, lean_object* v_x_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_){
_start:
{
lean_object* v___x_4063_; 
v___x_4063_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_4055_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___boxed(lean_object* v_c_4064_, lean_object* v_x_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_){
_start:
{
lean_object* v_res_4072_; 
v_res_4072_ = l_Lean_Compiler_LCNF_casesStringToMono(v_c_4064_, v_x_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_);
lean_dec(v_a_4070_);
lean_dec_ref(v_a_4069_);
lean_dec(v_a_4068_);
lean_dec_ref(v_a_4067_);
lean_dec(v_a_4066_);
return v_res_4072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono(lean_object* v_c_4073_, lean_object* v_x_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_){
_start:
{
lean_object* v___x_4081_; 
v___x_4081_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_4073_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___boxed(lean_object* v_c_4082_, lean_object* v_x_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_){
_start:
{
lean_object* v_res_4090_; 
v_res_4090_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono(v_c_4082_, v_x_4083_, v_a_4084_, v_a_4085_, v_a_4086_, v_a_4087_, v_a_4088_);
lean_dec(v_a_4088_);
lean_dec_ref(v_a_4087_);
lean_dec(v_a_4086_);
lean_dec_ref(v_a_4085_);
lean_dec(v_a_4084_);
return v_res_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono(lean_object* v_c_4091_, lean_object* v_x_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_){
_start:
{
lean_object* v___x_4099_; 
v___x_4099_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_4091_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___boxed(lean_object* v_c_4100_, lean_object* v_x_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l_Lean_Compiler_LCNF_casesByteArrayToMono(v_c_4100_, v_x_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_);
lean_dec(v_a_4106_);
lean_dec_ref(v_a_4105_);
lean_dec(v_a_4104_);
lean_dec_ref(v_a_4103_);
lean_dec(v_a_4102_);
return v_res_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono(lean_object* v_c_4109_, lean_object* v_x_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_){
_start:
{
lean_object* v___x_4117_; 
v___x_4117_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_4109_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___boxed(lean_object* v_c_4118_, lean_object* v_x_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_Lean_Compiler_LCNF_casesArrayToMono(v_c_4118_, v_x_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
lean_dec(v_a_4124_);
lean_dec_ref(v_a_4123_);
lean_dec(v_a_4122_);
lean_dec_ref(v_a_4121_);
lean_dec(v_a_4120_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono(lean_object* v_c_4127_, lean_object* v_uintName_4128_, lean_object* v_x_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_){
_start:
{
lean_object* v___x_4136_; 
v___x_4136_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_4127_, v_uintName_4128_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_);
return v___x_4136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___boxed(lean_object* v_c_4137_, lean_object* v_uintName_4138_, lean_object* v_x_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Lean_Compiler_LCNF_casesUIntToMono(v_c_4137_, v_uintName_4138_, v_x_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_);
lean_dec(v_a_4144_);
lean_dec_ref(v_a_4143_);
lean_dec(v_a_4142_);
lean_dec_ref(v_a_4141_);
lean_dec(v_a_4140_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono(lean_object* v_c_4147_, lean_object* v_x_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_){
_start:
{
lean_object* v___x_4155_; 
v___x_4155_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_4147_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_, v_a_4153_);
return v___x_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___boxed(lean_object* v_c_4156_, lean_object* v_x_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Lean_Compiler_LCNF_casesIntToMono(v_c_4156_, v_x_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_);
lean_dec(v_a_4162_);
lean_dec_ref(v_a_4161_);
lean_dec(v_a_4160_);
lean_dec_ref(v_a_4159_);
lean_dec(v_a_4158_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono(lean_object* v_c_4165_, lean_object* v_x_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_){
_start:
{
lean_object* v___x_4173_; 
v___x_4173_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_4165_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___boxed(lean_object* v_c_4174_, lean_object* v_x_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_){
_start:
{
lean_object* v_res_4182_; 
v_res_4182_ = l_Lean_Compiler_LCNF_casesNatToMono(v_c_4174_, v_x_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_);
lean_dec(v_a_4180_);
lean_dec_ref(v_a_4179_);
lean_dec(v_a_4178_);
lean_dec_ref(v_a_4177_);
lean_dec(v_a_4176_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(size_t v_sz_4183_, size_t v_i_4184_, lean_object* v_bs_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_4183_, v_i_4184_, v_bs_4185_, v___y_4186_, v___y_4188_, v___y_4189_, v___y_4190_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___boxed(lean_object* v_sz_4193_, lean_object* v_i_4194_, lean_object* v_bs_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_){
_start:
{
size_t v_sz_boxed_4202_; size_t v_i_boxed_4203_; lean_object* v_res_4204_; 
v_sz_boxed_4202_ = lean_unbox_usize(v_sz_4193_);
lean_dec(v_sz_4193_);
v_i_boxed_4203_ = lean_unbox_usize(v_i_4194_);
lean_dec(v_i_4194_);
v_res_4204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(v_sz_boxed_4202_, v_i_boxed_4203_, v_bs_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
lean_dec(v___y_4200_);
lean_dec_ref(v___y_4199_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
lean_dec(v___y_4196_);
return v_res_4204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(lean_object* v_f_4205_, lean_object* v_v_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
if (lean_obj_tag(v_v_4206_) == 0)
{
lean_object* v_code_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4237_; 
v_code_4213_ = lean_ctor_get(v_v_4206_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v_v_4206_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4215_ = v_v_4206_;
v_isShared_4216_ = v_isSharedCheck_4237_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_code_4213_);
lean_dec(v_v_4206_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4237_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4217_; 
lean_inc(v___y_4211_);
lean_inc_ref(v___y_4210_);
lean_inc(v___y_4209_);
lean_inc_ref(v___y_4208_);
lean_inc(v___y_4207_);
v___x_4217_ = lean_apply_7(v_f_4205_, v_code_4213_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, lean_box(0));
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4228_; 
v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4220_ = v___x_4217_;
v_isShared_4221_ = v_isSharedCheck_4228_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v___x_4217_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4228_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4223_; 
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 0, v_a_4218_);
v___x_4223_ = v___x_4215_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4218_);
v___x_4223_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
lean_object* v___x_4225_; 
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 0, v___x_4223_);
v___x_4225_ = v___x_4220_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4223_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
}
else
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
lean_del_object(v___x_4215_);
v_a_4229_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4231_ = v___x_4217_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4217_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4229_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
}
else
{
lean_object* v___x_4238_; 
lean_dec_ref(v_f_4205_);
v___x_4238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4238_, 0, v_v_4206_);
return v___x_4238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg___boxed(lean_object* v_f_4239_, lean_object* v_v_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_4239_, v_v_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(uint8_t v_pu_4248_, lean_object* v_f_4249_, lean_object* v_v_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_){
_start:
{
lean_object* v___x_4257_; 
v___x_4257_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_4249_, v_v_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___boxed(lean_object* v_pu_4258_, lean_object* v_f_4259_, lean_object* v_v_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
uint8_t v_pu_boxed_4267_; lean_object* v_res_4268_; 
v_pu_boxed_4267_ = lean_unbox(v_pu_4258_);
v_res_4268_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(v_pu_boxed_4267_, v_f_4259_, v_v_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec(v___y_4263_);
lean_dec_ref(v___y_4262_);
lean_dec(v___y_4261_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(lean_object* v_decl_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_){
_start:
{
lean_object* v_toSignature_4277_; lean_object* v_value_4278_; uint8_t v_recursive_4279_; lean_object* v_inlineAttr_x3f_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4350_; 
v_toSignature_4277_ = lean_ctor_get(v_decl_4270_, 0);
v_value_4278_ = lean_ctor_get(v_decl_4270_, 1);
v_recursive_4279_ = lean_ctor_get_uint8(v_decl_4270_, sizeof(void*)*3);
v_inlineAttr_x3f_4280_ = lean_ctor_get(v_decl_4270_, 2);
v_isSharedCheck_4350_ = !lean_is_exclusive(v_decl_4270_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4282_ = v_decl_4270_;
v_isShared_4283_ = v_isSharedCheck_4350_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_inlineAttr_x3f_4280_);
lean_inc(v_value_4278_);
lean_inc(v_toSignature_4277_);
lean_dec(v_decl_4270_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4350_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v_name_4284_; lean_object* v_type_4285_; lean_object* v_params_4286_; uint8_t v_safe_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4348_; 
v_name_4284_ = lean_ctor_get(v_toSignature_4277_, 0);
v_type_4285_ = lean_ctor_get(v_toSignature_4277_, 2);
v_params_4286_ = lean_ctor_get(v_toSignature_4277_, 3);
v_safe_4287_ = lean_ctor_get_uint8(v_toSignature_4277_, sizeof(void*)*4);
v_isSharedCheck_4348_ = !lean_is_exclusive(v_toSignature_4277_);
if (v_isSharedCheck_4348_ == 0)
{
lean_object* v_unused_4349_; 
v_unused_4349_ = lean_ctor_get(v_toSignature_4277_, 1);
lean_dec(v_unused_4349_);
v___x_4289_ = v_toSignature_4277_;
v_isShared_4290_ = v_isSharedCheck_4348_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_params_4286_);
lean_inc(v_type_4285_);
lean_inc(v_name_4284_);
lean_dec(v_toSignature_4277_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4348_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4291_; 
v___x_4291_ = l_Lean_Compiler_LCNF_toMonoType(v_type_4285_, v_a_4274_, v_a_4275_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; size_t v_sz_4293_; size_t v___x_4294_; lean_object* v___x_4295_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_a_4292_);
lean_dec_ref_known(v___x_4291_, 1);
v_sz_4293_ = lean_array_size(v_params_4286_);
v___x_4294_ = ((size_t)0ULL);
v___x_4295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_4293_, v___x_4294_, v_params_4286_, v_a_4271_, v_a_4273_, v_a_4274_, v_a_4275_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v_a_4296_; lean_object* v___f_4297_; lean_object* v___x_4298_; 
v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
lean_inc(v_a_4296_);
lean_dec_ref_known(v___x_4295_, 1);
v___f_4297_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___closed__0));
v___x_4298_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v___f_4297_, v_value_4278_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_object* v_a_4299_; lean_object* v___x_4300_; lean_object* v___x_4302_; 
v_a_4299_ = lean_ctor_get(v___x_4298_, 0);
lean_inc(v_a_4299_);
lean_dec_ref_known(v___x_4298_, 1);
v___x_4300_ = lean_box(0);
if (v_isShared_4290_ == 0)
{
lean_ctor_set(v___x_4289_, 3, v_a_4296_);
lean_ctor_set(v___x_4289_, 2, v_a_4292_);
lean_ctor_set(v___x_4289_, 1, v___x_4300_);
v___x_4302_ = v___x_4289_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v_name_4284_);
lean_ctor_set(v_reuseFailAlloc_4323_, 1, v___x_4300_);
lean_ctor_set(v_reuseFailAlloc_4323_, 2, v_a_4292_);
lean_ctor_set(v_reuseFailAlloc_4323_, 3, v_a_4296_);
lean_ctor_set_uint8(v_reuseFailAlloc_4323_, sizeof(void*)*4, v_safe_4287_);
v___x_4302_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
lean_object* v___x_4304_; 
if (v_isShared_4283_ == 0)
{
lean_ctor_set(v___x_4282_, 1, v_a_4299_);
lean_ctor_set(v___x_4282_, 0, v___x_4302_);
v___x_4304_ = v___x_4282_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v___x_4302_);
lean_ctor_set(v_reuseFailAlloc_4322_, 1, v_a_4299_);
lean_ctor_set(v_reuseFailAlloc_4322_, 2, v_inlineAttr_x3f_4280_);
lean_ctor_set_uint8(v_reuseFailAlloc_4322_, sizeof(void*)*3, v_recursive_4279_);
v___x_4304_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
lean_object* v___x_4305_; 
lean_inc_ref(v___x_4304_);
v___x_4305_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_4304_, v_a_4275_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4312_; 
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4312_ == 0)
{
lean_object* v_unused_4313_; 
v_unused_4313_ = lean_ctor_get(v___x_4305_, 0);
lean_dec(v_unused_4313_);
v___x_4307_ = v___x_4305_;
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
else
{
lean_dec(v___x_4305_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4310_; 
if (v_isShared_4308_ == 0)
{
lean_ctor_set(v___x_4307_, 0, v___x_4304_);
v___x_4310_ = v___x_4307_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v___x_4304_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
else
{
lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4321_; 
lean_dec_ref(v___x_4304_);
v_a_4314_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4316_ = v___x_4305_;
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_a_4314_);
lean_dec(v___x_4305_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4319_; 
if (v_isShared_4317_ == 0)
{
v___x_4319_ = v___x_4316_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_a_4314_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
return v___x_4319_;
}
}
}
}
}
}
else
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4331_; 
lean_dec(v_a_4296_);
lean_dec(v_a_4292_);
lean_del_object(v___x_4289_);
lean_dec(v_name_4284_);
lean_del_object(v___x_4282_);
lean_dec(v_inlineAttr_x3f_4280_);
v_a_4324_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4326_ = v___x_4298_;
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4298_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4329_; 
if (v_isShared_4327_ == 0)
{
v___x_4329_ = v___x_4326_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v_a_4324_);
v___x_4329_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
return v___x_4329_;
}
}
}
}
else
{
lean_object* v_a_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4339_; 
lean_dec(v_a_4292_);
lean_del_object(v___x_4289_);
lean_dec(v_name_4284_);
lean_del_object(v___x_4282_);
lean_dec(v_inlineAttr_x3f_4280_);
lean_dec_ref(v_value_4278_);
v_a_4332_ = lean_ctor_get(v___x_4295_, 0);
v_isSharedCheck_4339_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4334_ = v___x_4295_;
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_a_4332_);
lean_dec(v___x_4295_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___x_4337_; 
if (v_isShared_4335_ == 0)
{
v___x_4337_ = v___x_4334_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v_a_4332_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
return v___x_4337_;
}
}
}
}
else
{
lean_object* v_a_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4347_; 
lean_del_object(v___x_4289_);
lean_dec_ref(v_params_4286_);
lean_dec(v_name_4284_);
lean_del_object(v___x_4282_);
lean_dec(v_inlineAttr_x3f_4280_);
lean_dec_ref(v_value_4278_);
v_a_4340_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4342_ = v___x_4291_;
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_a_4340_);
lean_dec(v___x_4291_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4345_; 
if (v_isShared_4343_ == 0)
{
v___x_4345_ = v___x_4342_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_a_4340_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___boxed(lean_object* v_decl_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_){
_start:
{
lean_object* v_res_4358_; 
v_res_4358_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_);
lean_dec(v_a_4356_);
lean_dec_ref(v_a_4355_);
lean_dec(v_a_4354_);
lean_dec_ref(v_a_4353_);
lean_dec(v_a_4352_);
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono(lean_object* v_decl_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_){
_start:
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4365_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_4366_ = lean_st_mk_ref(v___x_4365_);
v___x_4367_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_4359_, v___x_4366_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4376_; 
v_a_4368_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4376_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4376_ == 0)
{
v___x_4370_ = v___x_4367_;
v_isShared_4371_ = v_isSharedCheck_4376_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4367_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4376_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v___x_4372_; lean_object* v___x_4374_; 
v___x_4372_ = lean_st_ref_get(v___x_4366_);
lean_dec(v___x_4366_);
lean_dec(v___x_4372_);
if (v_isShared_4371_ == 0)
{
v___x_4374_ = v___x_4370_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v_a_4368_);
v___x_4374_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
return v___x_4374_;
}
}
}
else
{
lean_dec(v___x_4366_);
return v___x_4367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono___boxed(lean_object* v_decl_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_){
_start:
{
lean_object* v_res_4383_; 
v_res_4383_ = l_Lean_Compiler_LCNF_Decl_toMono(v_decl_4377_, v_a_4378_, v_a_4379_, v_a_4380_, v_a_4381_);
lean_dec(v_a_4381_);
lean_dec_ref(v_a_4380_);
lean_dec(v_a_4379_);
lean_dec_ref(v_a_4378_);
return v_res_4383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(size_t v_sz_4384_, size_t v_i_4385_, lean_object* v_bs_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
uint8_t v___x_4392_; 
v___x_4392_ = lean_usize_dec_lt(v_i_4385_, v_sz_4384_);
if (v___x_4392_ == 0)
{
lean_object* v___x_4393_; 
v___x_4393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4393_, 0, v_bs_4386_);
return v___x_4393_;
}
else
{
lean_object* v_v_4394_; lean_object* v___x_4395_; 
v_v_4394_ = lean_array_uget_borrowed(v_bs_4386_, v_i_4385_);
lean_inc(v_v_4394_);
v___x_4395_ = l_Lean_Compiler_LCNF_Decl_toMono(v_v_4394_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v_a_4396_; lean_object* v___x_4397_; lean_object* v_bs_x27_4398_; size_t v___x_4399_; size_t v___x_4400_; lean_object* v___x_4401_; 
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
lean_inc(v_a_4396_);
lean_dec_ref_known(v___x_4395_, 1);
v___x_4397_ = lean_unsigned_to_nat(0u);
v_bs_x27_4398_ = lean_array_uset(v_bs_4386_, v_i_4385_, v___x_4397_);
v___x_4399_ = ((size_t)1ULL);
v___x_4400_ = lean_usize_add(v_i_4385_, v___x_4399_);
v___x_4401_ = lean_array_uset(v_bs_x27_4398_, v_i_4385_, v_a_4396_);
v_i_4385_ = v___x_4400_;
v_bs_4386_ = v___x_4401_;
goto _start;
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
lean_dec_ref(v_bs_4386_);
v_a_4403_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___x_4395_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4395_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4403_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0___boxed(lean_object* v_sz_4411_, lean_object* v_i_4412_, lean_object* v_bs_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
size_t v_sz_boxed_4419_; size_t v_i_boxed_4420_; lean_object* v_res_4421_; 
v_sz_boxed_4419_ = lean_unbox_usize(v_sz_4411_);
lean_dec(v_sz_4411_);
v_i_boxed_4420_ = lean_unbox_usize(v_i_4412_);
lean_dec(v_i_4412_);
v_res_4421_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_boxed_4419_, v_i_boxed_4420_, v_bs_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
lean_dec(v___y_4417_);
lean_dec_ref(v___y_4416_);
lean_dec(v___y_4415_);
lean_dec_ref(v___y_4414_);
return v_res_4421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0(lean_object* v_x_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_){
_start:
{
size_t v_sz_4428_; size_t v___x_4429_; lean_object* v___x_4430_; 
v_sz_4428_ = lean_array_size(v_x_4422_);
v___x_4429_ = ((size_t)0ULL);
v___x_4430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_4428_, v___x_4429_, v_x_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
return v___x_4430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0___boxed(lean_object* v_x_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l_Lean_Compiler_LCNF_toMono___lam__0(v_x_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4520_; uint8_t v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4520_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_));
v___x_4521_ = 1;
v___x_4522_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_));
v___x_4523_ = l_Lean_registerTraceClass(v___x_4520_, v___x_4521_, v___x_4522_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2____boxed(lean_object* v_a_4524_){
_start:
{
lean_object* v_res_4525_; 
v_res_4525_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_();
return v_res_4525_;
}
}
lean_object* runtime_initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_NoncomputableAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ToMono(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_ImplementedByAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_NoncomputableAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ToMono(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
lean_object* initialize_Lean_Compiler_NoncomputableAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ToMono(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_ImplementedByAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_NoncomputableAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ToMono(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ToMono(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ToMono(builtin);
}
#ifdef __cplusplus
}
#endif
