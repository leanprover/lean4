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
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default(uint8_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(uint8_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_anyExpr;
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedLetValue_default(uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argsToMonoRedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argsToMonoRedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_redArg"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 35, 1, 83, 6, 52, 87, 186)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isTrue"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__4_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__3_value),LEAN_SCALAR_PTR_LITERAL(9, 43, 53, 182, 5, 16, 39, 1)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__4_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isFalse"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__5_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__6_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__5_value),LEAN_SCALAR_PTR_LITERAL(21, 55, 194, 143, 15, 194, 124, 204)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__6_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__7_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__8_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__7_value),LEAN_SCALAR_PTR_LITERAL(16, 96, 65, 173, 152, 155, 4, 222)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__8_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Quot"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__9_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__10_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__9_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__11_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__10_value),LEAN_SCALAR_PTR_LITERAL(255, 113, 137, 82, 82, 132, 58, 248)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__11_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "lcInv"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__12_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__9_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__13_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__12_value),LEAN_SCALAR_PTR_LITERAL(246, 129, 23, 78, 51, 209, 87, 155)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__13_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__14_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__15_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__16_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__15_value),LEAN_SCALAR_PTR_LITERAL(51, 81, 163, 94, 71, 156, 90, 186)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__16_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__17 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__17_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__18_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__17_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__18 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__18_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Compiler.LCNF.ToMono"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__19 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__19_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Compiler.LCNF.LetValue.toMono"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__20 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__20_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__21 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__21_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_LetValue_toMono___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__22;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__23 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__23_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__23_value)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__24 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__24_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__25 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__25_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__26 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__26_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__25_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__27_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__26_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__27 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__27_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__28 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__28_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__29 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__29_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__25_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__30_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__29_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__30 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__30_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__31 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__31_value;
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
static const lean_ctor_object l_Lean_Compiler_LCNF_decToMono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__25_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Compiler_LCNF_decToMono___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_decToMono___redArg___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "expected inductive type"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Compiler.LCNF.Code.toMono"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toMono___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toMono___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__4;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toMono___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__5;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__2_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__7_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__6_value),LEAN_SCALAR_PTR_LITERAL(210, 189, 86, 121, 130, 22, 242, 236)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__7_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__9_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__9_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__10_value;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__11_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__11_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__12_value;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__13_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__13_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__14_value;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__15_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__15_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__16_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__17 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__17_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ByteArray"};
static const lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(16, 14, 5, 86, 33, 2, 113, 205)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__18 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__18_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "FloatArray"};
static const lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(159, 8, 149, 159, 140, 65, 145, 29)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__19 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__19_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__20 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__20_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Thunk"};
static const lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(85, 24, 139, 128, 157, 117, 211, 220)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__21 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__21_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Task"};
static const lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(189, 131, 95, 48, 7, 243, 177, 18)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__22 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__22_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "assertion violation: c.alts.size == 1\n  "};
static const lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_trivialStructToMono___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Compiler.LCNF.trivialStructToMono"};
static const lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_trivialStructToMono___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_trivialStructToMono___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___closed__1;
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
static const lean_string_object l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toBitVec"};
static const lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4;
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
static lean_once_cell_t l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5;
static const lean_string_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "decLt"};
static const lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(168, 105, 33, 134, 172, 206, 181, 195)}};
static const lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "negSucc"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 236, 205, 0, 179, 53, 99, 201)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natAbs"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 186, 174, 182, 213, 167, 94, 168)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__3_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__20___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__20___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "abs"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__4_value),LEAN_SCALAR_PTR_LITERAL(11, 180, 28, 55, 197, 20, 206, 35)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "one"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 166, 239, 19, 130, 98, 40, 185)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sub"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__4_value),LEAN_SCALAR_PTR_LITERAL(9, 137, 41, 185, 216, 152, 145, 196)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__15_value),LEAN_SCALAR_PTR_LITERAL(147, 155, 141, 233, 87, 0, 52, 207)}};
static const lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isZero"};
static const lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(65, 194, 46, 57, 180, 54, 219, 130)}};
static const lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__4_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "decEq"};
static const lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(13, 188, 70, 193, 211, 173, 121, 176)}};
static const lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__20(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_nbuckets_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_42_ = lean_array_get_size(v_data_41_);
v___x_43_ = lean_unsigned_to_nat(2u);
v_nbuckets_44_ = lean_nat_mul(v___x_42_, v___x_43_);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_box(0);
v___x_47_ = lean_mk_array(v_nbuckets_44_, v___x_46_);
v___x_48_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2___redArg(v___x_45_, v_data_41_, v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(lean_object* v_a_49_, lean_object* v_x_50_){
_start:
{
if (lean_obj_tag(v_x_50_) == 0)
{
uint8_t v___x_51_; 
v___x_51_ = 0;
return v___x_51_;
}
else
{
lean_object* v_key_52_; lean_object* v_tail_53_; uint8_t v___x_54_; 
v_key_52_ = lean_ctor_get(v_x_50_, 0);
v_tail_53_ = lean_ctor_get(v_x_50_, 2);
v___x_54_ = l_Lean_instBEqFVarId_beq(v_key_52_, v_a_49_);
if (v___x_54_ == 0)
{
v_x_50_ = v_tail_53_;
goto _start;
}
else
{
return v___x_54_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg___boxed(lean_object* v_a_56_, lean_object* v_x_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(v_a_56_, v_x_57_);
lean_dec(v_x_57_);
lean_dec(v_a_56_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg(lean_object* v_m_60_, lean_object* v_a_61_, lean_object* v_b_62_){
_start:
{
lean_object* v_size_63_; lean_object* v_buckets_64_; lean_object* v___x_65_; uint64_t v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; uint64_t v_fold_69_; uint64_t v___x_70_; uint64_t v___x_71_; uint64_t v___x_72_; size_t v___x_73_; size_t v___x_74_; size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; lean_object* v_bkt_78_; uint8_t v___x_79_; 
v_size_63_ = lean_ctor_get(v_m_60_, 0);
v_buckets_64_ = lean_ctor_get(v_m_60_, 1);
v___x_65_ = lean_array_get_size(v_buckets_64_);
v___x_66_ = l_Lean_instHashableFVarId_hash(v_a_61_);
v___x_67_ = 32ULL;
v___x_68_ = lean_uint64_shift_right(v___x_66_, v___x_67_);
v_fold_69_ = lean_uint64_xor(v___x_66_, v___x_68_);
v___x_70_ = 16ULL;
v___x_71_ = lean_uint64_shift_right(v_fold_69_, v___x_70_);
v___x_72_ = lean_uint64_xor(v_fold_69_, v___x_71_);
v___x_73_ = lean_uint64_to_usize(v___x_72_);
v___x_74_ = lean_usize_of_nat(v___x_65_);
v___x_75_ = ((size_t)1ULL);
v___x_76_ = lean_usize_sub(v___x_74_, v___x_75_);
v___x_77_ = lean_usize_land(v___x_73_, v___x_76_);
v_bkt_78_ = lean_array_uget_borrowed(v_buckets_64_, v___x_77_);
v___x_79_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(v_a_61_, v_bkt_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_100_; 
lean_inc_ref(v_buckets_64_);
lean_inc(v_size_63_);
v_isSharedCheck_100_ = !lean_is_exclusive(v_m_60_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; lean_object* v_unused_102_; 
v_unused_101_ = lean_ctor_get(v_m_60_, 1);
lean_dec(v_unused_101_);
v_unused_102_ = lean_ctor_get(v_m_60_, 0);
lean_dec(v_unused_102_);
v___x_81_ = v_m_60_;
v_isShared_82_ = v_isSharedCheck_100_;
goto v_resetjp_80_;
}
else
{
lean_dec(v_m_60_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_100_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; lean_object* v_size_x27_84_; lean_object* v___x_85_; lean_object* v_buckets_x27_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_83_ = lean_unsigned_to_nat(1u);
v_size_x27_84_ = lean_nat_add(v_size_63_, v___x_83_);
lean_dec(v_size_63_);
lean_inc(v_bkt_78_);
v___x_85_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_85_, 0, v_a_61_);
lean_ctor_set(v___x_85_, 1, v_b_62_);
lean_ctor_set(v___x_85_, 2, v_bkt_78_);
v_buckets_x27_86_ = lean_array_uset(v_buckets_64_, v___x_77_, v___x_85_);
v___x_87_ = lean_unsigned_to_nat(4u);
v___x_88_ = lean_nat_mul(v_size_x27_84_, v___x_87_);
v___x_89_ = lean_unsigned_to_nat(3u);
v___x_90_ = lean_nat_div(v___x_88_, v___x_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_array_get_size(v_buckets_x27_86_);
v___x_92_ = lean_nat_dec_le(v___x_90_, v___x_91_);
lean_dec(v___x_90_);
if (v___x_92_ == 0)
{
lean_object* v_val_93_; lean_object* v___x_95_; 
v_val_93_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1___redArg(v_buckets_x27_86_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v_val_93_);
lean_ctor_set(v___x_81_, 0, v_size_x27_84_);
v___x_95_ = v___x_81_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_size_x27_84_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_val_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
else
{
lean_object* v___x_98_; 
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v_buckets_x27_86_);
lean_ctor_set(v___x_81_, 0, v_size_x27_84_);
v___x_98_ = v___x_81_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_size_x27_84_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_buckets_x27_86_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
else
{
lean_dec(v_b_62_);
lean_dec(v_a_61_);
return v_m_60_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___redArg(lean_object* v_param_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v_fvarId_109_; lean_object* v_type_110_; lean_object* v___y_112_; lean_object* v___y_113_; lean_object* v___y_114_; uint8_t v___x_127_; 
v_fvarId_109_ = lean_ctor_get(v_param_103_, 0);
v_type_110_ = lean_ctor_get(v_param_103_, 2);
lean_inc_ref(v_type_110_);
v___x_127_ = l_Lean_Compiler_LCNF_isTypeFormerType(v_type_110_);
if (v___x_127_ == 0)
{
v___y_112_ = v_a_105_;
v___y_113_ = v_a_106_;
v___y_114_ = v_a_107_;
goto v___jp_111_;
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_128_ = lean_st_ref_take(v_a_104_);
v___x_129_ = lean_box(0);
lean_inc(v_fvarId_109_);
v___x_130_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg(v___x_128_, v_fvarId_109_, v___x_129_);
v___x_131_ = lean_st_ref_set(v_a_104_, v___x_130_);
v___y_112_ = v_a_105_;
v___y_113_ = v_a_106_;
v___y_114_ = v_a_107_;
goto v___jp_111_;
}
v___jp_111_:
{
lean_object* v___x_115_; 
lean_inc_ref(v_type_110_);
v___x_115_ = l_Lean_Compiler_LCNF_toMonoType(v_type_110_, v___y_113_, v___y_114_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; uint8_t v___x_117_; lean_object* v___x_118_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_a_116_);
lean_dec_ref_known(v___x_115_, 1);
v___x_117_ = 0;
v___x_118_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v___x_117_, v_param_103_, v_a_116_, v___y_112_);
return v___x_118_;
}
else
{
lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_126_; 
lean_dec_ref(v_param_103_);
v_a_119_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_126_ == 0)
{
v___x_121_ = v___x_115_;
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___x_115_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_124_; 
if (v_isShared_122_ == 0)
{
v___x_124_ = v___x_121_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_a_119_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___redArg___boxed(lean_object* v_param_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Compiler_LCNF_Param_toMono___redArg(v_param_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
lean_dec(v_a_133_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono(lean_object* v_param_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Compiler_LCNF_Param_toMono___redArg(v_param_139_, v_a_140_, v_a_142_, v_a_143_, v_a_144_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___boxed(lean_object* v_param_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Compiler_LCNF_Param_toMono(v_param_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0(lean_object* v_00_u03b2_155_, lean_object* v_m_156_, lean_object* v_a_157_, lean_object* v_b_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg(v_m_156_, v_a_157_, v_b_158_);
return v___x_159_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0(lean_object* v_00_u03b2_160_, lean_object* v_a_161_, lean_object* v_x_162_){
_start:
{
uint8_t v___x_163_; 
v___x_163_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(v_a_161_, v_x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___boxed(lean_object* v_00_u03b2_164_, lean_object* v_a_165_, lean_object* v_x_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0(v_00_u03b2_164_, v_a_165_, v_x_166_);
lean_dec(v_x_166_);
lean_dec(v_a_165_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1(lean_object* v_00_u03b2_169_, lean_object* v_data_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1___redArg(v_data_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_172_, lean_object* v_i_173_, lean_object* v_source_174_, lean_object* v_target_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2___redArg(v_i_173_, v_source_174_, v_target_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_177_, lean_object* v_x_178_, lean_object* v_x_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2_spec__3___redArg(v_x_178_, v_x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___redArg(lean_object* v_arg_183_, lean_object* v_a_184_){
_start:
{
if (lean_obj_tag(v_arg_183_) == 1)
{
lean_object* v_fvarId_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v_fvarId_186_ = lean_ctor_get(v_arg_183_, 0);
v___x_187_ = lean_st_ref_get(v_a_184_);
v___x_188_ = ((lean_object*)(l_Lean_Compiler_LCNF_argToMono___redArg___closed__0));
v___x_189_ = ((lean_object*)(l_Lean_Compiler_LCNF_argToMono___redArg___closed__1));
lean_inc(v_fvarId_186_);
v___x_190_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_188_, v___x_189_, v___x_187_, v_fvarId_186_);
lean_dec(v___x_187_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; 
v___x_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_191_, 0, v_arg_183_);
return v___x_191_;
}
else
{
lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_199_; 
v_isSharedCheck_199_ = !lean_is_exclusive(v_arg_183_);
if (v_isSharedCheck_199_ == 0)
{
lean_object* v_unused_200_; 
v_unused_200_ = lean_ctor_get(v_arg_183_, 0);
lean_dec(v_unused_200_);
v___x_193_ = v_arg_183_;
v_isShared_194_ = v_isSharedCheck_199_;
goto v_resetjp_192_;
}
else
{
lean_dec(v_arg_183_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_199_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_195_ = lean_box(0);
if (v_isShared_194_ == 0)
{
lean_ctor_set_tag(v___x_193_, 0);
lean_ctor_set(v___x_193_, 0, v___x_195_);
v___x_197_ = v___x_193_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec(v_arg_183_);
v___x_201_ = lean_box(0);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___redArg___boxed(lean_object* v_arg_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_Compiler_LCNF_argToMono___redArg(v_arg_203_, v_a_204_);
lean_dec(v_a_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono(lean_object* v_arg_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
if (lean_obj_tag(v_arg_207_) == 1)
{
lean_object* v_fvarId_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v_fvarId_214_ = lean_ctor_get(v_arg_207_, 0);
v___x_215_ = lean_st_ref_get(v_a_208_);
v___x_216_ = ((lean_object*)(l_Lean_Compiler_LCNF_argToMono___redArg___closed__0));
v___x_217_ = ((lean_object*)(l_Lean_Compiler_LCNF_argToMono___redArg___closed__1));
lean_inc(v_fvarId_214_);
v___x_218_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_216_, v___x_217_, v___x_215_, v_fvarId_214_);
lean_dec(v___x_215_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; 
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v_arg_207_);
return v___x_219_;
}
else
{
lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_227_; 
v_isSharedCheck_227_ = !lean_is_exclusive(v_arg_207_);
if (v_isSharedCheck_227_ == 0)
{
lean_object* v_unused_228_; 
v_unused_228_ = lean_ctor_get(v_arg_207_, 0);
lean_dec(v_unused_228_);
v___x_221_ = v_arg_207_;
v_isShared_222_ = v_isSharedCheck_227_;
goto v_resetjp_220_;
}
else
{
lean_dec(v_arg_207_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_227_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_223_ = lean_box(0);
if (v_isShared_222_ == 0)
{
lean_ctor_set_tag(v___x_221_, 0);
lean_ctor_set(v___x_221_, 0, v___x_223_);
v___x_225_ = v___x_221_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
else
{
lean_object* v___x_229_; lean_object* v___x_230_; 
lean_dec(v_arg_207_);
v___x_229_ = lean_box(0);
v___x_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___boxed(lean_object* v_arg_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Compiler_LCNF_argToMono(v_arg_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec(v_a_232_);
return v_res_238_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(lean_object* v_m_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_buckets_241_; lean_object* v___x_242_; uint64_t v___x_243_; uint64_t v___x_244_; uint64_t v___x_245_; uint64_t v_fold_246_; uint64_t v___x_247_; uint64_t v___x_248_; uint64_t v___x_249_; size_t v___x_250_; size_t v___x_251_; size_t v___x_252_; size_t v___x_253_; size_t v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_buckets_241_ = lean_ctor_get(v_m_239_, 1);
v___x_242_ = lean_array_get_size(v_buckets_241_);
v___x_243_ = l_Lean_instHashableFVarId_hash(v_a_240_);
v___x_244_ = 32ULL;
v___x_245_ = lean_uint64_shift_right(v___x_243_, v___x_244_);
v_fold_246_ = lean_uint64_xor(v___x_243_, v___x_245_);
v___x_247_ = 16ULL;
v___x_248_ = lean_uint64_shift_right(v_fold_246_, v___x_247_);
v___x_249_ = lean_uint64_xor(v_fold_246_, v___x_248_);
v___x_250_ = lean_uint64_to_usize(v___x_249_);
v___x_251_ = lean_usize_of_nat(v___x_242_);
v___x_252_ = ((size_t)1ULL);
v___x_253_ = lean_usize_sub(v___x_251_, v___x_252_);
v___x_254_ = lean_usize_land(v___x_250_, v___x_253_);
v___x_255_ = lean_array_uget_borrowed(v_buckets_241_, v___x_254_);
v___x_256_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(v_a_240_, v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg___boxed(lean_object* v_m_257_, lean_object* v_a_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v_m_257_, v_a_258_);
lean_dec(v_a_258_);
lean_dec_ref(v_m_257_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg(lean_object* v_as_261_, size_t v_sz_262_, size_t v_i_263_, lean_object* v_b_264_, lean_object* v___y_265_){
_start:
{
uint8_t v___x_267_; 
v___x_267_ = lean_usize_dec_lt(v_i_263_, v_sz_262_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v_b_264_);
return v___x_268_;
}
else
{
lean_object* v_fst_269_; lean_object* v_snd_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_310_; 
v_fst_269_ = lean_ctor_get(v_b_264_, 0);
v_snd_270_ = lean_ctor_get(v_b_264_, 1);
v_isSharedCheck_310_ = !lean_is_exclusive(v_b_264_);
if (v_isSharedCheck_310_ == 0)
{
v___x_272_ = v_b_264_;
v_isShared_273_ = v_isSharedCheck_310_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_snd_270_);
lean_inc(v_fst_269_);
lean_dec(v_b_264_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_310_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v_monoArg_275_; lean_object* v_remainingType_276_; lean_object* v_a_284_; lean_object* v___y_286_; 
v_a_284_ = lean_array_uget_borrowed(v_as_261_, v_i_263_);
if (lean_obj_tag(v_fst_269_) == 1)
{
lean_object* v_val_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_309_; 
v_val_293_ = lean_ctor_get(v_fst_269_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v_fst_269_);
if (v_isSharedCheck_309_ == 0)
{
v___x_295_ = v_fst_269_;
v_isShared_296_ = v_isSharedCheck_309_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_val_293_);
lean_dec(v_fst_269_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_309_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
if (lean_obj_tag(v_val_293_) == 7)
{
lean_object* v_binderType_297_; lean_object* v_body_298_; lean_object* v___x_300_; 
v_binderType_297_ = lean_ctor_get(v_val_293_, 1);
lean_inc_ref(v_binderType_297_);
v_body_298_ = lean_ctor_get(v_val_293_, 2);
lean_inc_ref(v_body_298_);
lean_dec_ref_known(v_val_293_, 3);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v_body_298_);
v___x_300_ = v___x_295_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_body_298_);
v___x_300_ = v_reuseFailAlloc_308_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
uint8_t v___x_301_; 
v___x_301_ = l_Lean_Expr_isErased(v_binderType_297_);
lean_dec_ref(v_binderType_297_);
if (v___x_301_ == 0)
{
if (lean_obj_tag(v_a_284_) == 1)
{
lean_object* v_fvarId_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_fvarId_302_ = lean_ctor_get(v_a_284_, 0);
v___x_303_ = lean_st_ref_get(v___y_265_);
v___x_304_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_303_, v_fvarId_302_);
lean_dec(v___x_303_);
if (v___x_304_ == 0)
{
lean_inc_ref(v_a_284_);
v_monoArg_275_ = v_a_284_;
v_remainingType_276_ = v___x_300_;
goto v___jp_274_;
}
else
{
lean_object* v___x_305_; 
v___x_305_ = lean_box(0);
v_monoArg_275_ = v___x_305_;
v_remainingType_276_ = v___x_300_;
goto v___jp_274_;
}
}
else
{
lean_object* v___x_306_; 
v___x_306_ = lean_box(0);
v_monoArg_275_ = v___x_306_;
v_remainingType_276_ = v___x_300_;
goto v___jp_274_;
}
}
else
{
lean_object* v___x_307_; 
v___x_307_ = lean_box(0);
v_monoArg_275_ = v___x_307_;
v_remainingType_276_ = v___x_300_;
goto v___jp_274_;
}
}
}
else
{
lean_del_object(v___x_295_);
lean_dec(v_val_293_);
v___y_286_ = v___y_265_;
goto v___jp_285_;
}
}
}
else
{
lean_dec(v_fst_269_);
v___y_286_ = v___y_265_;
goto v___jp_285_;
}
v___jp_274_:
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = lean_array_push(v_snd_270_, v_monoArg_275_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 1, v___x_277_);
lean_ctor_set(v___x_272_, 0, v_remainingType_276_);
v___x_279_ = v___x_272_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_remainingType_276_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v___x_277_);
v___x_279_ = v_reuseFailAlloc_283_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
size_t v___x_280_; size_t v___x_281_; 
v___x_280_ = ((size_t)1ULL);
v___x_281_ = lean_usize_add(v_i_263_, v___x_280_);
v_i_263_ = v___x_281_;
v_b_264_ = v___x_279_;
goto _start;
}
}
v___jp_285_:
{
lean_object* v___x_287_; 
v___x_287_ = lean_box(0);
if (lean_obj_tag(v_a_284_) == 1)
{
lean_object* v_fvarId_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v_fvarId_288_ = lean_ctor_get(v_a_284_, 0);
v___x_289_ = lean_st_ref_get(v___y_286_);
v___x_290_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_289_, v_fvarId_288_);
lean_dec(v___x_289_);
if (v___x_290_ == 0)
{
lean_inc_ref(v_a_284_);
v_monoArg_275_ = v_a_284_;
v_remainingType_276_ = v___x_287_;
goto v___jp_274_;
}
else
{
lean_object* v___x_291_; 
v___x_291_ = lean_box(0);
v_monoArg_275_ = v___x_291_;
v_remainingType_276_ = v___x_287_;
goto v___jp_274_;
}
}
else
{
lean_object* v___x_292_; 
v___x_292_ = lean_box(0);
v_monoArg_275_ = v___x_292_;
v_remainingType_276_ = v___x_287_;
goto v___jp_274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg___boxed(lean_object* v_as_311_, lean_object* v_sz_312_, lean_object* v_i_313_, lean_object* v_b_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
size_t v_sz_boxed_317_; size_t v_i_boxed_318_; lean_object* v_res_319_; 
v_sz_boxed_317_ = lean_unbox_usize(v_sz_312_);
lean_dec(v_sz_312_);
v_i_boxed_318_ = lean_unbox_usize(v_i_313_);
lean_dec(v_i_313_);
v_res_319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg(v_as_311_, v_sz_boxed_317_, v_i_boxed_318_, v_b_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v_as_311_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argsToMonoWithFnType(lean_object* v_args_320_, lean_object* v_type_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_remainingType_328_; lean_object* v___x_329_; lean_object* v_result_330_; lean_object* v___x_331_; size_t v_sz_332_; size_t v___x_333_; lean_object* v___x_334_; 
v_remainingType_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_remainingType_328_, 0, v_type_321_);
v___x_329_ = lean_array_get_size(v_args_320_);
v_result_330_ = lean_mk_empty_array_with_capacity(v___x_329_);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v_remainingType_328_);
lean_ctor_set(v___x_331_, 1, v_result_330_);
v_sz_332_ = lean_array_size(v_args_320_);
v___x_333_ = ((size_t)0ULL);
v___x_334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg(v_args_320_, v_sz_332_, v___x_333_, v___x_331_, v_a_322_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_343_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_343_ == 0)
{
v___x_337_ = v___x_334_;
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v_snd_339_; lean_object* v___x_341_; 
v_snd_339_ = lean_ctor_get(v_a_335_, 1);
lean_inc(v_snd_339_);
lean_dec(v_a_335_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v_snd_339_);
v___x_341_ = v___x_337_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_snd_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
v_a_344_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_334_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_334_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argsToMonoWithFnType___boxed(lean_object* v_args_352_, lean_object* v_type_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_Compiler_LCNF_argsToMonoWithFnType(v_args_352_, v_type_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_args_352_);
return v_res_360_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0(lean_object* v_00_u03b2_361_, lean_object* v_m_362_, lean_object* v_a_363_){
_start:
{
uint8_t v___x_364_; 
v___x_364_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v_m_362_, v_a_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___boxed(lean_object* v_00_u03b2_365_, lean_object* v_m_366_, lean_object* v_a_367_){
_start:
{
uint8_t v_res_368_; lean_object* v_r_369_; 
v_res_368_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0(v_00_u03b2_365_, v_m_366_, v_a_367_);
lean_dec(v_a_367_);
lean_dec_ref(v_m_366_);
v_r_369_ = lean_box(v_res_368_);
return v_r_369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1(lean_object* v_as_370_, size_t v_sz_371_, size_t v_i_372_, lean_object* v_b_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg(v_as_370_, v_sz_371_, v_i_372_, v_b_373_, v___y_374_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___boxed(lean_object* v_as_381_, lean_object* v_sz_382_, lean_object* v_i_383_, lean_object* v_b_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
size_t v_sz_boxed_391_; size_t v_i_boxed_392_; lean_object* v_res_393_; 
v_sz_boxed_391_ = lean_unbox_usize(v_sz_382_);
lean_dec(v_sz_382_);
v_i_boxed_392_ = lean_unbox_usize(v_i_383_);
lean_dec(v_i_383_);
v_res_393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1(v_as_381_, v_sz_boxed_391_, v_i_boxed_392_, v_b_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v_as_381_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2___redArg(lean_object* v_a_394_, lean_object* v_b_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_array_398_; lean_object* v_start_399_; lean_object* v_stop_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_421_; 
v_array_398_ = lean_ctor_get(v_a_394_, 0);
v_start_399_ = lean_ctor_get(v_a_394_, 1);
v_stop_400_ = lean_ctor_get(v_a_394_, 2);
v_isSharedCheck_421_ = !lean_is_exclusive(v_a_394_);
if (v_isSharedCheck_421_ == 0)
{
v___x_402_ = v_a_394_;
v_isShared_403_ = v_isSharedCheck_421_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_stop_400_);
lean_inc(v_start_399_);
lean_inc(v_array_398_);
lean_dec(v_a_394_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_421_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
uint8_t v___x_404_; 
v___x_404_ = lean_nat_dec_lt(v_start_399_, v_stop_400_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
lean_del_object(v___x_402_);
lean_dec(v_stop_400_);
lean_dec(v_start_399_);
lean_dec_ref(v_array_398_);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v_b_395_);
return v___x_405_;
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_406_ = lean_unsigned_to_nat(1u);
v___x_407_ = lean_nat_add(v_start_399_, v___x_406_);
lean_inc_ref(v_array_398_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 1, v___x_407_);
v___x_409_ = v___x_402_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_array_398_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v_stop_400_);
v___x_409_ = v_reuseFailAlloc_420_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v_a_411_; lean_object* v___x_414_; 
v___x_414_ = lean_array_fget(v_array_398_, v_start_399_);
lean_dec(v_start_399_);
lean_dec_ref(v_array_398_);
if (lean_obj_tag(v___x_414_) == 1)
{
lean_object* v_fvarId_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v_fvarId_415_ = lean_ctor_get(v___x_414_, 0);
v___x_416_ = lean_st_ref_get(v___y_396_);
v___x_417_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_416_, v_fvarId_415_);
lean_dec(v___x_416_);
if (v___x_417_ == 0)
{
v_a_411_ = v___x_414_;
goto v___jp_410_;
}
else
{
lean_object* v___x_418_; 
lean_dec_ref_known(v___x_414_, 1);
v___x_418_ = lean_box(0);
v_a_411_ = v___x_418_;
goto v___jp_410_;
}
}
else
{
lean_object* v___x_419_; 
lean_dec(v___x_414_);
v___x_419_ = lean_box(0);
v_a_411_ = v___x_419_;
goto v___jp_410_;
}
v___jp_410_:
{
lean_object* v___x_412_; 
v___x_412_ = lean_array_push(v_b_395_, v_a_411_);
v_a_394_ = v___x_409_;
v_b_395_ = v___x_412_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2___redArg___boxed(lean_object* v_a_422_, lean_object* v_b_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2___redArg(v_a_422_, v_b_423_, v___y_424_);
lean_dec(v___y_424_);
return v_res_426_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0(void){
_start:
{
uint8_t v___x_427_; lean_object* v___x_428_; 
v___x_427_ = 0;
v___x_428_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg(lean_object* v_params_429_, lean_object* v_fvarId_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_fvarId_435_; uint8_t v___x_436_; 
v___x_433_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_434_ = lean_array_get_borrowed(v___x_433_, v_params_429_, v_a_431_);
v_fvarId_435_ = lean_ctor_get(v___x_434_, 0);
v___x_436_ = l_Lean_instBEqFVarId_beq(v_fvarId_435_, v_fvarId_430_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_unsigned_to_nat(1u);
v___x_438_ = lean_nat_add(v_a_431_, v___x_437_);
lean_dec(v_a_431_);
v_a_431_ = v___x_438_;
goto _start;
}
else
{
lean_object* v___x_440_; 
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v_a_431_);
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___boxed(lean_object* v_params_441_, lean_object* v_fvarId_442_, lean_object* v_a_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg(v_params_441_, v_fvarId_442_, v_a_443_);
lean_dec(v_fvarId_442_);
lean_dec_ref(v_params_441_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__1(lean_object* v_params_446_, lean_object* v_args_447_, lean_object* v_as_448_, size_t v_sz_449_, size_t v_i_450_, lean_object* v_b_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_a_459_; uint8_t v___x_463_; 
v___x_463_ = lean_usize_dec_lt(v_i_450_, v_sz_449_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; 
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v_b_451_);
return v___x_464_;
}
else
{
lean_object* v_fst_465_; lean_object* v_snd_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_498_; 
v_fst_465_ = lean_ctor_get(v_b_451_, 0);
v_snd_466_ = lean_ctor_get(v_b_451_, 1);
v_isSharedCheck_498_ = !lean_is_exclusive(v_b_451_);
if (v_isSharedCheck_498_ == 0)
{
v___x_468_ = v_b_451_;
v_isShared_469_ = v_isSharedCheck_498_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_snd_466_);
lean_inc(v_fst_465_);
lean_dec(v_b_451_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_498_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v_a_470_; 
v_a_470_ = lean_array_uget_borrowed(v_as_448_, v_i_450_);
if (lean_obj_tag(v_a_470_) == 1)
{
lean_object* v_fvarId_471_; lean_object* v___x_472_; 
v_fvarId_471_ = lean_ctor_get(v_a_470_, 0);
v___x_472_ = l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg(v_params_446_, v_fvarId_471_, v_snd_466_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v_a_475_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_472_, 1);
v___x_482_ = lean_box(0);
v___x_483_ = lean_array_get_borrowed(v___x_482_, v_args_447_, v_a_473_);
if (lean_obj_tag(v___x_483_) == 1)
{
lean_object* v_fvarId_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v_fvarId_484_ = lean_ctor_get(v___x_483_, 0);
v___x_485_ = lean_st_ref_get(v___y_452_);
v___x_486_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_485_, v_fvarId_484_);
lean_dec(v___x_485_);
if (v___x_486_ == 0)
{
lean_inc_ref(v___x_483_);
v_a_475_ = v___x_483_;
goto v___jp_474_;
}
else
{
v_a_475_ = v___x_482_;
goto v___jp_474_;
}
}
else
{
v_a_475_ = v___x_482_;
goto v___jp_474_;
}
v___jp_474_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_nat_add(v_a_473_, v___x_476_);
lean_dec(v_a_473_);
v___x_478_ = lean_array_push(v_fst_465_, v_a_475_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v___x_477_);
lean_ctor_set(v___x_468_, 0, v___x_478_);
v___x_480_ = v___x_468_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v___x_477_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
v_a_459_ = v___x_480_;
goto v___jp_458_;
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
lean_del_object(v___x_468_);
lean_dec(v_fst_465_);
v_a_487_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_472_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_472_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
else
{
lean_object* v___x_496_; 
if (v_isShared_469_ == 0)
{
v___x_496_ = v___x_468_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_fst_465_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_snd_466_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
v_a_459_ = v___x_496_;
goto v___jp_458_;
}
}
}
}
v___jp_458_:
{
size_t v___x_460_; size_t v___x_461_; 
v___x_460_ = ((size_t)1ULL);
v___x_461_ = lean_usize_add(v_i_450_, v___x_460_);
v_i_450_ = v___x_461_;
v_b_451_ = v_a_459_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__1___boxed(lean_object* v_params_499_, lean_object* v_args_500_, lean_object* v_as_501_, lean_object* v_sz_502_, lean_object* v_i_503_, lean_object* v_b_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
size_t v_sz_boxed_511_; size_t v_i_boxed_512_; lean_object* v_res_513_; 
v_sz_boxed_511_ = lean_unbox_usize(v_sz_502_);
lean_dec(v_sz_502_);
v_i_boxed_512_ = lean_unbox_usize(v_i_503_);
lean_dec(v_i_503_);
v_res_513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__1(v_params_499_, v_args_500_, v_as_501_, v_sz_boxed_511_, v_i_boxed_512_, v_b_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v_as_501_);
lean_dec_ref(v_args_500_);
lean_dec_ref(v_params_499_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argsToMonoRedArg(lean_object* v_args_519_, lean_object* v_params_520_, lean_object* v_redArgs_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; size_t v_sz_530_; size_t v___x_531_; lean_object* v___x_532_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = ((lean_object*)(l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__1));
v_sz_530_ = lean_array_size(v_redArgs_521_);
v___x_531_ = ((size_t)0ULL);
v___x_532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__1(v_params_520_, v_args_519_, v_redArgs_521_, v_sz_530_, v___x_531_, v___x_529_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v_fst_534_; lean_object* v_lower_536_; lean_object* v_upper_537_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_532_, 1);
v_fst_534_ = lean_ctor_get(v_a_533_, 0);
lean_inc(v_fst_534_);
lean_dec(v_a_533_);
v___x_540_ = lean_array_get_size(v_params_520_);
v___x_541_ = lean_array_get_size(v_args_519_);
v___x_542_ = lean_nat_dec_le(v___x_540_, v___x_528_);
if (v___x_542_ == 0)
{
v_lower_536_ = v___x_540_;
v_upper_537_ = v___x_541_;
goto v___jp_535_;
}
else
{
v_lower_536_ = v___x_528_;
v_upper_537_ = v___x_541_;
goto v___jp_535_;
}
v___jp_535_:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = l_Array_toSubarray___redArg(v_args_519_, v_lower_536_, v_upper_537_);
v___x_539_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2___redArg(v___x_538_, v_fst_534_, v_a_522_);
return v___x_539_;
}
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_dec_ref(v_args_519_);
v_a_543_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_532_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_532_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argsToMonoRedArg___boxed(lean_object* v_args_551_, lean_object* v_params_552_, lean_object* v_redArgs_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Compiler_LCNF_argsToMonoRedArg(v_args_551_, v_params_552_, v_redArgs_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec(v_a_554_);
lean_dec_ref(v_redArgs_553_);
lean_dec_ref(v_params_552_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0(lean_object* v_params_561_, lean_object* v_fvarId_562_, lean_object* v_inst_563_, lean_object* v_a_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg(v_params_561_, v_fvarId_562_, v_a_564_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___boxed(lean_object* v_params_572_, lean_object* v_fvarId_573_, lean_object* v_inst_574_, lean_object* v_a_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0(v_params_572_, v_fvarId_573_, v_inst_574_, v_a_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec(v_fvarId_573_);
lean_dec_ref(v_params_572_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2(lean_object* v_inst_583_, lean_object* v_R_584_, lean_object* v_a_585_, lean_object* v_b_586_, lean_object* v_c_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2___redArg(v_a_585_, v_b_586_, v___y_588_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2___boxed(lean_object* v_inst_595_, lean_object* v_R_596_, lean_object* v_a_597_, lean_object* v_b_598_, lean_object* v_c_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2(v_inst_595_, v_R_596_, v_a_597_, v_b_598_, v_c_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(lean_object* v_a_607_, lean_object* v_b_608_){
_start:
{
lean_object* v_array_609_; lean_object* v_start_610_; lean_object* v_stop_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_624_; 
v_array_609_ = lean_ctor_get(v_a_607_, 0);
v_start_610_ = lean_ctor_get(v_a_607_, 1);
v_stop_611_ = lean_ctor_get(v_a_607_, 2);
v_isSharedCheck_624_ = !lean_is_exclusive(v_a_607_);
if (v_isSharedCheck_624_ == 0)
{
v___x_613_ = v_a_607_;
v_isShared_614_ = v_isSharedCheck_624_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_stop_611_);
lean_inc(v_start_610_);
lean_inc(v_array_609_);
lean_dec(v_a_607_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_624_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
uint8_t v___x_615_; 
v___x_615_ = lean_nat_dec_lt(v_start_610_, v_stop_611_);
if (v___x_615_ == 0)
{
lean_del_object(v___x_613_);
lean_dec(v_stop_611_);
lean_dec(v_start_610_);
lean_dec_ref(v_array_609_);
return v_b_608_;
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_616_ = lean_unsigned_to_nat(1u);
v___x_617_ = lean_nat_add(v_start_610_, v___x_616_);
lean_inc_ref(v_array_609_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v___x_617_);
v___x_619_ = v___x_613_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_array_609_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_623_, 2, v_stop_611_);
v___x_619_ = v_reuseFailAlloc_623_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_array_fget(v_array_609_, v_start_610_);
lean_dec(v_start_610_);
lean_dec_ref(v_array_609_);
v___x_621_ = lean_array_push(v_b_608_, v___x_620_);
v_a_607_ = v___x_619_;
v_b_608_ = v___x_621_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(size_t v_sz_625_, size_t v_i_626_, lean_object* v_bs_627_, lean_object* v___y_628_){
_start:
{
uint8_t v___x_630_; 
v___x_630_ = lean_usize_dec_lt(v_i_626_, v_sz_625_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; 
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v_bs_627_);
return v___x_631_;
}
else
{
lean_object* v_v_632_; lean_object* v___x_633_; lean_object* v_bs_x27_634_; lean_object* v_a_636_; 
v_v_632_ = lean_array_uget(v_bs_627_, v_i_626_);
v___x_633_ = lean_unsigned_to_nat(0u);
v_bs_x27_634_ = lean_array_uset(v_bs_627_, v_i_626_, v___x_633_);
if (lean_obj_tag(v_v_632_) == 1)
{
lean_object* v_fvarId_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v_fvarId_641_ = lean_ctor_get(v_v_632_, 0);
v___x_642_ = lean_st_ref_get(v___y_628_);
v___x_643_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_642_, v_fvarId_641_);
lean_dec(v___x_642_);
if (v___x_643_ == 0)
{
v_a_636_ = v_v_632_;
goto v___jp_635_;
}
else
{
lean_object* v___x_644_; 
lean_dec_ref_known(v_v_632_, 1);
v___x_644_ = lean_box(0);
v_a_636_ = v___x_644_;
goto v___jp_635_;
}
}
else
{
lean_object* v___x_645_; 
lean_dec(v_v_632_);
v___x_645_ = lean_box(0);
v_a_636_ = v___x_645_;
goto v___jp_635_;
}
v___jp_635_:
{
size_t v___x_637_; size_t v___x_638_; lean_object* v___x_639_; 
v___x_637_ = ((size_t)1ULL);
v___x_638_ = lean_usize_add(v_i_626_, v___x_637_);
v___x_639_ = lean_array_uset(v_bs_x27_634_, v_i_626_, v_a_636_);
v_i_626_ = v___x_638_;
v_bs_627_ = v___x_639_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg___boxed(lean_object* v_sz_646_, lean_object* v_i_647_, lean_object* v_bs_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
size_t v_sz_boxed_651_; size_t v_i_boxed_652_; lean_object* v_res_653_; 
v_sz_boxed_651_ = lean_unbox_usize(v_sz_646_);
lean_dec(v_sz_646_);
v_i_boxed_652_ = lean_unbox_usize(v_i_647_);
lean_dec(v_i_647_);
v_res_653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_boxed_651_, v_i_boxed_652_, v_bs_648_, v___y_649_);
lean_dec(v___y_649_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ctorAppToMono(lean_object* v_ctorInfo_654_, lean_object* v_args_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_toConstantVal_662_; lean_object* v_numParams_663_; lean_object* v___x_664_; lean_object* v_argsNewParams_665_; lean_object* v_lower_667_; lean_object* v_upper_668_; lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v_toConstantVal_662_ = lean_ctor_get(v_ctorInfo_654_, 0);
lean_inc_ref(v_toConstantVal_662_);
v_numParams_663_ = lean_ctor_get(v_ctorInfo_654_, 3);
lean_inc_n(v_numParams_663_, 2);
lean_dec_ref(v_ctorInfo_654_);
v___x_664_ = lean_box(0);
v_argsNewParams_665_ = lean_mk_array(v_numParams_663_, v___x_664_);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_array_get_size(v_args_655_);
v___x_705_ = lean_nat_dec_le(v_numParams_663_, v___x_703_);
if (v___x_705_ == 0)
{
v_lower_667_ = v_numParams_663_;
v_upper_668_ = v___x_704_;
goto v___jp_666_;
}
else
{
lean_dec(v_numParams_663_);
v_lower_667_ = v___x_703_;
v_upper_668_ = v___x_704_;
goto v___jp_666_;
}
v___jp_666_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; size_t v_sz_672_; size_t v___x_673_; lean_object* v___x_674_; 
v___x_669_ = l_Array_toSubarray___redArg(v_args_655_, v_lower_667_, v_upper_668_);
v___x_670_ = ((lean_object*)(l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0));
v___x_671_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(v___x_669_, v___x_670_);
v_sz_672_ = lean_array_size(v___x_671_);
v___x_673_ = ((size_t)0ULL);
v___x_674_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_672_, v___x_673_, v___x_671_, v_a_656_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_694_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_694_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_694_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_694_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v_name_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_691_; 
v_name_679_ = lean_ctor_get(v_toConstantVal_662_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v_toConstantVal_662_);
if (v_isSharedCheck_691_ == 0)
{
lean_object* v_unused_692_; lean_object* v_unused_693_; 
v_unused_692_ = lean_ctor_get(v_toConstantVal_662_, 2);
lean_dec(v_unused_692_);
v_unused_693_ = lean_ctor_get(v_toConstantVal_662_, 1);
lean_dec(v_unused_693_);
v___x_681_ = v_toConstantVal_662_;
v_isShared_682_ = v_isSharedCheck_691_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_name_679_);
lean_dec(v_toConstantVal_662_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_691_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_683_ = l_Array_append___redArg(v_argsNewParams_665_, v_a_675_);
lean_dec(v_a_675_);
v___x_684_ = lean_box(0);
if (v_isShared_682_ == 0)
{
lean_ctor_set_tag(v___x_681_, 3);
lean_ctor_set(v___x_681_, 2, v___x_683_);
lean_ctor_set(v___x_681_, 1, v___x_684_);
v___x_686_ = v___x_681_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_name_679_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_690_, 2, v___x_683_);
v___x_686_ = v_reuseFailAlloc_690_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_688_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_686_);
v___x_688_ = v___x_677_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_dec_ref(v_argsNewParams_665_);
lean_dec_ref(v_toConstantVal_662_);
v_a_695_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_674_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_674_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ctorAppToMono___boxed(lean_object* v_ctorInfo_706_, lean_object* v_args_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_Compiler_LCNF_ctorAppToMono(v_ctorInfo_706_, v_args_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0(lean_object* v_inst_715_, lean_object* v_R_716_, lean_object* v_a_717_, lean_object* v_b_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(v_a_717_, v_b_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1(size_t v_sz_720_, size_t v_i_721_, lean_object* v_bs_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_720_, v_i_721_, v_bs_722_, v___y_723_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___boxed(lean_object* v_sz_730_, lean_object* v_i_731_, lean_object* v_bs_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
size_t v_sz_boxed_739_; size_t v_i_boxed_740_; lean_object* v_res_741_; 
v_sz_boxed_739_ = lean_unbox_usize(v_sz_730_);
lean_dec(v_sz_730_);
v_i_boxed_740_ = lean_unbox_usize(v_i_731_);
lean_dec(v_i_731_);
v_res_741_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1(v_sz_boxed_739_, v_i_boxed_740_, v_bs_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
return v_res_741_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0(void){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_instMonadEIO(lean_box(0));
return v___x_742_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5(void){
_start:
{
uint8_t v___x_747_; lean_object* v___x_748_; 
v___x_747_ = 0;
v___x_748_ = l_Lean_Compiler_LCNF_instInhabitedLetValue_default(v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(lean_object* v_msg_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v_toApplicative_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_820_; 
v___x_756_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_757_ = l_StateRefT_x27_instMonad___redArg(v___x_756_);
v_toApplicative_758_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; 
v_unused_821_ = lean_ctor_get(v___x_757_, 1);
lean_dec(v_unused_821_);
v___x_760_ = v___x_757_;
v_isShared_761_ = v_isSharedCheck_820_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_toApplicative_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_820_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v_toFunctor_762_; lean_object* v_toSeq_763_; lean_object* v_toSeqLeft_764_; lean_object* v_toSeqRight_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_818_; 
v_toFunctor_762_ = lean_ctor_get(v_toApplicative_758_, 0);
v_toSeq_763_ = lean_ctor_get(v_toApplicative_758_, 2);
v_toSeqLeft_764_ = lean_ctor_get(v_toApplicative_758_, 3);
v_toSeqRight_765_ = lean_ctor_get(v_toApplicative_758_, 4);
v_isSharedCheck_818_ = !lean_is_exclusive(v_toApplicative_758_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; 
v_unused_819_ = lean_ctor_get(v_toApplicative_758_, 1);
lean_dec(v_unused_819_);
v___x_767_ = v_toApplicative_758_;
v_isShared_768_ = v_isSharedCheck_818_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_toSeqRight_765_);
lean_inc(v_toSeqLeft_764_);
lean_inc(v_toSeq_763_);
lean_inc(v_toFunctor_762_);
lean_dec(v_toApplicative_758_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_818_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___f_769_; lean_object* v___f_770_; lean_object* v___f_771_; lean_object* v___f_772_; lean_object* v___x_773_; lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___f_776_; lean_object* v___x_778_; 
v___f_769_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_770_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_762_);
v___f_771_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_771_, 0, v_toFunctor_762_);
v___f_772_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_772_, 0, v_toFunctor_762_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v___f_771_);
lean_ctor_set(v___x_773_, 1, v___f_772_);
v___f_774_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_774_, 0, v_toSeqRight_765_);
v___f_775_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_775_, 0, v_toSeqLeft_764_);
v___f_776_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_776_, 0, v_toSeq_763_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 4, v___f_774_);
lean_ctor_set(v___x_767_, 3, v___f_775_);
lean_ctor_set(v___x_767_, 2, v___f_776_);
lean_ctor_set(v___x_767_, 1, v___f_769_);
lean_ctor_set(v___x_767_, 0, v___x_773_);
v___x_778_ = v___x_767_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___f_769_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v___f_776_);
lean_ctor_set(v_reuseFailAlloc_817_, 3, v___f_775_);
lean_ctor_set(v_reuseFailAlloc_817_, 4, v___f_774_);
v___x_778_ = v_reuseFailAlloc_817_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_780_; 
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v___f_770_);
lean_ctor_set(v___x_760_, 0, v___x_778_);
v___x_780_ = v___x_760_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v___f_770_);
v___x_780_ = v_reuseFailAlloc_816_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; lean_object* v_toApplicative_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_814_; 
v___x_781_ = l_StateRefT_x27_instMonad___redArg(v___x_780_);
v_toApplicative_782_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v___x_781_, 1);
lean_dec(v_unused_815_);
v___x_784_ = v___x_781_;
v_isShared_785_ = v_isSharedCheck_814_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_toApplicative_782_);
lean_dec(v___x_781_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_814_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v_toFunctor_786_; lean_object* v_toSeq_787_; lean_object* v_toSeqLeft_788_; lean_object* v_toSeqRight_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_812_; 
v_toFunctor_786_ = lean_ctor_get(v_toApplicative_782_, 0);
v_toSeq_787_ = lean_ctor_get(v_toApplicative_782_, 2);
v_toSeqLeft_788_ = lean_ctor_get(v_toApplicative_782_, 3);
v_toSeqRight_789_ = lean_ctor_get(v_toApplicative_782_, 4);
v_isSharedCheck_812_ = !lean_is_exclusive(v_toApplicative_782_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; 
v_unused_813_ = lean_ctor_get(v_toApplicative_782_, 1);
lean_dec(v_unused_813_);
v___x_791_ = v_toApplicative_782_;
v_isShared_792_ = v_isSharedCheck_812_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_toSeqRight_789_);
lean_inc(v_toSeqLeft_788_);
lean_inc(v_toSeq_787_);
lean_inc(v_toFunctor_786_);
lean_dec(v_toApplicative_782_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_812_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___f_793_; lean_object* v___f_794_; lean_object* v___f_795_; lean_object* v___f_796_; lean_object* v___x_797_; lean_object* v___f_798_; lean_object* v___f_799_; lean_object* v___f_800_; lean_object* v___x_802_; 
v___f_793_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_794_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_786_);
v___f_795_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_795_, 0, v_toFunctor_786_);
v___f_796_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_796_, 0, v_toFunctor_786_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v___f_795_);
lean_ctor_set(v___x_797_, 1, v___f_796_);
v___f_798_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_798_, 0, v_toSeqRight_789_);
v___f_799_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_799_, 0, v_toSeqLeft_788_);
v___f_800_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_800_, 0, v_toSeq_787_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 4, v___f_798_);
lean_ctor_set(v___x_791_, 3, v___f_799_);
lean_ctor_set(v___x_791_, 2, v___f_800_);
lean_ctor_set(v___x_791_, 1, v___f_793_);
lean_ctor_set(v___x_791_, 0, v___x_797_);
v___x_802_ = v___x_791_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___f_793_);
lean_ctor_set(v_reuseFailAlloc_811_, 2, v___f_800_);
lean_ctor_set(v_reuseFailAlloc_811_, 3, v___f_799_);
lean_ctor_set(v_reuseFailAlloc_811_, 4, v___f_798_);
v___x_802_ = v_reuseFailAlloc_811_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_804_; 
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v___f_794_);
lean_ctor_set(v___x_784_, 0, v___x_802_);
v___x_804_ = v___x_784_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v___f_794_);
v___x_804_ = v_reuseFailAlloc_810_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_13671__overap_808_; lean_object* v___x_809_; 
v___x_805_ = l_StateRefT_x27_instMonad___redArg(v___x_804_);
v___x_806_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5);
v___x_807_ = l_instInhabitedOfMonad___redArg(v___x_805_, v___x_806_);
v___x_13671__overap_808_ = lean_panic_fn_borrowed(v___x_807_, v_msg_749_);
lean_dec(v___x_807_);
lean_inc(v___y_754_);
lean_inc_ref(v___y_753_);
lean_inc(v___y_752_);
lean_inc_ref(v___y_751_);
lean_inc(v___y_750_);
v___x_809_ = lean_apply_6(v___x_13671__overap_808_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, lean_box(0));
return v___x_809_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___boxed(lean_object* v_msg_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(v_msg_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(lean_object* v_upperBound_830_, lean_object* v_args_831_, lean_object* v_a_832_, lean_object* v_b_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_a_837_; uint8_t v___x_842_; 
v___x_842_ = lean_nat_dec_lt(v_a_832_, v_upperBound_830_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; 
lean_dec(v_a_832_);
v___x_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_843_, 0, v_b_833_);
return v___x_843_;
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_box(0);
v___x_845_ = lean_array_get_borrowed(v___x_844_, v_args_831_, v_a_832_);
if (lean_obj_tag(v___x_845_) == 1)
{
lean_object* v_fvarId_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v_fvarId_846_ = lean_ctor_get(v___x_845_, 0);
v___x_847_ = lean_st_ref_get(v___y_834_);
v___x_848_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_847_, v_fvarId_846_);
lean_dec(v___x_847_);
if (v___x_848_ == 0)
{
lean_inc_ref(v___x_845_);
v_a_837_ = v___x_845_;
goto v___jp_836_;
}
else
{
v_a_837_ = v___x_844_;
goto v___jp_836_;
}
}
else
{
v_a_837_ = v___x_844_;
goto v___jp_836_;
}
}
v___jp_836_:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_838_ = lean_array_push(v_b_833_, v_a_837_);
v___x_839_ = lean_unsigned_to_nat(1u);
v___x_840_ = lean_nat_add(v_a_832_, v___x_839_);
lean_dec(v_a_832_);
v_a_832_ = v___x_840_;
v_b_833_ = v___x_838_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg___boxed(lean_object* v_upperBound_849_, lean_object* v_args_850_, lean_object* v_a_851_, lean_object* v_b_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v_upperBound_849_, v_args_850_, v_a_851_, v_b_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v_args_850_);
lean_dec(v_upperBound_849_);
return v_res_855_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LetValue_toMono___closed__22(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_893_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_894_ = lean_unsigned_to_nat(6u);
v___x_895_ = lean_unsigned_to_nat(109u);
v___x_896_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__20));
v___x_897_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_898_ = l_mkPanicMessageWithDecl(v___x_897_, v___x_896_, v___x_895_, v___x_894_, v___x_893_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono(lean_object* v_e_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
switch(lean_obj_tag(v_e_920_))
{
case 2:
{
lean_object* v_typeName_927_; lean_object* v_idx_928_; lean_object* v_struct_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v_typeName_927_ = lean_ctor_get(v_e_920_, 0);
v_idx_928_ = lean_ctor_get(v_e_920_, 1);
v_struct_929_ = lean_ctor_get(v_e_920_, 2);
v___x_930_ = lean_st_ref_get(v_a_921_);
v___x_931_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_930_, v_struct_929_);
lean_dec(v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; 
lean_inc(v_typeName_927_);
v___x_932_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_typeName_927_, v_a_924_, v_a_925_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_952_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_952_ == 0)
{
v___x_935_ = v___x_932_;
v_isShared_936_ = v_isSharedCheck_952_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_952_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
if (lean_obj_tag(v_a_933_) == 1)
{
lean_object* v_val_937_; lean_object* v_fieldIdx_938_; uint8_t v___x_939_; 
lean_inc(v_struct_929_);
lean_inc(v_idx_928_);
lean_dec_ref_known(v_e_920_, 3);
v_val_937_ = lean_ctor_get(v_a_933_, 0);
lean_inc(v_val_937_);
lean_dec_ref_known(v_a_933_, 1);
v_fieldIdx_938_ = lean_ctor_get(v_val_937_, 2);
lean_inc(v_fieldIdx_938_);
lean_dec(v_val_937_);
v___x_939_ = lean_nat_dec_eq(v_fieldIdx_938_, v_idx_928_);
lean_dec(v_idx_928_);
lean_dec(v_fieldIdx_938_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; lean_object* v___x_942_; 
lean_dec(v_struct_929_);
v___x_940_ = lean_box(1);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_940_);
v___x_942_ = v___x_935_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_940_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
else
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_944_ = ((lean_object*)(l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0));
v___x_945_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_945_, 0, v_struct_929_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_945_);
v___x_947_ = v___x_935_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_945_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
else
{
lean_object* v___x_950_; 
lean_dec(v_a_933_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v_e_920_);
v___x_950_ = v___x_935_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_e_920_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec_ref_known(v_e_920_, 3);
v_a_953_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_932_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_932_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
else
{
lean_object* v___x_961_; lean_object* v___x_962_; 
lean_dec_ref_known(v_e_920_, 3);
v___x_961_ = lean_box(1);
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
return v___x_962_;
}
}
case 3:
{
lean_object* v_declName_963_; lean_object* v_args_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_1171_; 
v_declName_963_ = lean_ctor_get(v_e_920_, 0);
v_args_964_ = lean_ctor_get(v_e_920_, 2);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_e_920_);
if (v_isSharedCheck_1171_ == 0)
{
lean_object* v_unused_1172_; 
v_unused_1172_ = lean_ctor_get(v_e_920_, 1);
lean_dec(v_unused_1172_);
v___x_966_ = v_e_920_;
v_isShared_967_ = v_isSharedCheck_1171_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_args_964_);
lean_inc(v_declName_963_);
lean_dec(v_e_920_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_1171_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v_type_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; uint8_t v___y_1006_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1086_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__4));
v___x_1087_ = lean_name_eq(v_declName_963_, v___x_1086_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__6));
v___x_1089_ = lean_name_eq(v_declName_963_, v___x_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1090_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__8));
v___x_1091_ = lean_name_eq(v_declName_963_, v___x_1090_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__11));
v___x_1093_ = lean_name_eq(v_declName_963_, v___x_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; uint8_t v___x_1095_; 
v___x_1094_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__13));
v___x_1095_ = lean_name_eq(v_declName_963_, v___x_1094_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__16));
v___x_1097_ = lean_name_eq(v_declName_963_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1098_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__18));
v___x_1099_ = lean_name_eq(v_declName_963_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; lean_object* v_env_1101_; lean_object* v___x_1102_; 
v___x_1100_ = lean_st_ref_get(v_a_925_);
v_env_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc_ref(v_env_1101_);
lean_dec(v___x_1100_);
lean_inc(v_declName_963_);
v___x_1102_ = l_Lean_Environment_find_x3f(v_env_1101_, v_declName_963_, v___x_1099_);
if (lean_obj_tag(v___x_1102_) == 1)
{
lean_object* v_val_1103_; 
v_val_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_val_1103_);
lean_dec_ref_known(v___x_1102_, 1);
if (lean_obj_tag(v_val_1103_) == 6)
{
lean_object* v_val_1104_; lean_object* v_induct_1105_; lean_object* v_numParams_1106_; lean_object* v___x_1107_; 
lean_del_object(v___x_966_);
lean_dec(v_declName_963_);
v_val_1104_ = lean_ctor_get(v_val_1103_, 0);
lean_inc_ref(v_val_1104_);
lean_dec_ref_known(v_val_1103_, 1);
v_induct_1105_ = lean_ctor_get(v_val_1104_, 1);
v_numParams_1106_ = lean_ctor_get(v_val_1104_, 3);
lean_inc(v_induct_1105_);
v___x_1107_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_induct_1105_, v_a_924_, v_a_925_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
lean_dec_ref_known(v___x_1107_, 1);
if (lean_obj_tag(v_a_1108_) == 1)
{
lean_object* v_val_1109_; lean_object* v_fieldIdx_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_inc(v_numParams_1106_);
lean_dec_ref(v_val_1104_);
v_val_1109_ = lean_ctor_get(v_a_1108_, 0);
lean_inc(v_val_1109_);
lean_dec_ref_known(v_a_1108_, 1);
v_fieldIdx_1110_ = lean_ctor_get(v_val_1109_, 2);
lean_inc(v_fieldIdx_1110_);
lean_dec(v_val_1109_);
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_nat_add(v_numParams_1106_, v_fieldIdx_1110_);
lean_dec(v_fieldIdx_1110_);
lean_dec(v_numParams_1106_);
v___x_1113_ = lean_array_get(v___x_1111_, v_args_964_, v___x_1112_);
lean_dec(v___x_1112_);
lean_dec_ref(v_args_964_);
v___x_1114_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_1113_);
lean_dec(v___x_1113_);
v_e_920_ = v___x_1114_;
goto _start;
}
else
{
lean_object* v___x_1116_; 
lean_dec(v_a_1108_);
v___x_1116_ = l_Lean_Compiler_LCNF_ctorAppToMono(v_val_1104_, v_args_964_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
return v___x_1116_;
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec_ref(v_val_1104_);
lean_dec_ref(v_args_964_);
v_a_1117_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1107_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1107_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
else
{
lean_dec(v_val_1103_);
v___y_1029_ = v_a_921_;
v___y_1030_ = v_a_922_;
v___y_1031_ = v_a_923_;
v___y_1032_ = v_a_924_;
v___y_1033_ = v_a_925_;
goto v___jp_1028_;
}
}
else
{
lean_dec(v___x_1102_);
v___y_1029_ = v_a_921_;
v___y_1030_ = v_a_922_;
v___y_1031_ = v_a_923_;
v___y_1032_ = v_a_924_;
v___y_1033_ = v_a_925_;
goto v___jp_1028_;
}
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_del_object(v___x_966_);
lean_dec_ref(v_args_964_);
lean_dec(v_declName_963_);
v___x_1125_ = lean_obj_once(&l_Lean_Compiler_LCNF_LetValue_toMono___closed__22, &l_Lean_Compiler_LCNF_LetValue_toMono___closed__22_once, _init_l_Lean_Compiler_LCNF_LetValue_toMono___closed__22);
v___x_1126_ = l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(v___x_1125_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
return v___x_1126_;
}
}
else
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_del_object(v___x_966_);
lean_dec_ref(v_args_964_);
lean_dec(v_declName_963_);
v___x_1127_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__24));
v___x_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
return v___x_1128_;
}
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_del_object(v___x_966_);
lean_dec(v_declName_963_);
v___x_1129_ = lean_box(0);
v___x_1130_ = lean_unsigned_to_nat(2u);
v___x_1131_ = lean_array_get_borrowed(v___x_1129_, v_args_964_, v___x_1130_);
if (lean_obj_tag(v___x_1131_) == 1)
{
lean_object* v_fvarId_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v_extraArgs_1136_; lean_object* v___x_1137_; 
v_fvarId_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_fvarId_1132_);
v___x_1133_ = lean_array_get_size(v_args_964_);
v___x_1134_ = lean_unsigned_to_nat(3u);
v___x_1135_ = lean_nat_sub(v___x_1133_, v___x_1134_);
v_extraArgs_1136_ = lean_mk_empty_array_with_capacity(v___x_1135_);
lean_dec(v___x_1135_);
v___x_1137_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v___x_1133_, v_args_964_, v___x_1134_, v_extraArgs_1136_, v_a_921_);
lean_dec_ref(v_args_964_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1146_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1140_ = v___x_1137_;
v_isShared_1141_ = v_isSharedCheck_1146_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1137_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1146_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1142_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1142_, 0, v_fvarId_1132_);
lean_ctor_set(v___x_1142_, 1, v_a_1138_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1142_);
v___x_1144_ = v___x_1140_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec(v_fvarId_1132_);
v_a_1147_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1137_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1137_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_dec_ref(v_args_964_);
v___x_1155_ = lean_box(1);
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
return v___x_1156_;
}
}
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_del_object(v___x_966_);
lean_dec(v_declName_963_);
v___x_1157_ = lean_box(0);
v___x_1158_ = lean_unsigned_to_nat(2u);
v___x_1159_ = lean_array_get(v___x_1157_, v_args_964_, v___x_1158_);
lean_dec_ref(v_args_964_);
v___x_1160_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_1159_);
lean_dec(v___x_1159_);
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
return v___x_1161_;
}
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_del_object(v___x_966_);
lean_dec(v_declName_963_);
v___x_1162_ = lean_box(0);
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_array_get(v___x_1162_, v_args_964_, v___x_1163_);
lean_dec_ref(v_args_964_);
v___x_1165_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_1164_);
lean_dec(v___x_1164_);
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_del_object(v___x_966_);
lean_dec_ref(v_args_964_);
lean_dec(v_declName_963_);
v___x_1167_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
}
else
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_del_object(v___x_966_);
lean_dec_ref(v_args_964_);
lean_dec(v_declName_963_);
v___x_1169_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__31));
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
return v___x_1170_;
}
v___jp_968_:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_Compiler_LCNF_argsToMonoWithFnType(v_args_964_, v_type_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec_ref(v_args_964_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_987_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_987_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_987_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_987_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_980_ = lean_box(0);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 2, v_a_976_);
lean_ctor_set(v___x_966_, 1, v___x_980_);
v___x_982_ = v___x_966_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_declName_963_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_986_, 2, v_a_976_);
v___x_982_ = v_reuseFailAlloc_986_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_984_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_982_);
v___x_984_ = v___x_978_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_del_object(v___x_966_);
lean_dec(v_declName_963_);
v_a_988_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_975_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_975_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
v___jp_996_:
{
if (v___y_1006_ == 0)
{
lean_object* v_toSignature_1007_; lean_object* v_type_1008_; 
lean_dec_ref(v___y_1003_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_997_);
v_toSignature_1007_ = lean_ctor_get(v___y_1000_, 0);
lean_inc_ref(v_toSignature_1007_);
lean_dec_ref(v___y_1000_);
v_type_1008_ = lean_ctor_get(v_toSignature_1007_, 2);
lean_inc_ref(v_type_1008_);
lean_dec_ref(v_toSignature_1007_);
v_type_969_ = v_type_1008_;
v___y_970_ = v___y_1002_;
v___y_971_ = v___y_1001_;
v___y_972_ = v___y_998_;
v___y_973_ = v___y_1004_;
v___y_974_ = v___y_1005_;
goto v___jp_968_;
}
else
{
lean_object* v___x_1009_; 
lean_dec_ref(v___y_1000_);
lean_del_object(v___x_966_);
lean_dec(v_declName_963_);
v___x_1009_ = l_Lean_Compiler_LCNF_argsToMonoRedArg(v_args_964_, v___y_1003_, v___y_999_, v___y_1002_, v___y_1001_, v___y_998_, v___y_1004_, v___y_1005_);
lean_dec_ref(v___y_999_);
lean_dec_ref(v___y_1003_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1019_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1019_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1019_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1014_ = lean_box(0);
v___x_1015_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1015_, 0, v___y_997_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
lean_ctor_set(v___x_1015_, 2, v_a_1010_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1015_);
v___x_1017_ = v___x_1012_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_dec(v___y_997_);
v_a_1020_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_1009_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1009_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
v___jp_1028_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_st_ref_get(v___y_1033_);
lean_dec(v___x_1034_);
lean_inc(v_declName_963_);
v___x_1035_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_963_, v___y_1033_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___x_1035_, 1);
if (lean_obj_tag(v_a_1036_) == 1)
{
lean_object* v_val_1037_; lean_object* v_toSignature_1038_; lean_object* v_value_1039_; lean_object* v_type_1040_; lean_object* v_params_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v_val_1037_ = lean_ctor_get(v_a_1036_, 0);
lean_inc(v_val_1037_);
lean_dec_ref_known(v_a_1036_, 1);
v_toSignature_1038_ = lean_ctor_get(v_val_1037_, 0);
v_value_1039_ = lean_ctor_get(v_val_1037_, 1);
v_type_1040_ = lean_ctor_get(v_toSignature_1038_, 2);
v_params_1041_ = lean_ctor_get(v_toSignature_1038_, 3);
lean_inc_ref(v_params_1041_);
v___x_1042_ = lean_array_get_size(v_params_1041_);
v___x_1043_ = lean_array_get_size(v_args_964_);
v___x_1044_ = lean_nat_dec_le(v___x_1042_, v___x_1043_);
if (v___x_1044_ == 0)
{
lean_inc_ref(v_type_1040_);
lean_dec_ref(v_params_1041_);
lean_dec(v_val_1037_);
v_type_969_ = v_type_1040_;
v___y_970_ = v___y_1029_;
v___y_971_ = v___y_1030_;
v___y_972_ = v___y_1031_;
v___y_973_ = v___y_1032_;
v___y_974_ = v___y_1033_;
goto v___jp_968_;
}
else
{
if (lean_obj_tag(v_value_1039_) == 0)
{
lean_object* v_code_1045_; 
v_code_1045_ = lean_ctor_get(v_value_1039_, 0);
if (lean_obj_tag(v_code_1045_) == 0)
{
lean_object* v_decl_1046_; lean_object* v_value_1047_; 
v_decl_1046_ = lean_ctor_get(v_code_1045_, 0);
v_value_1047_ = lean_ctor_get(v_decl_1046_, 3);
if (lean_obj_tag(v_value_1047_) == 3)
{
lean_object* v_k_1048_; 
v_k_1048_ = lean_ctor_get(v_code_1045_, 1);
if (lean_obj_tag(v_k_1048_) == 5)
{
lean_object* v_fvarId_1049_; lean_object* v_declName_1050_; lean_object* v_args_1051_; lean_object* v_fvarId_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
v_fvarId_1049_ = lean_ctor_get(v_decl_1046_, 0);
v_declName_1050_ = lean_ctor_get(v_value_1047_, 0);
v_args_1051_ = lean_ctor_get(v_value_1047_, 2);
lean_inc_ref(v_args_1051_);
v_fvarId_1052_ = lean_ctor_get(v_k_1048_, 0);
v___x_1053_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__1));
lean_inc(v_declName_963_);
v___x_1054_ = l_Lean_Name_append(v_declName_963_, v___x_1053_);
v___x_1055_ = lean_name_eq(v_declName_1050_, v___x_1054_);
if (v___x_1055_ == 0)
{
v___y_997_ = v___x_1054_;
v___y_998_ = v___y_1031_;
v___y_999_ = v_args_1051_;
v___y_1000_ = v_val_1037_;
v___y_1001_ = v___y_1030_;
v___y_1002_ = v___y_1029_;
v___y_1003_ = v_params_1041_;
v___y_1004_ = v___y_1032_;
v___y_1005_ = v___y_1033_;
v___y_1006_ = v___x_1055_;
goto v___jp_996_;
}
else
{
uint8_t v___x_1056_; 
v___x_1056_ = l_Lean_instBEqFVarId_beq(v_fvarId_1052_, v_fvarId_1049_);
v___y_997_ = v___x_1054_;
v___y_998_ = v___y_1031_;
v___y_999_ = v_args_1051_;
v___y_1000_ = v_val_1037_;
v___y_1001_ = v___y_1030_;
v___y_1002_ = v___y_1029_;
v___y_1003_ = v_params_1041_;
v___y_1004_ = v___y_1032_;
v___y_1005_ = v___y_1033_;
v___y_1006_ = v___x_1056_;
goto v___jp_996_;
}
}
else
{
lean_inc_ref(v_type_1040_);
lean_dec_ref(v_params_1041_);
lean_dec(v_val_1037_);
v_type_969_ = v_type_1040_;
v___y_970_ = v___y_1029_;
v___y_971_ = v___y_1030_;
v___y_972_ = v___y_1031_;
v___y_973_ = v___y_1032_;
v___y_974_ = v___y_1033_;
goto v___jp_968_;
}
}
else
{
lean_inc_ref(v_type_1040_);
lean_dec_ref(v_params_1041_);
lean_dec(v_val_1037_);
v_type_969_ = v_type_1040_;
v___y_970_ = v___y_1029_;
v___y_971_ = v___y_1030_;
v___y_972_ = v___y_1031_;
v___y_973_ = v___y_1032_;
v___y_974_ = v___y_1033_;
goto v___jp_968_;
}
}
else
{
lean_inc_ref(v_type_1040_);
lean_dec_ref(v_params_1041_);
lean_dec(v_val_1037_);
v_type_969_ = v_type_1040_;
v___y_970_ = v___y_1029_;
v___y_971_ = v___y_1030_;
v___y_972_ = v___y_1031_;
v___y_973_ = v___y_1032_;
v___y_974_ = v___y_1033_;
goto v___jp_968_;
}
}
else
{
lean_inc_ref(v_type_1040_);
lean_dec_ref(v_params_1041_);
lean_dec(v_val_1037_);
v_type_969_ = v_type_1040_;
v___y_970_ = v___y_1029_;
v___y_971_ = v___y_1030_;
v___y_972_ = v___y_1031_;
v___y_973_ = v___y_1032_;
v___y_974_ = v___y_1033_;
goto v___jp_968_;
}
}
}
else
{
size_t v_sz_1057_; size_t v___x_1058_; lean_object* v___x_1059_; 
lean_dec(v_a_1036_);
lean_del_object(v___x_966_);
v_sz_1057_ = lean_array_size(v_args_964_);
v___x_1058_ = ((size_t)0ULL);
v___x_1059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_1057_, v___x_1058_, v_args_964_, v___y_1029_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1069_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1062_ = v___x_1059_;
v_isShared_1063_ = v_isSharedCheck_1069_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1069_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1064_ = lean_box(0);
v___x_1065_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1065_, 0, v_declName_963_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
lean_ctor_set(v___x_1065_, 2, v_a_1060_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v___x_1065_);
v___x_1067_ = v___x_1062_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec(v_declName_963_);
v_a_1070_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1059_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1059_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_del_object(v___x_966_);
lean_dec_ref(v_args_964_);
lean_dec(v_declName_963_);
v_a_1078_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1035_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1035_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
}
case 4:
{
lean_object* v_fvarId_1173_; lean_object* v_args_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1204_; 
v_fvarId_1173_ = lean_ctor_get(v_e_920_, 0);
v_args_1174_ = lean_ctor_get(v_e_920_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_e_920_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1176_ = v_e_920_;
v_isShared_1177_ = v_isSharedCheck_1204_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_args_1174_);
lean_inc(v_fvarId_1173_);
lean_dec(v_e_920_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1204_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = lean_st_ref_get(v_a_921_);
v___x_1179_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_1178_, v_fvarId_1173_);
lean_dec(v___x_1178_);
if (v___x_1179_ == 0)
{
size_t v_sz_1180_; size_t v___x_1181_; lean_object* v___x_1182_; 
v_sz_1180_ = lean_array_size(v_args_1174_);
v___x_1181_ = ((size_t)0ULL);
v___x_1182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_1180_, v___x_1181_, v_args_1174_, v_a_921_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1193_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1193_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1193_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 1, v_a_1183_);
v___x_1188_ = v___x_1176_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_fvarId_1173_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1190_; 
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
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_del_object(v___x_1176_);
lean_dec(v_fvarId_1173_);
v_a_1194_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1182_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1182_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
lean_del_object(v___x_1176_);
lean_dec_ref(v_args_1174_);
lean_dec(v_fvarId_1173_);
v___x_1202_ = lean_box(1);
v___x_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
return v___x_1203_;
}
}
}
default: 
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v_e_920_);
return v___x_1205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___boxed(lean_object* v_e_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_Compiler_LCNF_LetValue_toMono(v_e_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1(lean_object* v_upperBound_1214_, lean_object* v_args_1215_, lean_object* v_inst_1216_, lean_object* v_R_1217_, lean_object* v_a_1218_, lean_object* v_b_1219_, lean_object* v_c_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v_upperBound_1214_, v_args_1215_, v_a_1218_, v_b_1219_, v___y_1221_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___boxed(lean_object* v_upperBound_1228_, lean_object* v_args_1229_, lean_object* v_inst_1230_, lean_object* v_R_1231_, lean_object* v_a_1232_, lean_object* v_b_1233_, lean_object* v_c_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1(v_upperBound_1228_, v_args_1229_, v_inst_1230_, v_R_1231_, v_a_1232_, v_b_1233_, v_c_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v_args_1229_);
lean_dec(v_upperBound_1228_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono(lean_object* v_decl_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v_type_1249_; lean_object* v_value_1250_; lean_object* v___x_1251_; 
v_type_1249_ = lean_ctor_get(v_decl_1242_, 2);
v_value_1250_ = lean_ctor_get(v_decl_1242_, 3);
lean_inc_ref(v_type_1249_);
v___x_1251_ = l_Lean_Compiler_LCNF_toMonoType(v_type_1249_, v_a_1246_, v_a_1247_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1253_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___x_1251_, 1);
lean_inc(v_value_1250_);
v___x_1253_ = l_Lean_Compiler_LCNF_LetValue_toMono(v_value_1250_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; uint8_t v___x_1255_; lean_object* v___x_1256_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1253_, 1);
v___x_1255_ = 0;
v___x_1256_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_1255_, v_decl_1242_, v_a_1252_, v_a_1254_, v_a_1245_);
return v___x_1256_;
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v_a_1252_);
lean_dec_ref(v_decl_1242_);
v_a_1257_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1253_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1253_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec_ref(v_decl_1242_);
v_a_1265_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1251_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1251_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono___boxed(lean_object* v_decl_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_Compiler_LCNF_LetDecl_toMono(v_decl_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(lean_object* v_msg_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v_toApplicative_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1352_; 
v___x_1288_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1289_ = l_StateRefT_x27_instMonad___redArg(v___x_1288_);
v_toApplicative_1290_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1352_ == 0)
{
lean_object* v_unused_1353_; 
v_unused_1353_ = lean_ctor_get(v___x_1289_, 1);
lean_dec(v_unused_1353_);
v___x_1292_ = v___x_1289_;
v_isShared_1293_ = v_isSharedCheck_1352_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_toApplicative_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1352_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v_toFunctor_1294_; lean_object* v_toSeq_1295_; lean_object* v_toSeqLeft_1296_; lean_object* v_toSeqRight_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1350_; 
v_toFunctor_1294_ = lean_ctor_get(v_toApplicative_1290_, 0);
v_toSeq_1295_ = lean_ctor_get(v_toApplicative_1290_, 2);
v_toSeqLeft_1296_ = lean_ctor_get(v_toApplicative_1290_, 3);
v_toSeqRight_1297_ = lean_ctor_get(v_toApplicative_1290_, 4);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_toApplicative_1290_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; 
v_unused_1351_ = lean_ctor_get(v_toApplicative_1290_, 1);
lean_dec(v_unused_1351_);
v___x_1299_ = v_toApplicative_1290_;
v_isShared_1300_ = v_isSharedCheck_1350_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_toSeqRight_1297_);
lean_inc(v_toSeqLeft_1296_);
lean_inc(v_toSeq_1295_);
lean_inc(v_toFunctor_1294_);
lean_dec(v_toApplicative_1290_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1350_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___f_1301_; lean_object* v___f_1302_; lean_object* v___f_1303_; lean_object* v___f_1304_; lean_object* v___x_1305_; lean_object* v___f_1306_; lean_object* v___f_1307_; lean_object* v___f_1308_; lean_object* v___x_1310_; 
v___f_1301_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1302_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1294_);
v___f_1303_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1303_, 0, v_toFunctor_1294_);
v___f_1304_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1304_, 0, v_toFunctor_1294_);
v___x_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___f_1303_);
lean_ctor_set(v___x_1305_, 1, v___f_1304_);
v___f_1306_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1306_, 0, v_toSeqRight_1297_);
v___f_1307_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1307_, 0, v_toSeqLeft_1296_);
v___f_1308_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1308_, 0, v_toSeq_1295_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 4, v___f_1306_);
lean_ctor_set(v___x_1299_, 3, v___f_1307_);
lean_ctor_set(v___x_1299_, 2, v___f_1308_);
lean_ctor_set(v___x_1299_, 1, v___f_1301_);
lean_ctor_set(v___x_1299_, 0, v___x_1305_);
v___x_1310_ = v___x_1299_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1305_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v___f_1301_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v___f_1308_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v___f_1307_);
lean_ctor_set(v_reuseFailAlloc_1349_, 4, v___f_1306_);
v___x_1310_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v___x_1312_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 1, v___f_1302_);
lean_ctor_set(v___x_1292_, 0, v___x_1310_);
v___x_1312_ = v___x_1292_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v___f_1302_);
v___x_1312_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1313_; lean_object* v_toApplicative_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1346_; 
v___x_1313_ = l_StateRefT_x27_instMonad___redArg(v___x_1312_);
v_toApplicative_1314_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; 
v_unused_1347_ = lean_ctor_get(v___x_1313_, 1);
lean_dec(v_unused_1347_);
v___x_1316_ = v___x_1313_;
v_isShared_1317_ = v_isSharedCheck_1346_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_toApplicative_1314_);
lean_dec(v___x_1313_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1346_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v_toFunctor_1318_; lean_object* v_toSeq_1319_; lean_object* v_toSeqLeft_1320_; lean_object* v_toSeqRight_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1344_; 
v_toFunctor_1318_ = lean_ctor_get(v_toApplicative_1314_, 0);
v_toSeq_1319_ = lean_ctor_get(v_toApplicative_1314_, 2);
v_toSeqLeft_1320_ = lean_ctor_get(v_toApplicative_1314_, 3);
v_toSeqRight_1321_ = lean_ctor_get(v_toApplicative_1314_, 4);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_toApplicative_1314_);
if (v_isSharedCheck_1344_ == 0)
{
lean_object* v_unused_1345_; 
v_unused_1345_ = lean_ctor_get(v_toApplicative_1314_, 1);
lean_dec(v_unused_1345_);
v___x_1323_ = v_toApplicative_1314_;
v_isShared_1324_ = v_isSharedCheck_1344_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_toSeqRight_1321_);
lean_inc(v_toSeqLeft_1320_);
lean_inc(v_toSeq_1319_);
lean_inc(v_toFunctor_1318_);
lean_dec(v_toApplicative_1314_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1344_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___f_1325_; lean_object* v___f_1326_; lean_object* v___f_1327_; lean_object* v___f_1328_; lean_object* v___x_1329_; lean_object* v___f_1330_; lean_object* v___f_1331_; lean_object* v___f_1332_; lean_object* v___x_1334_; 
v___f_1325_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1326_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1318_);
v___f_1327_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1327_, 0, v_toFunctor_1318_);
v___f_1328_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1328_, 0, v_toFunctor_1318_);
v___x_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___f_1327_);
lean_ctor_set(v___x_1329_, 1, v___f_1328_);
v___f_1330_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1330_, 0, v_toSeqRight_1321_);
v___f_1331_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1331_, 0, v_toSeqLeft_1320_);
v___f_1332_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1332_, 0, v_toSeq_1319_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 4, v___f_1330_);
lean_ctor_set(v___x_1323_, 3, v___f_1331_);
lean_ctor_set(v___x_1323_, 2, v___f_1332_);
lean_ctor_set(v___x_1323_, 1, v___f_1325_);
lean_ctor_set(v___x_1323_, 0, v___x_1329_);
v___x_1334_ = v___x_1323_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v___f_1325_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v___f_1332_);
lean_ctor_set(v_reuseFailAlloc_1343_, 3, v___f_1331_);
lean_ctor_set(v_reuseFailAlloc_1343_, 4, v___f_1330_);
v___x_1334_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1336_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 1, v___f_1326_);
lean_ctor_set(v___x_1316_, 0, v___x_1334_);
v___x_1336_ = v___x_1316_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v___f_1326_);
v___x_1336_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_4540__overap_1340_; lean_object* v___x_1341_; 
v___x_1337_ = l_StateRefT_x27_instMonad___redArg(v___x_1336_);
v___x_1338_ = lean_box(0);
v___x_1339_ = l_instInhabitedOfMonad___redArg(v___x_1337_, v___x_1338_);
v___x_4540__overap_1340_ = lean_panic_fn_borrowed(v___x_1339_, v_msg_1281_);
lean_dec(v___x_1339_);
lean_inc(v___y_1286_);
lean_inc_ref(v___y_1285_);
lean_inc(v___y_1284_);
lean_inc_ref(v___y_1283_);
lean_inc(v___y_1282_);
v___x_1341_ = lean_apply_6(v___x_4540__overap_1340_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, lean_box(0));
return v___x_1341_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0___boxed(lean_object* v_msg_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v_msg_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
return v_res_1361_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1363_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_1364_ = lean_unsigned_to_nat(11u);
v___x_1365_ = lean_unsigned_to_nat(158u);
v___x_1366_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__0));
v___x_1367_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1368_ = l_mkPanicMessageWithDecl(v___x_1367_, v___x_1366_, v___x_1365_, v___x_1364_, v___x_1363_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(lean_object* v_upperBound_1369_, lean_object* v_a_1370_, lean_object* v_b_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v_a_1379_; uint8_t v___x_1383_; 
v___x_1383_ = lean_nat_dec_lt(v_a_1370_, v_upperBound_1369_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; 
lean_dec(v_a_1370_);
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v_b_1371_);
return v___x_1384_;
}
else
{
if (lean_obj_tag(v_b_1371_) == 7)
{
lean_object* v_body_1385_; 
v_body_1385_ = lean_ctor_get(v_b_1371_, 2);
lean_inc_ref(v_body_1385_);
lean_dec_ref_known(v_b_1371_, 3);
v_a_1379_ = v_body_1385_;
goto v___jp_1378_;
}
else
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1);
v___x_1387_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v___x_1386_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_dec_ref_known(v___x_1387_, 1);
v_a_1379_ = v_b_1371_;
goto v___jp_1378_;
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_dec_ref(v_b_1371_);
lean_dec(v_a_1370_);
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1387_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1387_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
}
v___jp_1378_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = lean_unsigned_to_nat(1u);
v___x_1381_ = lean_nat_add(v_a_1370_, v___x_1380_);
lean_dec(v_a_1370_);
v_a_1370_ = v___x_1381_;
v_b_1371_ = v_a_1379_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___boxed(lean_object* v_upperBound_1396_, lean_object* v_a_1397_, lean_object* v_b_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_upperBound_1396_, v_a_1397_, v_b_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec(v_upperBound_1396_);
return v_res_1405_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1406_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_1407_ = lean_unsigned_to_nat(11u);
v___x_1408_ = lean_unsigned_to_nat(166u);
v___x_1409_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__0));
v___x_1410_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1411_ = l_mkPanicMessageWithDecl(v___x_1410_, v___x_1409_, v___x_1408_, v___x_1407_, v___x_1406_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(lean_object* v_upperBound_1412_, lean_object* v_a_1413_, lean_object* v_b_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v_a_1422_; uint8_t v___x_1426_; 
v___x_1426_ = lean_nat_dec_lt(v_a_1413_, v_upperBound_1412_);
if (v___x_1426_ == 0)
{
lean_object* v___x_1427_; 
lean_dec(v_a_1413_);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v_b_1414_);
return v___x_1427_;
}
else
{
lean_object* v_fst_1428_; 
v_fst_1428_ = lean_ctor_get(v_b_1414_, 0);
lean_inc(v_fst_1428_);
if (lean_obj_tag(v_fst_1428_) == 7)
{
lean_object* v_snd_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1462_; 
v_snd_1429_ = lean_ctor_get(v_b_1414_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_b_1414_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; 
v_unused_1463_ = lean_ctor_get(v_b_1414_, 0);
lean_dec(v_unused_1463_);
v___x_1431_ = v_b_1414_;
v_isShared_1432_ = v_isSharedCheck_1462_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_snd_1429_);
lean_dec(v_b_1414_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1462_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v_binderName_1433_; lean_object* v_binderType_1434_; lean_object* v_body_1435_; lean_object* v___x_1436_; 
v_binderName_1433_ = lean_ctor_get(v_fst_1428_, 0);
lean_inc(v_binderName_1433_);
v_binderType_1434_ = lean_ctor_get(v_fst_1428_, 1);
lean_inc_ref(v_binderType_1434_);
v_body_1435_ = lean_ctor_get(v_fst_1428_, 2);
lean_inc_ref(v_body_1435_);
lean_dec_ref_known(v_fst_1428_, 3);
v___x_1436_ = l_Lean_Compiler_LCNF_toMonoType(v_binderType_1434_, v___y_1418_, v___y_1419_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; uint8_t v___x_1438_; uint8_t v___x_1439_; lean_object* v___x_1440_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_a_1437_);
lean_dec_ref_known(v___x_1436_, 1);
v___x_1438_ = 0;
v___x_1439_ = 0;
v___x_1440_ = l_Lean_Compiler_LCNF_mkParam(v___x_1438_, v_binderName_1433_, v_a_1437_, v___x_1439_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1440_, 1);
v___x_1442_ = lean_array_push(v_snd_1429_, v_a_1441_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v___x_1442_);
lean_ctor_set(v___x_1431_, 0, v_body_1435_);
v___x_1444_ = v___x_1431_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_body_1435_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
v_a_1422_ = v___x_1444_;
goto v___jp_1421_;
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec_ref(v_body_1435_);
lean_del_object(v___x_1431_);
lean_dec(v_snd_1429_);
lean_dec(v_a_1413_);
v_a_1446_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1440_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1440_);
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
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec_ref(v_body_1435_);
lean_dec(v_binderName_1433_);
lean_del_object(v___x_1431_);
lean_dec(v_snd_1429_);
lean_dec(v_a_1413_);
v_a_1454_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1436_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1436_);
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
}
else
{
lean_object* v_snd_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1481_; 
v_snd_1464_ = lean_ctor_get(v_b_1414_, 1);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_b_1414_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; 
v_unused_1482_ = lean_ctor_get(v_b_1414_, 0);
lean_dec(v_unused_1482_);
v___x_1466_ = v_b_1414_;
v_isShared_1467_ = v_isSharedCheck_1481_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_snd_1464_);
lean_dec(v_b_1414_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1481_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0);
v___x_1469_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v___x_1468_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v___x_1471_; 
lean_dec_ref_known(v___x_1469_, 1);
if (v_isShared_1467_ == 0)
{
v___x_1471_ = v___x_1466_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_fst_1428_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_snd_1464_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
v_a_1422_ = v___x_1471_;
goto v___jp_1421_;
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_del_object(v___x_1466_);
lean_dec(v_snd_1464_);
lean_dec(v_fst_1428_);
lean_dec(v_a_1413_);
v_a_1473_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1469_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1469_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
}
v___jp_1421_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = lean_unsigned_to_nat(1u);
v___x_1424_ = lean_nat_add(v_a_1413_, v___x_1423_);
lean_dec(v_a_1413_);
v_a_1413_ = v___x_1424_;
v_b_1414_ = v_a_1422_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___boxed(lean_object* v_upperBound_1483_, lean_object* v_a_1484_, lean_object* v_b_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_upperBound_1483_, v_a_1484_, v_b_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec(v_upperBound_1483_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(lean_object* v_ctorType_1493_, lean_object* v_numParams_1494_, lean_object* v_numNewFields_1495_, lean_object* v_oldFields_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = lean_unsigned_to_nat(0u);
v___x_1504_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_numParams_1494_, v___x_1503_, v_ctorType_1493_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
lean_dec_ref_known(v___x_1504_, 1);
v___x_1506_ = lean_array_get_size(v_oldFields_1496_);
v___x_1507_ = lean_nat_add(v___x_1506_, v_numNewFields_1495_);
v___x_1508_ = lean_mk_empty_array_with_capacity(v___x_1507_);
lean_dec(v___x_1507_);
v___x_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1509_, 0, v_a_1505_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_numNewFields_1495_, v___x_1503_, v___x_1509_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1520_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1520_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1520_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v_snd_1515_; lean_object* v___x_1516_; lean_object* v___x_1518_; 
v_snd_1515_ = lean_ctor_get(v_a_1511_, 1);
lean_inc(v_snd_1515_);
lean_dec(v_a_1511_);
v___x_1516_ = l_Array_append___redArg(v_snd_1515_, v_oldFields_1496_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___x_1516_);
v___x_1518_ = v___x_1513_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
v_a_1521_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1510_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1510_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
v_a_1529_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1504_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1504_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields___boxed(lean_object* v_ctorType_1537_, lean_object* v_numParams_1538_, lean_object* v_numNewFields_1539_, lean_object* v_oldFields_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(v_ctorType_1537_, v_numParams_1538_, v_numNewFields_1539_, v_oldFields_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
lean_dec(v_a_1545_);
lean_dec_ref(v_a_1544_);
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
lean_dec(v_a_1541_);
lean_dec_ref(v_oldFields_1540_);
lean_dec(v_numNewFields_1539_);
lean_dec(v_numParams_1538_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1(lean_object* v_upperBound_1548_, lean_object* v_inst_1549_, lean_object* v_R_1550_, lean_object* v_a_1551_, lean_object* v_b_1552_, lean_object* v_c_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_upperBound_1548_, v_a_1551_, v_b_1552_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___boxed(lean_object* v_upperBound_1561_, lean_object* v_inst_1562_, lean_object* v_R_1563_, lean_object* v_a_1564_, lean_object* v_b_1565_, lean_object* v_c_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1(v_upperBound_1561_, v_inst_1562_, v_R_1563_, v_a_1564_, v_b_1565_, v_c_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec(v_upperBound_1561_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2(lean_object* v_upperBound_1574_, lean_object* v_inst_1575_, lean_object* v_R_1576_, lean_object* v_a_1577_, lean_object* v_b_1578_, lean_object* v_c_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_upperBound_1574_, v_a_1577_, v_b_1578_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___boxed(lean_object* v_upperBound_1587_, lean_object* v_inst_1588_, lean_object* v_R_1589_, lean_object* v_a_1590_, lean_object* v_b_1591_, lean_object* v_c_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2(v_upperBound_1587_, v_inst_1588_, v_R_1589_, v_a_1590_, v_b_1591_, v_c_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec(v_upperBound_1587_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(size_t v_sz_1600_, size_t v_i_1601_, lean_object* v_bs_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
uint8_t v___x_1608_; 
v___x_1608_ = lean_usize_dec_lt(v_i_1601_, v_sz_1600_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1609_, 0, v_bs_1602_);
return v___x_1609_;
}
else
{
lean_object* v_v_1610_; lean_object* v___x_1611_; 
v_v_1610_ = lean_array_uget_borrowed(v_bs_1602_, v_i_1601_);
lean_inc(v_v_1610_);
v___x_1611_ = l_Lean_Compiler_LCNF_Param_toMono___redArg(v_v_1610_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1613_; lean_object* v_bs_x27_1614_; size_t v___x_1615_; size_t v___x_1616_; lean_object* v___x_1617_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1611_, 1);
v___x_1613_ = lean_unsigned_to_nat(0u);
v_bs_x27_1614_ = lean_array_uset(v_bs_1602_, v_i_1601_, v___x_1613_);
v___x_1615_ = ((size_t)1ULL);
v___x_1616_ = lean_usize_add(v_i_1601_, v___x_1615_);
v___x_1617_ = lean_array_uset(v_bs_x27_1614_, v_i_1601_, v_a_1612_);
v_i_1601_ = v___x_1616_;
v_bs_1602_ = v___x_1617_;
goto _start;
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec_ref(v_bs_1602_);
v_a_1619_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1611_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1611_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg___boxed(lean_object* v_sz_1627_, lean_object* v_i_1628_, lean_object* v_bs_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
size_t v_sz_boxed_1635_; size_t v_i_boxed_1636_; lean_object* v_res_1637_; 
v_sz_boxed_1635_ = lean_unbox_usize(v_sz_1627_);
lean_dec(v_sz_1627_);
v_i_boxed_1636_ = lean_unbox_usize(v_i_1628_);
lean_dec(v_i_1628_);
v_res_1637_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_boxed_1635_, v_i_boxed_1636_, v_bs_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec(v___y_1630_);
return v_res_1637_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0(void){
_start:
{
uint8_t v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = 0;
v___x_1639_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(lean_object* v_msg_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v_toApplicative_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1711_; 
v___x_1647_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1648_ = l_StateRefT_x27_instMonad___redArg(v___x_1647_);
v_toApplicative_1649_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1711_ == 0)
{
lean_object* v_unused_1712_; 
v_unused_1712_ = lean_ctor_get(v___x_1648_, 1);
lean_dec(v_unused_1712_);
v___x_1651_ = v___x_1648_;
v_isShared_1652_ = v_isSharedCheck_1711_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_toApplicative_1649_);
lean_dec(v___x_1648_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1711_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v_toFunctor_1653_; lean_object* v_toSeq_1654_; lean_object* v_toSeqLeft_1655_; lean_object* v_toSeqRight_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1709_; 
v_toFunctor_1653_ = lean_ctor_get(v_toApplicative_1649_, 0);
v_toSeq_1654_ = lean_ctor_get(v_toApplicative_1649_, 2);
v_toSeqLeft_1655_ = lean_ctor_get(v_toApplicative_1649_, 3);
v_toSeqRight_1656_ = lean_ctor_get(v_toApplicative_1649_, 4);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_toApplicative_1649_);
if (v_isSharedCheck_1709_ == 0)
{
lean_object* v_unused_1710_; 
v_unused_1710_ = lean_ctor_get(v_toApplicative_1649_, 1);
lean_dec(v_unused_1710_);
v___x_1658_ = v_toApplicative_1649_;
v_isShared_1659_ = v_isSharedCheck_1709_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_toSeqRight_1656_);
lean_inc(v_toSeqLeft_1655_);
lean_inc(v_toSeq_1654_);
lean_inc(v_toFunctor_1653_);
lean_dec(v_toApplicative_1649_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1709_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___f_1660_; lean_object* v___f_1661_; lean_object* v___f_1662_; lean_object* v___f_1663_; lean_object* v___x_1664_; lean_object* v___f_1665_; lean_object* v___f_1666_; lean_object* v___f_1667_; lean_object* v___x_1669_; 
v___f_1660_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1661_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1653_);
v___f_1662_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1662_, 0, v_toFunctor_1653_);
v___f_1663_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1663_, 0, v_toFunctor_1653_);
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___f_1662_);
lean_ctor_set(v___x_1664_, 1, v___f_1663_);
v___f_1665_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1665_, 0, v_toSeqRight_1656_);
v___f_1666_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1666_, 0, v_toSeqLeft_1655_);
v___f_1667_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1667_, 0, v_toSeq_1654_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 4, v___f_1665_);
lean_ctor_set(v___x_1658_, 3, v___f_1666_);
lean_ctor_set(v___x_1658_, 2, v___f_1667_);
lean_ctor_set(v___x_1658_, 1, v___f_1660_);
lean_ctor_set(v___x_1658_, 0, v___x_1664_);
v___x_1669_ = v___x_1658_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1664_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v___f_1660_);
lean_ctor_set(v_reuseFailAlloc_1708_, 2, v___f_1667_);
lean_ctor_set(v_reuseFailAlloc_1708_, 3, v___f_1666_);
lean_ctor_set(v_reuseFailAlloc_1708_, 4, v___f_1665_);
v___x_1669_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1671_; 
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 1, v___f_1661_);
lean_ctor_set(v___x_1651_, 0, v___x_1669_);
v___x_1671_ = v___x_1651_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v___f_1661_);
v___x_1671_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1672_; lean_object* v_toApplicative_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1705_; 
v___x_1672_ = l_StateRefT_x27_instMonad___redArg(v___x_1671_);
v_toApplicative_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1705_ == 0)
{
lean_object* v_unused_1706_; 
v_unused_1706_ = lean_ctor_get(v___x_1672_, 1);
lean_dec(v_unused_1706_);
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1705_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_toApplicative_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1705_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v_toFunctor_1677_; lean_object* v_toSeq_1678_; lean_object* v_toSeqLeft_1679_; lean_object* v_toSeqRight_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1703_; 
v_toFunctor_1677_ = lean_ctor_get(v_toApplicative_1673_, 0);
v_toSeq_1678_ = lean_ctor_get(v_toApplicative_1673_, 2);
v_toSeqLeft_1679_ = lean_ctor_get(v_toApplicative_1673_, 3);
v_toSeqRight_1680_ = lean_ctor_get(v_toApplicative_1673_, 4);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_toApplicative_1673_);
if (v_isSharedCheck_1703_ == 0)
{
lean_object* v_unused_1704_; 
v_unused_1704_ = lean_ctor_get(v_toApplicative_1673_, 1);
lean_dec(v_unused_1704_);
v___x_1682_ = v_toApplicative_1673_;
v_isShared_1683_ = v_isSharedCheck_1703_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_toSeqRight_1680_);
lean_inc(v_toSeqLeft_1679_);
lean_inc(v_toSeq_1678_);
lean_inc(v_toFunctor_1677_);
lean_dec(v_toApplicative_1673_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1703_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___f_1684_; lean_object* v___f_1685_; lean_object* v___f_1686_; lean_object* v___f_1687_; lean_object* v___x_1688_; lean_object* v___f_1689_; lean_object* v___f_1690_; lean_object* v___f_1691_; lean_object* v___x_1693_; 
v___f_1684_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1685_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1677_);
v___f_1686_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1686_, 0, v_toFunctor_1677_);
v___f_1687_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1687_, 0, v_toFunctor_1677_);
v___x_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___f_1686_);
lean_ctor_set(v___x_1688_, 1, v___f_1687_);
v___f_1689_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1689_, 0, v_toSeqRight_1680_);
v___f_1690_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1690_, 0, v_toSeqLeft_1679_);
v___f_1691_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1691_, 0, v_toSeq_1678_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 4, v___f_1689_);
lean_ctor_set(v___x_1682_, 3, v___f_1690_);
lean_ctor_set(v___x_1682_, 2, v___f_1691_);
lean_ctor_set(v___x_1682_, 1, v___f_1684_);
lean_ctor_set(v___x_1682_, 0, v___x_1688_);
v___x_1693_ = v___x_1682_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1688_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v___f_1684_);
lean_ctor_set(v_reuseFailAlloc_1702_, 2, v___f_1691_);
lean_ctor_set(v_reuseFailAlloc_1702_, 3, v___f_1690_);
lean_ctor_set(v_reuseFailAlloc_1702_, 4, v___f_1689_);
v___x_1693_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1695_; 
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 1, v___f_1685_);
lean_ctor_set(v___x_1675_, 0, v___x_1693_);
v___x_1695_ = v___x_1675_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1693_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v___f_1685_);
v___x_1695_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_39983__overap_1699_; lean_object* v___x_1700_; 
v___x_1696_ = l_StateRefT_x27_instMonad___redArg(v___x_1695_);
v___x_1697_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0);
v___x_1698_ = l_instInhabitedOfMonad___redArg(v___x_1696_, v___x_1697_);
v___x_39983__overap_1699_ = lean_panic_fn_borrowed(v___x_1698_, v_msg_1640_);
lean_dec(v___x_1698_);
lean_inc(v___y_1645_);
lean_inc_ref(v___y_1644_);
lean_inc(v___y_1643_);
lean_inc_ref(v___y_1642_);
lean_inc(v___y_1641_);
v___x_1700_ = lean_apply_6(v___x_39983__overap_1699_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, lean_box(0));
return v___x_1700_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___boxed(lean_object* v_msg_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v_msg_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__2(lean_object* v_msg_1721_){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0);
v___x_1723_ = lean_panic_fn_borrowed(v___x_1722_, v_msg_1721_);
return v___x_1723_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0(void){
_start:
{
uint8_t v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = 0;
v___x_1725_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(lean_object* v_msg_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v_toApplicative_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1797_; 
v___x_1733_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1734_ = l_StateRefT_x27_instMonad___redArg(v___x_1733_);
v_toApplicative_1735_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1797_ == 0)
{
lean_object* v_unused_1798_; 
v_unused_1798_ = lean_ctor_get(v___x_1734_, 1);
lean_dec(v_unused_1798_);
v___x_1737_ = v___x_1734_;
v_isShared_1738_ = v_isSharedCheck_1797_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_toApplicative_1735_);
lean_dec(v___x_1734_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1797_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v_toFunctor_1739_; lean_object* v_toSeq_1740_; lean_object* v_toSeqLeft_1741_; lean_object* v_toSeqRight_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1795_; 
v_toFunctor_1739_ = lean_ctor_get(v_toApplicative_1735_, 0);
v_toSeq_1740_ = lean_ctor_get(v_toApplicative_1735_, 2);
v_toSeqLeft_1741_ = lean_ctor_get(v_toApplicative_1735_, 3);
v_toSeqRight_1742_ = lean_ctor_get(v_toApplicative_1735_, 4);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_toApplicative_1735_);
if (v_isSharedCheck_1795_ == 0)
{
lean_object* v_unused_1796_; 
v_unused_1796_ = lean_ctor_get(v_toApplicative_1735_, 1);
lean_dec(v_unused_1796_);
v___x_1744_ = v_toApplicative_1735_;
v_isShared_1745_ = v_isSharedCheck_1795_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_toSeqRight_1742_);
lean_inc(v_toSeqLeft_1741_);
lean_inc(v_toSeq_1740_);
lean_inc(v_toFunctor_1739_);
lean_dec(v_toApplicative_1735_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1795_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___f_1746_; lean_object* v___f_1747_; lean_object* v___f_1748_; lean_object* v___f_1749_; lean_object* v___x_1750_; lean_object* v___f_1751_; lean_object* v___f_1752_; lean_object* v___f_1753_; lean_object* v___x_1755_; 
v___f_1746_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1747_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1739_);
v___f_1748_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1748_, 0, v_toFunctor_1739_);
v___f_1749_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1749_, 0, v_toFunctor_1739_);
v___x_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___f_1748_);
lean_ctor_set(v___x_1750_, 1, v___f_1749_);
v___f_1751_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1751_, 0, v_toSeqRight_1742_);
v___f_1752_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1752_, 0, v_toSeqLeft_1741_);
v___f_1753_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1753_, 0, v_toSeq_1740_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 4, v___f_1751_);
lean_ctor_set(v___x_1744_, 3, v___f_1752_);
lean_ctor_set(v___x_1744_, 2, v___f_1753_);
lean_ctor_set(v___x_1744_, 1, v___f_1746_);
lean_ctor_set(v___x_1744_, 0, v___x_1750_);
v___x_1755_ = v___x_1744_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1750_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v___f_1746_);
lean_ctor_set(v_reuseFailAlloc_1794_, 2, v___f_1753_);
lean_ctor_set(v_reuseFailAlloc_1794_, 3, v___f_1752_);
lean_ctor_set(v_reuseFailAlloc_1794_, 4, v___f_1751_);
v___x_1755_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1757_; 
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 1, v___f_1747_);
lean_ctor_set(v___x_1737_, 0, v___x_1755_);
v___x_1757_ = v___x_1737_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v___f_1747_);
v___x_1757_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1758_; lean_object* v_toApplicative_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1791_; 
v___x_1758_ = l_StateRefT_x27_instMonad___redArg(v___x_1757_);
v_toApplicative_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1791_ == 0)
{
lean_object* v_unused_1792_; 
v_unused_1792_ = lean_ctor_get(v___x_1758_, 1);
lean_dec(v_unused_1792_);
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1791_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_toApplicative_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1791_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v_toFunctor_1763_; lean_object* v_toSeq_1764_; lean_object* v_toSeqLeft_1765_; lean_object* v_toSeqRight_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1789_; 
v_toFunctor_1763_ = lean_ctor_get(v_toApplicative_1759_, 0);
v_toSeq_1764_ = lean_ctor_get(v_toApplicative_1759_, 2);
v_toSeqLeft_1765_ = lean_ctor_get(v_toApplicative_1759_, 3);
v_toSeqRight_1766_ = lean_ctor_get(v_toApplicative_1759_, 4);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_toApplicative_1759_);
if (v_isSharedCheck_1789_ == 0)
{
lean_object* v_unused_1790_; 
v_unused_1790_ = lean_ctor_get(v_toApplicative_1759_, 1);
lean_dec(v_unused_1790_);
v___x_1768_ = v_toApplicative_1759_;
v_isShared_1769_ = v_isSharedCheck_1789_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_toSeqRight_1766_);
lean_inc(v_toSeqLeft_1765_);
lean_inc(v_toSeq_1764_);
lean_inc(v_toFunctor_1763_);
lean_dec(v_toApplicative_1759_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1789_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___f_1770_; lean_object* v___f_1771_; lean_object* v___f_1772_; lean_object* v___f_1773_; lean_object* v___x_1774_; lean_object* v___f_1775_; lean_object* v___f_1776_; lean_object* v___f_1777_; lean_object* v___x_1779_; 
v___f_1770_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1771_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1763_);
v___f_1772_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1772_, 0, v_toFunctor_1763_);
v___f_1773_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1773_, 0, v_toFunctor_1763_);
v___x_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___f_1772_);
lean_ctor_set(v___x_1774_, 1, v___f_1773_);
v___f_1775_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1775_, 0, v_toSeqRight_1766_);
v___f_1776_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1776_, 0, v_toSeqLeft_1765_);
v___f_1777_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1777_, 0, v_toSeq_1764_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 4, v___f_1775_);
lean_ctor_set(v___x_1768_, 3, v___f_1776_);
lean_ctor_set(v___x_1768_, 2, v___f_1777_);
lean_ctor_set(v___x_1768_, 1, v___f_1770_);
lean_ctor_set(v___x_1768_, 0, v___x_1774_);
v___x_1779_ = v___x_1768_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v___f_1770_);
lean_ctor_set(v_reuseFailAlloc_1788_, 2, v___f_1777_);
lean_ctor_set(v_reuseFailAlloc_1788_, 3, v___f_1776_);
lean_ctor_set(v_reuseFailAlloc_1788_, 4, v___f_1775_);
v___x_1779_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1781_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 1, v___f_1771_);
lean_ctor_set(v___x_1761_, 0, v___x_1779_);
v___x_1781_ = v___x_1761_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v___f_1771_);
v___x_1781_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_39998__overap_1785_; lean_object* v___x_1786_; 
v___x_1782_ = l_StateRefT_x27_instMonad___redArg(v___x_1781_);
v___x_1783_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_1784_ = l_instInhabitedOfMonad___redArg(v___x_1782_, v___x_1783_);
v___x_39998__overap_1785_ = lean_panic_fn_borrowed(v___x_1784_, v_msg_1726_);
lean_dec(v___x_1784_);
lean_inc(v___y_1731_);
lean_inc_ref(v___y_1730_);
lean_inc(v___y_1729_);
lean_inc_ref(v___y_1728_);
lean_inc(v___y_1727_);
v___x_1786_ = lean_apply_6(v___x_39998__overap_1785_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, lean_box(0));
return v___x_1786_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___boxed(lean_object* v_msg_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(v_msg_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
return v_res_1806_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__1(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1811_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__0));
v___x_1812_ = lean_unsigned_to_nat(66u);
v___x_1813_ = lean_unsigned_to_nat(385u);
v___x_1814_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_1815_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1816_ = l_mkPanicMessageWithDecl(v___x_1815_, v___x_1814_, v___x_1813_, v___x_1812_, v___x_1811_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono(lean_object* v_decl_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v_params_1824_; lean_object* v_type_1825_; lean_object* v_value_1826_; lean_object* v___x_1827_; 
v_params_1824_ = lean_ctor_get(v_decl_1817_, 2);
v_type_1825_ = lean_ctor_get(v_decl_1817_, 3);
v_value_1826_ = lean_ctor_get(v_decl_1817_, 4);
lean_inc_ref(v_type_1825_);
v___x_1827_ = l_Lean_Compiler_LCNF_toMonoType(v_type_1825_, v_a_1821_, v_a_1822_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; size_t v_sz_1829_; size_t v___x_1830_; lean_object* v___x_1831_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_a_1828_);
lean_dec_ref_known(v___x_1827_, 1);
v_sz_1829_ = lean_array_size(v_params_1824_);
v___x_1830_ = ((size_t)0ULL);
lean_inc_ref(v_params_1824_);
v___x_1831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_1829_, v___x_1830_, v_params_1824_, v_a_1818_, v_a_1820_, v_a_1821_, v_a_1822_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1833_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref_known(v___x_1831_, 1);
lean_inc_ref(v_value_1826_);
v___x_1833_ = l_Lean_Compiler_LCNF_Code_toMono(v_value_1826_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; uint8_t v___x_1835_; lean_object* v___x_1836_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1833_, 1);
v___x_1835_ = 0;
v___x_1836_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1835_, v_decl_1817_, v_a_1828_, v_a_1832_, v_a_1834_, v_a_1820_);
return v___x_1836_;
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
lean_dec(v_a_1832_);
lean_dec(v_a_1828_);
lean_dec_ref(v_decl_1817_);
v_a_1837_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1833_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1833_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
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
lean_dec(v_a_1828_);
lean_dec_ref(v_decl_1817_);
v_a_1845_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1831_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1831_);
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
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec_ref(v_decl_1817_);
v_a_1853_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1827_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1827_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__4(void){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1863_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_1864_ = lean_unsigned_to_nat(9u);
v___x_1865_ = lean_unsigned_to_nat(641u);
v___x_1866_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__3));
v___x_1867_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__2));
v___x_1868_ = l_mkPanicMessageWithDecl(v___x_1867_, v___x_1866_, v___x_1865_, v___x_1864_, v___x_1863_);
return v___x_1868_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__5(void){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1869_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_1870_ = lean_unsigned_to_nat(27u);
v___x_1871_ = lean_unsigned_to_nat(343u);
v___x_1872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_1873_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1874_ = l_mkPanicMessageWithDecl(v___x_1873_, v___x_1872_, v___x_1871_, v___x_1870_, v___x_1869_);
return v___x_1874_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__1(void){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1925_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_1926_ = lean_unsigned_to_nat(2u);
v___x_1927_ = lean_unsigned_to_nat(326u);
v___x_1928_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1929_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1930_ = l_mkPanicMessageWithDecl(v___x_1929_, v___x_1928_, v___x_1927_, v___x_1926_, v___x_1925_);
return v___x_1930_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__3(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1932_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__2));
v___x_1933_ = lean_unsigned_to_nat(2u);
v___x_1934_ = lean_unsigned_to_nat(328u);
v___x_1935_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1936_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1937_ = l_mkPanicMessageWithDecl(v___x_1936_, v___x_1935_, v___x_1934_, v___x_1933_, v___x_1932_);
return v___x_1937_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__5(void){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1939_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__4));
v___x_1940_ = lean_unsigned_to_nat(2u);
v___x_1941_ = lean_unsigned_to_nat(329u);
v___x_1942_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1943_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1944_ = l_mkPanicMessageWithDecl(v___x_1943_, v___x_1942_, v___x_1941_, v___x_1940_, v___x_1939_);
return v___x_1944_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__6(void){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1945_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_1946_ = lean_unsigned_to_nat(41u);
v___x_1947_ = lean_unsigned_to_nat(327u);
v___x_1948_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1949_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1950_ = l_mkPanicMessageWithDecl(v___x_1949_, v___x_1948_, v___x_1947_, v___x_1946_, v___x_1945_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono(lean_object* v_info_1951_, lean_object* v_c_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v_discr_1959_; lean_object* v_alts_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_2038_; 
v_discr_1959_ = lean_ctor_get(v_c_1952_, 2);
v_alts_1960_ = lean_ctor_get(v_c_1952_, 3);
v_isSharedCheck_2038_ = !lean_is_exclusive(v_c_1952_);
if (v_isSharedCheck_2038_ == 0)
{
lean_object* v_unused_2039_; lean_object* v_unused_2040_; 
v_unused_2039_ = lean_ctor_get(v_c_1952_, 1);
lean_dec(v_unused_2039_);
v_unused_2040_ = lean_ctor_get(v_c_1952_, 0);
lean_dec(v_unused_2040_);
v___x_1962_ = v_c_1952_;
v_isShared_1963_ = v_isSharedCheck_2038_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_alts_1960_);
lean_inc(v_discr_1959_);
lean_dec(v_c_1952_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_2038_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
v___x_1964_ = lean_array_get_size(v_alts_1960_);
v___x_1965_ = lean_unsigned_to_nat(1u);
v___x_1966_ = lean_nat_dec_eq(v___x_1964_, v___x_1965_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
lean_del_object(v___x_1962_);
lean_dec_ref(v_alts_1960_);
lean_dec(v_discr_1959_);
v___x_1967_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__1, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__1_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__1);
v___x_1968_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1967_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
return v___x_1968_;
}
else
{
uint8_t v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1969_ = 0;
v___x_1970_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_1971_ = lean_unsigned_to_nat(0u);
v___x_1972_ = lean_array_get(v___x_1970_, v_alts_1960_, v___x_1971_);
lean_dec_ref(v_alts_1960_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_ctorName_1973_; lean_object* v_params_1974_; lean_object* v_code_1975_; lean_object* v_ctorName_1976_; lean_object* v_fieldIdx_1977_; uint8_t v___x_1978_; 
v_ctorName_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_ctorName_1973_);
v_params_1974_ = lean_ctor_get(v___x_1972_, 1);
lean_inc_ref(v_params_1974_);
v_code_1975_ = lean_ctor_get(v___x_1972_, 2);
lean_inc_ref(v_code_1975_);
lean_dec_ref_known(v___x_1972_, 3);
v_ctorName_1976_ = lean_ctor_get(v_info_1951_, 0);
v_fieldIdx_1977_ = lean_ctor_get(v_info_1951_, 2);
v___x_1978_ = lean_name_eq(v_ctorName_1973_, v_ctorName_1976_);
lean_dec(v_ctorName_1973_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_dec_ref(v_code_1975_);
lean_dec_ref(v_params_1974_);
lean_del_object(v___x_1962_);
lean_dec(v_discr_1959_);
v___x_1979_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__3, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__3_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__3);
v___x_1980_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1979_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
return v___x_1980_;
}
else
{
lean_object* v___x_1981_; uint8_t v___x_1982_; 
v___x_1981_ = lean_array_get_size(v_params_1974_);
v___x_1982_ = lean_nat_dec_lt(v_fieldIdx_1977_, v___x_1981_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
lean_dec_ref(v_code_1975_);
lean_dec_ref(v_params_1974_);
lean_del_object(v___x_1962_);
lean_dec(v_discr_1959_);
v___x_1983_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__5, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__5_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__5);
v___x_1984_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1983_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
return v___x_1984_;
}
else
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_1986_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1969_, v_params_1974_, v_a_1955_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_p_1987_; lean_object* v_fvarId_1988_; lean_object* v_binderName_1989_; lean_object* v_type_1990_; lean_object* v___x_1991_; 
lean_dec_ref_known(v___x_1986_, 1);
v_p_1987_ = lean_array_get(v___x_1985_, v_params_1974_, v_fieldIdx_1977_);
lean_dec_ref(v_params_1974_);
v_fvarId_1988_ = lean_ctor_get(v_p_1987_, 0);
lean_inc(v_fvarId_1988_);
v_binderName_1989_ = lean_ctor_get(v_p_1987_, 1);
lean_inc(v_binderName_1989_);
v_type_1990_ = lean_ctor_get(v_p_1987_, 2);
lean_inc_ref(v_type_1990_);
lean_dec(v_p_1987_);
v___x_1991_ = l_Lean_Compiler_LCNF_toMonoType(v_type_1990_, v_a_1956_, v_a_1957_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1993_; lean_object* v_lctx_1994_; lean_object* v_nextIdx_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2019_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1991_, 1);
v___x_1993_ = lean_st_ref_take(v_a_1955_);
v_lctx_1994_ = lean_ctor_get(v___x_1993_, 0);
v_nextIdx_1995_ = lean_ctor_get(v___x_1993_, 1);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_1997_ = v___x_1993_;
v_isShared_1998_ = v_isSharedCheck_2019_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_nextIdx_1995_);
lean_inc(v_lctx_1994_);
lean_dec(v___x_1993_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2019_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_1999_ = ((lean_object*)(l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0));
v___x_2000_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2000_, 0, v_discr_1959_);
lean_ctor_set(v___x_2000_, 1, v___x_1999_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 3, v___x_2000_);
lean_ctor_set(v___x_1962_, 2, v_a_1992_);
lean_ctor_set(v___x_1962_, 1, v_binderName_1989_);
lean_ctor_set(v___x_1962_, 0, v_fvarId_1988_);
v___x_2002_ = v___x_1962_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_fvarId_1988_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_binderName_1989_);
lean_ctor_set(v_reuseFailAlloc_2018_, 2, v_a_1992_);
lean_ctor_set(v_reuseFailAlloc_2018_, 3, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
lean_inc_ref(v___x_2002_);
v___x_2003_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1969_, v_lctx_1994_, v___x_2002_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2003_);
v___x_2005_ = v___x_1997_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_nextIdx_1995_);
v___x_2005_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_st_ref_set(v_a_1955_, v___x_2005_);
v___x_2007_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1975_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2016_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2002_);
lean_ctor_set(v___x_2012_, 1, v_a_2008_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2012_);
v___x_2014_ = v___x_2010_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
else
{
lean_dec_ref(v___x_2002_);
return v___x_2007_;
}
}
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v_binderName_1989_);
lean_dec(v_fvarId_1988_);
lean_dec_ref(v_code_1975_);
lean_del_object(v___x_1962_);
lean_dec(v_discr_1959_);
v_a_2020_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_1991_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_1991_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec_ref(v_code_1975_);
lean_dec_ref(v_params_1974_);
lean_del_object(v___x_1962_);
lean_dec(v_discr_1959_);
v_a_2028_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_1986_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_1986_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_dec(v___x_1972_);
lean_del_object(v___x_1962_);
lean_dec(v_discr_1959_);
v___x_2036_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__6, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__6_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__6);
v___x_2037_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2036_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
return v___x_2037_;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2042_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__1));
v___x_2043_ = lean_unsigned_to_nat(70u);
v___x_2044_ = lean_unsigned_to_nat(395u);
v___x_2045_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_2046_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2047_ = l_mkPanicMessageWithDecl(v___x_2046_, v___x_2045_, v___x_2044_, v___x_2043_, v___x_2042_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(lean_object* v___x_2051_, uint8_t v___x_2052_, size_t v_sz_2053_, size_t v_i_2054_, lean_object* v_bs_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
uint8_t v___x_2062_; 
v___x_2062_ = lean_usize_dec_lt(v_i_2054_, v_sz_2053_);
if (v___x_2062_ == 0)
{
lean_object* v___x_2063_; 
lean_dec_ref(v___x_2051_);
v___x_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2063_, 0, v_bs_2055_);
return v___x_2063_;
}
else
{
lean_object* v_v_2064_; lean_object* v___x_2065_; lean_object* v_bs_x27_2066_; lean_object* v_a_2068_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; 
v_v_2064_ = lean_array_uget(v_bs_2055_, v_i_2054_);
v___x_2065_ = lean_unsigned_to_nat(0u);
v_bs_x27_2066_ = lean_array_uset(v_bs_2055_, v_i_2054_, v___x_2065_);
if (lean_obj_tag(v_v_2064_) == 0)
{
lean_object* v_ctorName_2090_; lean_object* v_params_2091_; lean_object* v_code_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2130_; 
v_ctorName_2090_ = lean_ctor_get(v_v_2064_, 0);
v_params_2091_ = lean_ctor_get(v_v_2064_, 1);
v_code_2092_ = lean_ctor_get(v_v_2064_, 2);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_v_2064_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2094_ = v_v_2064_;
v_isShared_2095_ = v_isSharedCheck_2130_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_code_2092_);
lean_inc(v_params_2091_);
lean_inc(v_ctorName_2090_);
lean_dec(v_v_2064_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2130_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2096_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4));
v___x_2097_ = l_Lean_Name_append(v_ctorName_2090_, v___x_2096_);
lean_inc(v___x_2097_);
lean_inc_ref(v___x_2051_);
v___x_2098_ = l_Lean_Environment_find_x3f(v___x_2051_, v___x_2097_, v___x_2052_);
if (lean_obj_tag(v___x_2098_) == 1)
{
lean_object* v_val_2099_; 
v_val_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_val_2099_);
lean_dec_ref_known(v___x_2098_, 1);
if (lean_obj_tag(v_val_2099_) == 6)
{
lean_object* v_val_2100_; lean_object* v_toConstantVal_2101_; lean_object* v_numParams_2102_; lean_object* v_numFields_2103_; lean_object* v_type_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v_val_2100_ = lean_ctor_get(v_val_2099_, 0);
lean_inc_ref(v_val_2100_);
lean_dec_ref_known(v_val_2099_, 1);
v_toConstantVal_2101_ = lean_ctor_get(v_val_2100_, 0);
lean_inc_ref(v_toConstantVal_2101_);
v_numParams_2102_ = lean_ctor_get(v_val_2100_, 3);
lean_inc(v_numParams_2102_);
v_numFields_2103_ = lean_ctor_get(v_val_2100_, 4);
lean_inc(v_numFields_2103_);
lean_dec_ref(v_val_2100_);
v_type_2104_ = lean_ctor_get(v_toConstantVal_2101_, 2);
lean_inc_ref(v_type_2104_);
lean_dec_ref(v_toConstantVal_2101_);
v___x_2105_ = lean_array_get_size(v_params_2091_);
v___x_2106_ = lean_nat_sub(v_numFields_2103_, v___x_2105_);
lean_dec(v_numFields_2103_);
v___x_2107_ = l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(v_type_2104_, v_numParams_2102_, v___x_2106_, v_params_2091_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
lean_dec_ref(v_params_2091_);
lean_dec(v___x_2106_);
lean_dec(v_numParams_2102_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v___x_2109_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
v___x_2109_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2092_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2112_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref_known(v___x_2109_, 1);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 2, v_a_2110_);
lean_ctor_set(v___x_2094_, 1, v_a_2108_);
lean_ctor_set(v___x_2094_, 0, v___x_2097_);
v___x_2112_ = v___x_2094_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_a_2108_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_a_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
v_a_2068_ = v___x_2112_;
goto v___jp_2067_;
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec(v_a_2108_);
lean_dec(v___x_2097_);
lean_del_object(v___x_2094_);
lean_dec_ref(v_bs_x27_2066_);
lean_dec_ref(v___x_2051_);
v_a_2114_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2109_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2109_);
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
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec(v___x_2097_);
lean_del_object(v___x_2094_);
lean_dec_ref(v_code_2092_);
lean_dec_ref(v_bs_x27_2066_);
lean_dec_ref(v___x_2051_);
v_a_2122_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2107_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2107_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
else
{
lean_dec(v_val_2099_);
lean_dec(v___x_2097_);
lean_del_object(v___x_2094_);
lean_dec_ref(v_code_2092_);
lean_dec_ref(v_params_2091_);
v___y_2074_ = v___y_2056_;
v___y_2075_ = v___y_2057_;
v___y_2076_ = v___y_2058_;
v___y_2077_ = v___y_2059_;
v___y_2078_ = v___y_2060_;
goto v___jp_2073_;
}
}
else
{
lean_dec(v___x_2098_);
lean_dec(v___x_2097_);
lean_del_object(v___x_2094_);
lean_dec_ref(v_code_2092_);
lean_dec_ref(v_params_2091_);
v___y_2074_ = v___y_2056_;
v___y_2075_ = v___y_2057_;
v___y_2076_ = v___y_2058_;
v___y_2077_ = v___y_2059_;
v___y_2078_ = v___y_2060_;
goto v___jp_2073_;
}
}
}
else
{
lean_object* v_code_2131_; lean_object* v___x_2132_; 
v_code_2131_ = lean_ctor_get(v_v_2064_, 0);
lean_inc_ref(v_code_2131_);
v___x_2132_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2131_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v___x_2134_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_2064_, v_a_2133_);
v_a_2068_ = v___x_2134_;
goto v___jp_2067_;
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec_ref_known(v_v_2064_, 1);
lean_dec_ref(v_bs_x27_2066_);
lean_dec_ref(v___x_2051_);
v_a_2135_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2132_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2132_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
v___jp_2067_:
{
size_t v___x_2069_; size_t v___x_2070_; lean_object* v___x_2071_; 
v___x_2069_ = ((size_t)1ULL);
v___x_2070_ = lean_usize_add(v_i_2054_, v___x_2069_);
v___x_2071_ = lean_array_uset(v_bs_x27_2066_, v_i_2054_, v_a_2068_);
v_i_2054_ = v___x_2070_;
v_bs_2055_ = v___x_2071_;
goto _start;
}
v___jp_2073_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2);
v___x_2080_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(v___x_2079_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_a_2081_);
lean_dec_ref_known(v___x_2080_, 1);
v_a_2068_ = v_a_2081_;
goto v___jp_2067_;
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec_ref(v_bs_x27_2066_);
lean_dec_ref(v___x_2051_);
v_a_2082_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2080_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2080_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(size_t v_sz_2143_, size_t v_i_2144_, lean_object* v_bs_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
uint8_t v___x_2152_; 
v___x_2152_ = lean_usize_dec_lt(v_i_2144_, v_sz_2143_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; 
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v_bs_2145_);
return v___x_2153_;
}
else
{
lean_object* v_v_2154_; lean_object* v___x_2155_; lean_object* v_bs_x27_2156_; lean_object* v_a_2158_; 
v_v_2154_ = lean_array_uget(v_bs_2145_, v_i_2144_);
v___x_2155_ = lean_unsigned_to_nat(0u);
v_bs_x27_2156_ = lean_array_uset(v_bs_2145_, v_i_2144_, v___x_2155_);
if (lean_obj_tag(v_v_2154_) == 0)
{
lean_object* v_params_2163_; lean_object* v_code_2164_; size_t v_sz_2165_; size_t v___x_2166_; lean_object* v___x_2167_; 
v_params_2163_ = lean_ctor_get(v_v_2154_, 1);
v_code_2164_ = lean_ctor_get(v_v_2154_, 2);
v_sz_2165_ = lean_array_size(v_params_2163_);
v___x_2166_ = ((size_t)0ULL);
lean_inc_ref(v_params_2163_);
v___x_2167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_2165_, v___x_2166_, v_params_2163_, v___y_2146_, v___y_2148_, v___y_2149_, v___y_2150_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2169_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2167_, 1);
lean_inc_ref(v_code_2164_);
v___x_2169_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2164_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; uint8_t v___x_2171_; lean_object* v___x_2172_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 1);
v___x_2171_ = 0;
v___x_2172_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v___x_2171_, v_v_2154_, v_a_2168_, v_a_2170_);
v_a_2158_ = v___x_2172_;
goto v___jp_2157_;
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_a_2168_);
lean_dec_ref_known(v_v_2154_, 3);
lean_dec_ref(v_bs_x27_2156_);
v_a_2173_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2169_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2169_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
else
{
lean_dec_ref_known(v_v_2154_, 3);
lean_dec_ref(v_bs_x27_2156_);
return v___x_2167_;
}
}
else
{
lean_object* v_code_2181_; lean_object* v___x_2182_; 
v_code_2181_ = lean_ctor_get(v_v_2154_, 0);
lean_inc_ref(v_code_2181_);
v___x_2182_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2181_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2184_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
v___x_2184_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_2154_, v_a_2183_);
v_a_2158_ = v___x_2184_;
goto v___jp_2157_;
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec_ref_known(v_v_2154_, 1);
lean_dec_ref(v_bs_x27_2156_);
v_a_2185_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2182_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2182_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
v___jp_2157_:
{
size_t v___x_2159_; size_t v___x_2160_; lean_object* v___x_2161_; 
v___x_2159_ = ((size_t)1ULL);
v___x_2160_ = lean_usize_add(v_i_2144_, v___x_2159_);
v___x_2161_ = lean_array_uset(v_bs_x27_2156_, v_i_2144_, v_a_2158_);
v_i_2144_ = v___x_2160_;
v_bs_2145_ = v___x_2161_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2194_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2195_ = lean_unsigned_to_nat(2u);
v___x_2196_ = lean_unsigned_to_nat(315u);
v___x_2197_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0));
v___x_2198_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2199_ = l_mkPanicMessageWithDecl(v___x_2198_, v___x_2197_, v___x_2196_, v___x_2195_, v___x_2194_);
return v___x_2199_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2204_ = lean_box(0);
v___x_2205_ = lean_unsigned_to_nat(2u);
v___x_2206_ = lean_mk_empty_array_with_capacity(v___x_2205_);
v___x_2207_ = lean_array_push(v___x_2206_, v___x_2204_);
return v___x_2207_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2208_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2209_ = lean_unsigned_to_nat(34u);
v___x_2210_ = lean_unsigned_to_nat(316u);
v___x_2211_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0));
v___x_2212_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2213_ = l_mkPanicMessageWithDecl(v___x_2212_, v___x_2211_, v___x_2210_, v___x_2209_, v___x_2208_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg(lean_object* v_c_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_){
_start:
{
lean_object* v_discr_2221_; lean_object* v_alts_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2291_; 
v_discr_2221_ = lean_ctor_get(v_c_2214_, 2);
v_alts_2222_ = lean_ctor_get(v_c_2214_, 3);
v_isSharedCheck_2291_ = !lean_is_exclusive(v_c_2214_);
if (v_isSharedCheck_2291_ == 0)
{
lean_object* v_unused_2292_; lean_object* v_unused_2293_; 
v_unused_2292_ = lean_ctor_get(v_c_2214_, 1);
lean_dec(v_unused_2292_);
v_unused_2293_ = lean_ctor_get(v_c_2214_, 0);
lean_dec(v_unused_2293_);
v___x_2224_ = v_c_2214_;
v_isShared_2225_ = v_isSharedCheck_2291_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_alts_2222_);
lean_inc(v_discr_2221_);
lean_dec(v_c_2214_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2291_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v___x_2226_ = lean_array_get_size(v_alts_2222_);
v___x_2227_ = lean_unsigned_to_nat(1u);
v___x_2228_ = lean_nat_dec_eq(v___x_2226_, v___x_2227_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
lean_del_object(v___x_2224_);
lean_dec_ref(v_alts_2222_);
lean_dec(v_discr_2221_);
v___x_2229_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1);
v___x_2230_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2229_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
return v___x_2230_;
}
else
{
uint8_t v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2231_ = 0;
v___x_2232_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2233_ = lean_unsigned_to_nat(0u);
v___x_2234_ = lean_array_get(v___x_2232_, v_alts_2222_, v___x_2233_);
lean_dec_ref(v_alts_2222_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_params_2235_; lean_object* v_code_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2287_; 
v_params_2235_ = lean_ctor_get(v___x_2234_, 1);
v_code_2236_ = lean_ctor_get(v___x_2234_, 2);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2287_ == 0)
{
lean_object* v_unused_2288_; 
v_unused_2288_ = lean_ctor_get(v___x_2234_, 0);
lean_dec(v_unused_2288_);
v___x_2238_ = v___x_2234_;
v_isShared_2239_ = v_isSharedCheck_2287_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_code_2236_);
lean_inc(v_params_2235_);
lean_dec(v___x_2234_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2287_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2231_, v_params_2235_, v_a_2217_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v_fvarId_2244_; lean_object* v_binderName_2245_; lean_object* v_lctx_2246_; lean_object* v_nextIdx_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2278_; 
lean_dec_ref_known(v___x_2240_, 1);
v___x_2241_ = lean_st_ref_take(v_a_2217_);
v___x_2242_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2243_ = lean_array_get(v___x_2242_, v_params_2235_, v___x_2233_);
lean_dec_ref(v_params_2235_);
v_fvarId_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_fvarId_2244_);
v_binderName_2245_ = lean_ctor_get(v___x_2243_, 1);
lean_inc(v_binderName_2245_);
lean_dec(v___x_2243_);
v_lctx_2246_ = lean_ctor_get(v___x_2241_, 0);
v_nextIdx_2247_ = lean_ctor_get(v___x_2241_, 1);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2249_ = v___x_2241_;
v_isShared_2250_ = v_isSharedCheck_2278_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_nextIdx_2247_);
lean_inc(v_lctx_2246_);
lean_dec(v___x_2241_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2278_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2257_; 
v___x_2251_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__4));
v___x_2252_ = lean_box(0);
v___x_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2253_, 0, v_discr_2221_);
v___x_2254_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_2255_ = lean_array_push(v___x_2254_, v___x_2253_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set_tag(v___x_2238_, 3);
lean_ctor_set(v___x_2238_, 2, v___x_2255_);
lean_ctor_set(v___x_2238_, 1, v___x_2252_);
lean_ctor_set(v___x_2238_, 0, v___x_2251_);
v___x_2257_ = v___x_2238_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2251_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v___x_2252_);
lean_ctor_set(v_reuseFailAlloc_2277_, 2, v___x_2255_);
v___x_2257_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
lean_object* v___x_2258_; lean_object* v___x_2260_; 
v___x_2258_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 3, v___x_2257_);
lean_ctor_set(v___x_2224_, 2, v___x_2258_);
lean_ctor_set(v___x_2224_, 1, v_binderName_2245_);
lean_ctor_set(v___x_2224_, 0, v_fvarId_2244_);
v___x_2260_ = v___x_2224_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_fvarId_2244_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_binderName_2245_);
lean_ctor_set(v_reuseFailAlloc_2276_, 2, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2276_, 3, v___x_2257_);
v___x_2260_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
lean_object* v___x_2261_; lean_object* v___x_2263_; 
lean_inc_ref(v___x_2260_);
v___x_2261_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2231_, v_lctx_2246_, v___x_2260_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 0, v___x_2261_);
v___x_2263_ = v___x_2249_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2261_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v_nextIdx_2247_);
v___x_2263_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = lean_st_ref_set(v_a_2217_, v___x_2263_);
v___x_2265_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2236_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2274_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2268_ = v___x_2265_;
v_isShared_2269_ = v_isSharedCheck_2274_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2265_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2274_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; lean_object* v___x_2272_; 
v___x_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2260_);
lean_ctor_set(v___x_2270_, 1, v_a_2266_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 0, v___x_2270_);
v___x_2272_ = v___x_2268_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
else
{
lean_dec_ref(v___x_2260_);
return v___x_2265_;
}
}
}
}
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_del_object(v___x_2238_);
lean_dec_ref(v_code_2236_);
lean_dec_ref(v_params_2235_);
lean_del_object(v___x_2224_);
lean_dec(v_discr_2221_);
v_a_2279_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2240_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2240_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
}
else
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
lean_dec(v___x_2234_);
lean_del_object(v___x_2224_);
lean_dec(v_discr_2221_);
v___x_2289_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5);
v___x_2290_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2289_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
return v___x_2290_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2295_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2296_ = lean_unsigned_to_nat(2u);
v___x_2297_ = lean_unsigned_to_nat(295u);
v___x_2298_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0));
v___x_2299_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2300_ = l_mkPanicMessageWithDecl(v___x_2299_, v___x_2298_, v___x_2297_, v___x_2296_, v___x_2295_);
return v___x_2300_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8(void){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2307_ = lean_box(0);
v___x_2308_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__7));
v___x_2309_ = l_Lean_Expr_const___override(v___x_2308_, v___x_2307_);
return v___x_2309_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9(void){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2310_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2311_ = lean_unsigned_to_nat(34u);
v___x_2312_ = lean_unsigned_to_nat(296u);
v___x_2313_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0));
v___x_2314_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2315_ = l_mkPanicMessageWithDecl(v___x_2314_, v___x_2313_, v___x_2312_, v___x_2311_, v___x_2310_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg(lean_object* v_c_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v_discr_2323_; lean_object* v_alts_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; uint8_t v___x_2327_; 
v_discr_2323_ = lean_ctor_get(v_c_2316_, 2);
v_alts_2324_ = lean_ctor_get(v_c_2316_, 3);
v___x_2325_ = lean_array_get_size(v_alts_2324_);
v___x_2326_ = lean_unsigned_to_nat(1u);
v___x_2327_ = lean_nat_dec_eq(v___x_2325_, v___x_2326_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1);
v___x_2329_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2328_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
return v___x_2329_;
}
else
{
uint8_t v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2330_ = 0;
v___x_2331_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2332_ = lean_unsigned_to_nat(0u);
v___x_2333_ = lean_array_get(v___x_2331_, v_alts_2324_, v___x_2332_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_params_2334_; lean_object* v_code_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2432_; 
v_params_2334_ = lean_ctor_get(v___x_2333_, 1);
v_code_2335_ = lean_ctor_get(v___x_2333_, 2);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2432_ == 0)
{
lean_object* v_unused_2433_; 
v_unused_2433_ = lean_ctor_get(v___x_2333_, 0);
lean_dec(v_unused_2433_);
v___x_2337_ = v___x_2333_;
v_isShared_2338_ = v_isSharedCheck_2432_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_code_2335_);
lean_inc(v_params_2334_);
lean_dec(v___x_2333_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2432_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2330_, v_params_2334_, v_a_2319_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
lean_dec_ref_known(v___x_2339_, 1);
v___x_2340_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3));
v___x_2341_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2340_, v_a_2319_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2350_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2341_, 1);
v___x_2343_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
lean_inc(v_discr_2323_);
v___x_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2344_, 0, v_discr_2323_);
v___x_2345_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5));
v___x_2346_ = lean_box(0);
v___x_2347_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_2348_ = lean_array_push(v___x_2347_, v___x_2344_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set_tag(v___x_2337_, 3);
lean_ctor_set(v___x_2337_, 2, v___x_2348_);
lean_ctor_set(v___x_2337_, 1, v___x_2346_);
lean_ctor_set(v___x_2337_, 0, v___x_2345_);
v___x_2350_ = v___x_2337_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2345_);
lean_ctor_set(v_reuseFailAlloc_2415_, 1, v___x_2346_);
lean_ctor_set(v_reuseFailAlloc_2415_, 2, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2352_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2330_, v_a_2342_, v___x_2351_, v___x_2350_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; lean_object* v___x_2356_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2353_);
lean_dec_ref_known(v___x_2352_, 1);
v___x_2354_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8);
v___x_2355_ = 0;
v___x_2356_ = l_Lean_Compiler_LCNF_mkAuxParam(v___x_2330_, v___x_2354_, v___x_2355_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2358_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_a_2357_);
lean_dec_ref_known(v___x_2356_, 1);
v___x_2358_ = l_Lean_mkArrow(v___x_2354_, v___x_2351_, v_a_2320_, v_a_2321_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v_fvarId_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v_fvarId_2363_; lean_object* v_binderName_2364_; lean_object* v_lctx_2365_; lean_object* v_nextIdx_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2390_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v___x_2358_, 1);
v_fvarId_2360_ = lean_ctor_get(v_a_2353_, 0);
v___x_2361_ = lean_st_ref_take(v_a_2319_);
v___x_2362_ = lean_array_get(v___x_2343_, v_params_2334_, v___x_2332_);
lean_dec_ref(v_params_2334_);
v_fvarId_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_fvarId_2363_);
v_binderName_2364_ = lean_ctor_get(v___x_2362_, 1);
lean_inc(v_binderName_2364_);
lean_dec(v___x_2362_);
v_lctx_2365_ = lean_ctor_get(v___x_2361_, 0);
v_nextIdx_2366_ = lean_ctor_get(v___x_2361_, 1);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2368_ = v___x_2361_;
v_isShared_2369_ = v_isSharedCheck_2390_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_nextIdx_2366_);
lean_inc(v_lctx_2365_);
lean_dec(v___x_2361_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2390_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2377_; 
lean_inc(v_fvarId_2360_);
v___x_2370_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2370_, 0, v_fvarId_2360_);
v___x_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2371_, 0, v_a_2353_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
v___x_2372_ = lean_mk_empty_array_with_capacity(v___x_2326_);
v___x_2373_ = lean_array_push(v___x_2372_, v_a_2357_);
v___x_2374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2374_, 0, v_fvarId_2363_);
lean_ctor_set(v___x_2374_, 1, v_binderName_2364_);
lean_ctor_set(v___x_2374_, 2, v___x_2373_);
lean_ctor_set(v___x_2374_, 3, v_a_2359_);
lean_ctor_set(v___x_2374_, 4, v___x_2371_);
lean_inc_ref(v___x_2374_);
v___x_2375_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_2330_, v_lctx_2365_, v___x_2374_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v___x_2375_);
v___x_2377_ = v___x_2368_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_nextIdx_2366_);
v___x_2377_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = lean_st_ref_set(v_a_2319_, v___x_2377_);
v___x_2379_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2335_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2388_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2388_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2388_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; lean_object* v___x_2386_; 
v___x_2384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2374_);
lean_ctor_set(v___x_2384_, 1, v_a_2380_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2384_);
v___x_2386_ = v___x_2382_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2384_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
else
{
lean_dec_ref_known(v___x_2374_, 5);
return v___x_2379_;
}
}
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_dec(v_a_2357_);
lean_dec(v_a_2353_);
lean_dec_ref(v_code_2335_);
lean_dec_ref(v_params_2334_);
v_a_2391_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2358_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2358_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec(v_a_2353_);
lean_dec_ref(v_code_2335_);
lean_dec_ref(v_params_2334_);
v_a_2399_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2356_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2356_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
lean_dec_ref(v_code_2335_);
lean_dec_ref(v_params_2334_);
v_a_2407_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2352_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2352_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_del_object(v___x_2337_);
lean_dec_ref(v_code_2335_);
lean_dec_ref(v_params_2334_);
v_a_2416_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2341_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2341_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
lean_del_object(v___x_2337_);
lean_dec_ref(v_code_2335_);
lean_dec_ref(v_params_2334_);
v_a_2424_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2339_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2339_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
else
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
lean_dec(v___x_2333_);
v___x_2434_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9);
v___x_2435_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2434_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
return v___x_2435_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2437_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2438_ = lean_unsigned_to_nat(2u);
v___x_2439_ = lean_unsigned_to_nat(284u);
v___x_2440_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0));
v___x_2441_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2442_ = l_mkPanicMessageWithDecl(v___x_2441_, v___x_2440_, v___x_2439_, v___x_2438_, v___x_2437_);
return v___x_2442_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2447_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2448_ = lean_unsigned_to_nat(34u);
v___x_2449_ = lean_unsigned_to_nat(285u);
v___x_2450_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0));
v___x_2451_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2452_ = l_mkPanicMessageWithDecl(v___x_2451_, v___x_2450_, v___x_2449_, v___x_2448_, v___x_2447_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg(lean_object* v_c_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v_discr_2460_; lean_object* v_alts_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2530_; 
v_discr_2460_ = lean_ctor_get(v_c_2453_, 2);
v_alts_2461_ = lean_ctor_get(v_c_2453_, 3);
v_isSharedCheck_2530_ = !lean_is_exclusive(v_c_2453_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; lean_object* v_unused_2532_; 
v_unused_2531_ = lean_ctor_get(v_c_2453_, 1);
lean_dec(v_unused_2531_);
v_unused_2532_ = lean_ctor_get(v_c_2453_, 0);
lean_dec(v_unused_2532_);
v___x_2463_ = v_c_2453_;
v_isShared_2464_ = v_isSharedCheck_2530_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_alts_2461_);
lean_inc(v_discr_2460_);
lean_dec(v_c_2453_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2530_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2465_ = lean_array_get_size(v_alts_2461_);
v___x_2466_ = lean_unsigned_to_nat(1u);
v___x_2467_ = lean_nat_dec_eq(v___x_2465_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
lean_del_object(v___x_2463_);
lean_dec_ref(v_alts_2461_);
lean_dec(v_discr_2460_);
v___x_2468_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1);
v___x_2469_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2468_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_);
return v___x_2469_;
}
else
{
uint8_t v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2470_ = 0;
v___x_2471_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2472_ = lean_unsigned_to_nat(0u);
v___x_2473_ = lean_array_get(v___x_2471_, v_alts_2461_, v___x_2472_);
lean_dec_ref(v_alts_2461_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_params_2474_; lean_object* v_code_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2526_; 
v_params_2474_ = lean_ctor_get(v___x_2473_, 1);
v_code_2475_ = lean_ctor_get(v___x_2473_, 2);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2526_ == 0)
{
lean_object* v_unused_2527_; 
v_unused_2527_ = lean_ctor_get(v___x_2473_, 0);
lean_dec(v_unused_2527_);
v___x_2477_ = v___x_2473_;
v_isShared_2478_ = v_isSharedCheck_2526_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_code_2475_);
lean_inc(v_params_2474_);
lean_dec(v___x_2473_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2526_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2470_, v_params_2474_, v_a_2456_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v_fvarId_2483_; lean_object* v_binderName_2484_; lean_object* v_lctx_2485_; lean_object* v_nextIdx_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2517_; 
lean_dec_ref_known(v___x_2479_, 1);
v___x_2480_ = lean_st_ref_take(v_a_2456_);
v___x_2481_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2482_ = lean_array_get(v___x_2481_, v_params_2474_, v___x_2472_);
lean_dec_ref(v_params_2474_);
v_fvarId_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_fvarId_2483_);
v_binderName_2484_ = lean_ctor_get(v___x_2482_, 1);
lean_inc(v_binderName_2484_);
lean_dec(v___x_2482_);
v_lctx_2485_ = lean_ctor_get(v___x_2480_, 0);
v_nextIdx_2486_ = lean_ctor_get(v___x_2480_, 1);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2488_ = v___x_2480_;
v_isShared_2489_ = v_isSharedCheck_2517_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_nextIdx_2486_);
lean_inc(v_lctx_2485_);
lean_dec(v___x_2480_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2517_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2496_; 
v___x_2490_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__4));
v___x_2491_ = lean_box(0);
v___x_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2492_, 0, v_discr_2460_);
v___x_2493_ = lean_mk_empty_array_with_capacity(v___x_2466_);
v___x_2494_ = lean_array_push(v___x_2493_, v___x_2492_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set_tag(v___x_2477_, 3);
lean_ctor_set(v___x_2477_, 2, v___x_2494_);
lean_ctor_set(v___x_2477_, 1, v___x_2491_);
lean_ctor_set(v___x_2477_, 0, v___x_2490_);
v___x_2496_ = v___x_2477_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v___x_2491_);
lean_ctor_set(v_reuseFailAlloc_2516_, 2, v___x_2494_);
v___x_2496_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2497_; lean_object* v___x_2499_; 
v___x_2497_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 3, v___x_2496_);
lean_ctor_set(v___x_2463_, 2, v___x_2497_);
lean_ctor_set(v___x_2463_, 1, v_binderName_2484_);
lean_ctor_set(v___x_2463_, 0, v_fvarId_2483_);
v___x_2499_ = v___x_2463_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_fvarId_2483_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_binderName_2484_);
lean_ctor_set(v_reuseFailAlloc_2515_, 2, v___x_2497_);
lean_ctor_set(v_reuseFailAlloc_2515_, 3, v___x_2496_);
v___x_2499_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
lean_object* v___x_2500_; lean_object* v___x_2502_; 
lean_inc_ref(v___x_2499_);
v___x_2500_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2470_, v_lctx_2485_, v___x_2499_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 0, v___x_2500_);
v___x_2502_ = v___x_2488_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2500_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_nextIdx_2486_);
v___x_2502_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = lean_st_ref_set(v_a_2456_, v___x_2502_);
v___x_2504_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2475_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2513_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2507_ = v___x_2504_;
v_isShared_2508_ = v_isSharedCheck_2513_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2513_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2509_; lean_object* v___x_2511_; 
v___x_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2499_);
lean_ctor_set(v___x_2509_, 1, v_a_2505_);
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 0, v___x_2509_);
v___x_2511_ = v___x_2507_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2509_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
else
{
lean_dec_ref(v___x_2499_);
return v___x_2504_;
}
}
}
}
}
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_del_object(v___x_2477_);
lean_dec_ref(v_code_2475_);
lean_dec_ref(v_params_2474_);
lean_del_object(v___x_2463_);
lean_dec(v_discr_2460_);
v_a_2518_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2479_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2479_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
else
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
lean_dec(v___x_2473_);
lean_del_object(v___x_2463_);
lean_dec(v_discr_2460_);
v___x_2528_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5);
v___x_2529_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2528_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_);
return v___x_2529_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2534_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2535_ = lean_unsigned_to_nat(2u);
v___x_2536_ = lean_unsigned_to_nat(273u);
v___x_2537_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0));
v___x_2538_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2539_ = l_mkPanicMessageWithDecl(v___x_2538_, v___x_2537_, v___x_2536_, v___x_2535_, v___x_2534_);
return v___x_2539_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2544_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2545_ = lean_unsigned_to_nat(34u);
v___x_2546_ = lean_unsigned_to_nat(274u);
v___x_2547_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0));
v___x_2548_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2549_ = l_mkPanicMessageWithDecl(v___x_2548_, v___x_2547_, v___x_2546_, v___x_2545_, v___x_2544_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(lean_object* v_c_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_){
_start:
{
lean_object* v_discr_2557_; lean_object* v_alts_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2627_; 
v_discr_2557_ = lean_ctor_get(v_c_2550_, 2);
v_alts_2558_ = lean_ctor_get(v_c_2550_, 3);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_c_2550_);
if (v_isSharedCheck_2627_ == 0)
{
lean_object* v_unused_2628_; lean_object* v_unused_2629_; 
v_unused_2628_ = lean_ctor_get(v_c_2550_, 1);
lean_dec(v_unused_2628_);
v_unused_2629_ = lean_ctor_get(v_c_2550_, 0);
lean_dec(v_unused_2629_);
v___x_2560_ = v_c_2550_;
v_isShared_2561_ = v_isSharedCheck_2627_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_alts_2558_);
lean_inc(v_discr_2557_);
lean_dec(v_c_2550_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2627_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; 
v___x_2562_ = lean_array_get_size(v_alts_2558_);
v___x_2563_ = lean_unsigned_to_nat(1u);
v___x_2564_ = lean_nat_dec_eq(v___x_2562_, v___x_2563_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
lean_del_object(v___x_2560_);
lean_dec_ref(v_alts_2558_);
lean_dec(v_discr_2557_);
v___x_2565_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1);
v___x_2566_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2565_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_);
return v___x_2566_;
}
else
{
uint8_t v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2567_ = 0;
v___x_2568_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2569_ = lean_unsigned_to_nat(0u);
v___x_2570_ = lean_array_get(v___x_2568_, v_alts_2558_, v___x_2569_);
lean_dec_ref(v_alts_2558_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_params_2571_; lean_object* v_code_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2623_; 
v_params_2571_ = lean_ctor_get(v___x_2570_, 1);
v_code_2572_ = lean_ctor_get(v___x_2570_, 2);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2623_ == 0)
{
lean_object* v_unused_2624_; 
v_unused_2624_ = lean_ctor_get(v___x_2570_, 0);
lean_dec(v_unused_2624_);
v___x_2574_ = v___x_2570_;
v_isShared_2575_ = v_isSharedCheck_2623_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_code_2572_);
lean_inc(v_params_2571_);
lean_dec(v___x_2570_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2623_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; 
v___x_2576_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2567_, v_params_2571_, v_a_2553_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v_fvarId_2580_; lean_object* v_binderName_2581_; lean_object* v_lctx_2582_; lean_object* v_nextIdx_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2614_; 
lean_dec_ref_known(v___x_2576_, 1);
v___x_2577_ = lean_st_ref_take(v_a_2553_);
v___x_2578_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2579_ = lean_array_get(v___x_2578_, v_params_2571_, v___x_2569_);
lean_dec_ref(v_params_2571_);
v_fvarId_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_fvarId_2580_);
v_binderName_2581_ = lean_ctor_get(v___x_2579_, 1);
lean_inc(v_binderName_2581_);
lean_dec(v___x_2579_);
v_lctx_2582_ = lean_ctor_get(v___x_2577_, 0);
v_nextIdx_2583_ = lean_ctor_get(v___x_2577_, 1);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2585_ = v___x_2577_;
v_isShared_2586_ = v_isSharedCheck_2614_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_nextIdx_2583_);
lean_inc(v_lctx_2582_);
lean_dec(v___x_2577_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2614_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2593_; 
v___x_2587_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__3));
v___x_2588_ = lean_box(0);
v___x_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2589_, 0, v_discr_2557_);
v___x_2590_ = lean_mk_empty_array_with_capacity(v___x_2563_);
v___x_2591_ = lean_array_push(v___x_2590_, v___x_2589_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set_tag(v___x_2574_, 3);
lean_ctor_set(v___x_2574_, 2, v___x_2591_);
lean_ctor_set(v___x_2574_, 1, v___x_2588_);
lean_ctor_set(v___x_2574_, 0, v___x_2587_);
v___x_2593_ = v___x_2574_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2587_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v___x_2588_);
lean_ctor_set(v_reuseFailAlloc_2613_, 2, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2594_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 3, v___x_2593_);
lean_ctor_set(v___x_2560_, 2, v___x_2594_);
lean_ctor_set(v___x_2560_, 1, v_binderName_2581_);
lean_ctor_set(v___x_2560_, 0, v_fvarId_2580_);
v___x_2596_ = v___x_2560_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_fvarId_2580_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_binderName_2581_);
lean_ctor_set(v_reuseFailAlloc_2612_, 2, v___x_2594_);
lean_ctor_set(v_reuseFailAlloc_2612_, 3, v___x_2593_);
v___x_2596_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
lean_object* v___x_2597_; lean_object* v___x_2599_; 
lean_inc_ref(v___x_2596_);
v___x_2597_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2567_, v_lctx_2582_, v___x_2596_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2597_);
v___x_2599_ = v___x_2585_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v_nextIdx_2583_);
v___x_2599_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = lean_st_ref_set(v_a_2553_, v___x_2599_);
v___x_2601_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2572_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2610_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2610_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2610_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2606_; lean_object* v___x_2608_; 
v___x_2606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2596_);
lean_ctor_set(v___x_2606_, 1, v_a_2602_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v___x_2606_);
v___x_2608_ = v___x_2604_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
else
{
lean_dec_ref(v___x_2596_);
return v___x_2601_;
}
}
}
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_del_object(v___x_2574_);
lean_dec_ref(v_code_2572_);
lean_dec_ref(v_params_2571_);
lean_del_object(v___x_2560_);
lean_dec(v_discr_2557_);
v_a_2615_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2576_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2576_);
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
else
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_dec(v___x_2570_);
lean_del_object(v___x_2560_);
lean_dec(v_discr_2557_);
v___x_2625_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4);
v___x_2626_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2625_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_);
return v___x_2626_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2631_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2632_ = lean_unsigned_to_nat(2u);
v___x_2633_ = lean_unsigned_to_nat(261u);
v___x_2634_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0));
v___x_2635_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2636_ = l_mkPanicMessageWithDecl(v___x_2635_, v___x_2634_, v___x_2633_, v___x_2632_, v___x_2631_);
return v___x_2636_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2640_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2641_ = lean_unsigned_to_nat(34u);
v___x_2642_ = lean_unsigned_to_nat(262u);
v___x_2643_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0));
v___x_2644_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2645_ = l_mkPanicMessageWithDecl(v___x_2644_, v___x_2643_, v___x_2642_, v___x_2641_, v___x_2640_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(lean_object* v_c_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_){
_start:
{
lean_object* v_discr_2653_; lean_object* v_alts_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2723_; 
v_discr_2653_ = lean_ctor_get(v_c_2646_, 2);
v_alts_2654_ = lean_ctor_get(v_c_2646_, 3);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_c_2646_);
if (v_isSharedCheck_2723_ == 0)
{
lean_object* v_unused_2724_; lean_object* v_unused_2725_; 
v_unused_2724_ = lean_ctor_get(v_c_2646_, 1);
lean_dec(v_unused_2724_);
v_unused_2725_ = lean_ctor_get(v_c_2646_, 0);
lean_dec(v_unused_2725_);
v___x_2656_ = v_c_2646_;
v_isShared_2657_ = v_isSharedCheck_2723_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_alts_2654_);
lean_inc(v_discr_2653_);
lean_dec(v_c_2646_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2723_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; uint8_t v___x_2660_; 
v___x_2658_ = lean_array_get_size(v_alts_2654_);
v___x_2659_ = lean_unsigned_to_nat(1u);
v___x_2660_ = lean_nat_dec_eq(v___x_2658_, v___x_2659_);
if (v___x_2660_ == 0)
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
lean_del_object(v___x_2656_);
lean_dec_ref(v_alts_2654_);
lean_dec(v_discr_2653_);
v___x_2661_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1);
v___x_2662_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2661_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
return v___x_2662_;
}
else
{
uint8_t v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2663_ = 0;
v___x_2664_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2665_ = lean_unsigned_to_nat(0u);
v___x_2666_ = lean_array_get(v___x_2664_, v_alts_2654_, v___x_2665_);
lean_dec_ref(v_alts_2654_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_params_2667_; lean_object* v_code_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2719_; 
v_params_2667_ = lean_ctor_get(v___x_2666_, 1);
v_code_2668_ = lean_ctor_get(v___x_2666_, 2);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2719_ == 0)
{
lean_object* v_unused_2720_; 
v_unused_2720_ = lean_ctor_get(v___x_2666_, 0);
lean_dec(v_unused_2720_);
v___x_2670_ = v___x_2666_;
v_isShared_2671_ = v_isSharedCheck_2719_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_code_2668_);
lean_inc(v_params_2667_);
lean_dec(v___x_2666_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2719_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2663_, v_params_2667_, v_a_2649_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v_fvarId_2676_; lean_object* v_binderName_2677_; lean_object* v_lctx_2678_; lean_object* v_nextIdx_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2710_; 
lean_dec_ref_known(v___x_2672_, 1);
v___x_2673_ = lean_st_ref_take(v_a_2649_);
v___x_2674_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2675_ = lean_array_get(v___x_2674_, v_params_2667_, v___x_2665_);
lean_dec_ref(v_params_2667_);
v_fvarId_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_fvarId_2676_);
v_binderName_2677_ = lean_ctor_get(v___x_2675_, 1);
lean_inc(v_binderName_2677_);
lean_dec(v___x_2675_);
v_lctx_2678_ = lean_ctor_get(v___x_2673_, 0);
v_nextIdx_2679_ = lean_ctor_get(v___x_2673_, 1);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2681_ = v___x_2673_;
v_isShared_2682_ = v_isSharedCheck_2710_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_nextIdx_2679_);
lean_inc(v_lctx_2678_);
lean_dec(v___x_2673_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2710_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2689_; 
v___x_2683_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__4));
v___x_2684_ = lean_box(0);
v___x_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2685_, 0, v_discr_2653_);
v___x_2686_ = lean_mk_empty_array_with_capacity(v___x_2659_);
v___x_2687_ = lean_array_push(v___x_2686_, v___x_2685_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set_tag(v___x_2670_, 3);
lean_ctor_set(v___x_2670_, 2, v___x_2687_);
lean_ctor_set(v___x_2670_, 1, v___x_2684_);
lean_ctor_set(v___x_2670_, 0, v___x_2683_);
v___x_2689_ = v___x_2670_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2683_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v___x_2684_);
lean_ctor_set(v_reuseFailAlloc_2709_, 2, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_object* v___x_2690_; lean_object* v___x_2692_; 
v___x_2690_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 3, v___x_2689_);
lean_ctor_set(v___x_2656_, 2, v___x_2690_);
lean_ctor_set(v___x_2656_, 1, v_binderName_2677_);
lean_ctor_set(v___x_2656_, 0, v_fvarId_2676_);
v___x_2692_ = v___x_2656_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_fvarId_2676_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_binderName_2677_);
lean_ctor_set(v_reuseFailAlloc_2708_, 2, v___x_2690_);
lean_ctor_set(v_reuseFailAlloc_2708_, 3, v___x_2689_);
v___x_2692_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
lean_object* v___x_2693_; lean_object* v___x_2695_; 
lean_inc_ref(v___x_2692_);
v___x_2693_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2663_, v_lctx_2678_, v___x_2692_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v___x_2693_);
v___x_2695_ = v___x_2681_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2693_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v_nextIdx_2679_);
v___x_2695_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2696_ = lean_st_ref_set(v_a_2649_, v___x_2695_);
v___x_2697_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2668_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2706_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2700_ = v___x_2697_;
v_isShared_2701_ = v_isSharedCheck_2706_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2697_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2706_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2692_);
lean_ctor_set(v___x_2702_, 1, v_a_2698_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_2702_);
v___x_2704_ = v___x_2700_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
else
{
lean_dec_ref(v___x_2692_);
return v___x_2697_;
}
}
}
}
}
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_del_object(v___x_2670_);
lean_dec_ref(v_code_2668_);
lean_dec_ref(v_params_2667_);
lean_del_object(v___x_2656_);
lean_dec(v_discr_2653_);
v_a_2711_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2672_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2672_);
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
}
}
else
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
lean_dec(v___x_2666_);
lean_del_object(v___x_2656_);
lean_dec(v_discr_2653_);
v___x_2721_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5);
v___x_2722_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2721_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
return v___x_2722_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2727_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2728_ = lean_unsigned_to_nat(2u);
v___x_2729_ = lean_unsigned_to_nat(249u);
v___x_2730_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0));
v___x_2731_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2732_ = l_mkPanicMessageWithDecl(v___x_2731_, v___x_2730_, v___x_2729_, v___x_2728_, v___x_2727_);
return v___x_2732_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6(void){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2737_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2738_ = lean_unsigned_to_nat(34u);
v___x_2739_ = lean_unsigned_to_nat(250u);
v___x_2740_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0));
v___x_2741_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2742_ = l_mkPanicMessageWithDecl(v___x_2741_, v___x_2740_, v___x_2739_, v___x_2738_, v___x_2737_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg(lean_object* v_c_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_){
_start:
{
lean_object* v_discr_2750_; lean_object* v_alts_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2820_; 
v_discr_2750_ = lean_ctor_get(v_c_2743_, 2);
v_alts_2751_ = lean_ctor_get(v_c_2743_, 3);
v_isSharedCheck_2820_ = !lean_is_exclusive(v_c_2743_);
if (v_isSharedCheck_2820_ == 0)
{
lean_object* v_unused_2821_; lean_object* v_unused_2822_; 
v_unused_2821_ = lean_ctor_get(v_c_2743_, 1);
lean_dec(v_unused_2821_);
v_unused_2822_ = lean_ctor_get(v_c_2743_, 0);
lean_dec(v_unused_2822_);
v___x_2753_ = v_c_2743_;
v_isShared_2754_ = v_isSharedCheck_2820_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_alts_2751_);
lean_inc(v_discr_2750_);
lean_dec(v_c_2743_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2820_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; uint8_t v___x_2757_; 
v___x_2755_ = lean_array_get_size(v_alts_2751_);
v___x_2756_ = lean_unsigned_to_nat(1u);
v___x_2757_ = lean_nat_dec_eq(v___x_2755_, v___x_2756_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
lean_del_object(v___x_2753_);
lean_dec_ref(v_alts_2751_);
lean_dec(v_discr_2750_);
v___x_2758_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1);
v___x_2759_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2758_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_);
return v___x_2759_;
}
else
{
uint8_t v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2760_ = 0;
v___x_2761_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2762_ = lean_unsigned_to_nat(0u);
v___x_2763_ = lean_array_get(v___x_2761_, v_alts_2751_, v___x_2762_);
lean_dec_ref(v_alts_2751_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_params_2764_; lean_object* v_code_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2816_; 
v_params_2764_ = lean_ctor_get(v___x_2763_, 1);
v_code_2765_ = lean_ctor_get(v___x_2763_, 2);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2816_ == 0)
{
lean_object* v_unused_2817_; 
v_unused_2817_ = lean_ctor_get(v___x_2763_, 0);
lean_dec(v_unused_2817_);
v___x_2767_ = v___x_2763_;
v_isShared_2768_ = v_isSharedCheck_2816_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_code_2765_);
lean_inc(v_params_2764_);
lean_dec(v___x_2763_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2816_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2769_; 
v___x_2769_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2760_, v_params_2764_, v_a_2746_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v_fvarId_2773_; lean_object* v_binderName_2774_; lean_object* v_lctx_2775_; lean_object* v_nextIdx_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2807_; 
lean_dec_ref_known(v___x_2769_, 1);
v___x_2770_ = lean_st_ref_take(v_a_2746_);
v___x_2771_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2772_ = lean_array_get(v___x_2771_, v_params_2764_, v___x_2762_);
lean_dec_ref(v_params_2764_);
v_fvarId_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_fvarId_2773_);
v_binderName_2774_ = lean_ctor_get(v___x_2772_, 1);
lean_inc(v_binderName_2774_);
lean_dec(v___x_2772_);
v_lctx_2775_ = lean_ctor_get(v___x_2770_, 0);
v_nextIdx_2776_ = lean_ctor_get(v___x_2770_, 1);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2778_ = v___x_2770_;
v_isShared_2779_ = v_isSharedCheck_2807_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_nextIdx_2776_);
lean_inc(v_lctx_2775_);
lean_dec(v___x_2770_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2807_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2786_; 
v___x_2780_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__4));
v___x_2781_ = lean_box(0);
v___x_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2782_, 0, v_discr_2750_);
v___x_2783_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_2784_ = lean_array_push(v___x_2783_, v___x_2782_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set_tag(v___x_2767_, 3);
lean_ctor_set(v___x_2767_, 2, v___x_2784_);
lean_ctor_set(v___x_2767_, 1, v___x_2781_);
lean_ctor_set(v___x_2767_, 0, v___x_2780_);
v___x_2786_ = v___x_2767_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v___x_2781_);
lean_ctor_set(v_reuseFailAlloc_2806_, 2, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_object* v___x_2787_; lean_object* v___x_2789_; 
v___x_2787_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 3, v___x_2786_);
lean_ctor_set(v___x_2753_, 2, v___x_2787_);
lean_ctor_set(v___x_2753_, 1, v_binderName_2774_);
lean_ctor_set(v___x_2753_, 0, v_fvarId_2773_);
v___x_2789_ = v___x_2753_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_fvarId_2773_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v_binderName_2774_);
lean_ctor_set(v_reuseFailAlloc_2805_, 2, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2805_, 3, v___x_2786_);
v___x_2789_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
lean_object* v___x_2790_; lean_object* v___x_2792_; 
lean_inc_ref(v___x_2789_);
v___x_2790_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2760_, v_lctx_2775_, v___x_2789_);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 0, v___x_2790_);
v___x_2792_ = v___x_2778_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2790_);
lean_ctor_set(v_reuseFailAlloc_2804_, 1, v_nextIdx_2776_);
v___x_2792_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = lean_st_ref_set(v_a_2746_, v___x_2792_);
v___x_2794_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2765_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2803_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2797_ = v___x_2794_;
v_isShared_2798_ = v_isSharedCheck_2803_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2794_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2803_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2799_; lean_object* v___x_2801_; 
v___x_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2789_);
lean_ctor_set(v___x_2799_, 1, v_a_2795_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 0, v___x_2799_);
v___x_2801_ = v___x_2797_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2799_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
else
{
lean_dec_ref(v___x_2789_);
return v___x_2794_;
}
}
}
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_del_object(v___x_2767_);
lean_dec_ref(v_code_2765_);
lean_dec_ref(v_params_2764_);
lean_del_object(v___x_2753_);
lean_dec(v_discr_2750_);
v_a_2808_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2769_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2769_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
}
else
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
lean_dec(v___x_2763_);
lean_del_object(v___x_2753_);
lean_dec(v_discr_2750_);
v___x_2818_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6);
v___x_2819_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2818_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_);
return v___x_2819_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2(void){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2824_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2825_ = lean_unsigned_to_nat(2u);
v___x_2826_ = lean_unsigned_to_nat(238u);
v___x_2827_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0));
v___x_2828_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2829_ = l_mkPanicMessageWithDecl(v___x_2828_, v___x_2827_, v___x_2826_, v___x_2825_, v___x_2824_);
return v___x_2829_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2831_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2832_ = lean_unsigned_to_nat(34u);
v___x_2833_ = lean_unsigned_to_nat(239u);
v___x_2834_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0));
v___x_2835_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2836_ = l_mkPanicMessageWithDecl(v___x_2835_, v___x_2834_, v___x_2833_, v___x_2832_, v___x_2831_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg(lean_object* v_c_2837_, lean_object* v_uintName_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_){
_start:
{
lean_object* v_discr_2845_; lean_object* v_alts_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2916_; 
v_discr_2845_ = lean_ctor_get(v_c_2837_, 2);
v_alts_2846_ = lean_ctor_get(v_c_2837_, 3);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_c_2837_);
if (v_isSharedCheck_2916_ == 0)
{
lean_object* v_unused_2917_; lean_object* v_unused_2918_; 
v_unused_2917_ = lean_ctor_get(v_c_2837_, 1);
lean_dec(v_unused_2917_);
v_unused_2918_ = lean_ctor_get(v_c_2837_, 0);
lean_dec(v_unused_2918_);
v___x_2848_ = v_c_2837_;
v_isShared_2849_ = v_isSharedCheck_2916_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_alts_2846_);
lean_inc(v_discr_2845_);
lean_dec(v_c_2837_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2916_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; 
v___x_2850_ = lean_array_get_size(v_alts_2846_);
v___x_2851_ = lean_unsigned_to_nat(1u);
v___x_2852_ = lean_nat_dec_eq(v___x_2850_, v___x_2851_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
lean_del_object(v___x_2848_);
lean_dec_ref(v_alts_2846_);
lean_dec(v_discr_2845_);
lean_dec(v_uintName_2838_);
v___x_2853_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2);
v___x_2854_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2853_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_);
return v___x_2854_;
}
else
{
uint8_t v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2855_ = 0;
v___x_2856_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2857_ = lean_unsigned_to_nat(0u);
v___x_2858_ = lean_array_get(v___x_2856_, v_alts_2846_, v___x_2857_);
lean_dec_ref(v_alts_2846_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_params_2859_; lean_object* v_code_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2912_; 
v_params_2859_ = lean_ctor_get(v___x_2858_, 1);
v_code_2860_ = lean_ctor_get(v___x_2858_, 2);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2912_ == 0)
{
lean_object* v_unused_2913_; 
v_unused_2913_ = lean_ctor_get(v___x_2858_, 0);
lean_dec(v_unused_2913_);
v___x_2862_ = v___x_2858_;
v_isShared_2863_ = v_isSharedCheck_2912_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_code_2860_);
lean_inc(v_params_2859_);
lean_dec(v___x_2858_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2912_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2855_, v_params_2859_, v_a_2841_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v_fvarId_2868_; lean_object* v_binderName_2869_; lean_object* v_lctx_2870_; lean_object* v_nextIdx_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2903_; 
lean_dec_ref_known(v___x_2864_, 1);
v___x_2865_ = lean_st_ref_take(v_a_2841_);
v___x_2866_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2867_ = lean_array_get(v___x_2866_, v_params_2859_, v___x_2857_);
lean_dec_ref(v_params_2859_);
v_fvarId_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_fvarId_2868_);
v_binderName_2869_ = lean_ctor_get(v___x_2867_, 1);
lean_inc(v_binderName_2869_);
lean_dec(v___x_2867_);
v_lctx_2870_ = lean_ctor_get(v___x_2865_, 0);
v_nextIdx_2871_ = lean_ctor_get(v___x_2865_, 1);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2873_ = v___x_2865_;
v_isShared_2874_ = v_isSharedCheck_2903_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_nextIdx_2871_);
lean_inc(v_lctx_2870_);
lean_dec(v___x_2865_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2903_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2882_; 
v___x_2875_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3));
v___x_2876_ = l_Lean_Name_str___override(v_uintName_2838_, v___x_2875_);
v___x_2877_ = lean_box(0);
v___x_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2878_, 0, v_discr_2845_);
v___x_2879_ = lean_mk_empty_array_with_capacity(v___x_2851_);
v___x_2880_ = lean_array_push(v___x_2879_, v___x_2878_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set_tag(v___x_2862_, 3);
lean_ctor_set(v___x_2862_, 2, v___x_2880_);
lean_ctor_set(v___x_2862_, 1, v___x_2877_);
lean_ctor_set(v___x_2862_, 0, v___x_2876_);
v___x_2882_ = v___x_2862_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2876_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v___x_2877_);
lean_ctor_set(v_reuseFailAlloc_2902_, 2, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2883_; lean_object* v___x_2885_; 
v___x_2883_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 3, v___x_2882_);
lean_ctor_set(v___x_2848_, 2, v___x_2883_);
lean_ctor_set(v___x_2848_, 1, v_binderName_2869_);
lean_ctor_set(v___x_2848_, 0, v_fvarId_2868_);
v___x_2885_ = v___x_2848_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_fvarId_2868_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_binderName_2869_);
lean_ctor_set(v_reuseFailAlloc_2901_, 2, v___x_2883_);
lean_ctor_set(v_reuseFailAlloc_2901_, 3, v___x_2882_);
v___x_2885_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
lean_object* v___x_2886_; lean_object* v___x_2888_; 
lean_inc_ref(v___x_2885_);
v___x_2886_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2855_, v_lctx_2870_, v___x_2885_);
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 0, v___x_2886_);
v___x_2888_ = v___x_2873_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2886_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v_nextIdx_2871_);
v___x_2888_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = lean_st_ref_set(v_a_2841_, v___x_2888_);
v___x_2890_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2860_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2899_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2893_ = v___x_2890_;
v_isShared_2894_ = v_isSharedCheck_2899_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2890_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2899_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2885_);
lean_ctor_set(v___x_2895_, 1, v_a_2891_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v___x_2895_);
v___x_2897_ = v___x_2893_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2895_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
else
{
lean_dec_ref(v___x_2885_);
return v___x_2890_;
}
}
}
}
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_del_object(v___x_2862_);
lean_dec_ref(v_code_2860_);
lean_dec_ref(v_params_2859_);
lean_del_object(v___x_2848_);
lean_dec(v_discr_2845_);
lean_dec(v_uintName_2838_);
v_a_2904_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2864_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2864_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
}
else
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
lean_dec(v___x_2858_);
lean_del_object(v___x_2848_);
lean_dec(v_discr_2845_);
lean_dec(v_uintName_2838_);
v___x_2914_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4);
v___x_2915_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2914_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_);
return v___x_2915_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2919_ = lean_box(0);
v___x_2920_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0));
v___x_2921_ = l_Lean_mkConst(v___x_2920_, v___x_2919_);
return v___x_2921_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6(void){
_start:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2928_ = lean_box(0);
v___x_2929_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3));
v___x_2930_ = l_Lean_mkConst(v___x_2929_, v___x_2928_);
return v___x_2930_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2938_ = lean_box(0);
v___x_2939_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
v___x_2940_ = l_Lean_mkConst(v___x_2939_, v___x_2938_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16(lean_object* v___x_2965_, size_t v_sz_2966_, size_t v_i_2967_, lean_object* v_bs_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
uint8_t v___x_2975_; 
v___x_2975_ = lean_usize_dec_lt(v_i_2967_, v_sz_2966_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; 
lean_dec(v___x_2965_);
v___x_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2976_, 0, v_bs_2968_);
return v___x_2976_;
}
else
{
lean_object* v_v_2977_; lean_object* v___x_2978_; lean_object* v_bs_x27_2979_; lean_object* v_a_2981_; 
v_v_2977_ = lean_array_uget(v_bs_2968_, v_i_2967_);
v___x_2978_ = lean_unsigned_to_nat(0u);
v_bs_x27_2979_ = lean_array_uset(v_bs_2968_, v_i_2967_, v___x_2978_);
if (lean_obj_tag(v_v_2977_) == 0)
{
lean_object* v_ctorName_2986_; lean_object* v_params_2987_; lean_object* v_code_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3115_; 
v_ctorName_2986_ = lean_ctor_get(v_v_2977_, 0);
v_params_2987_ = lean_ctor_get(v_v_2977_, 1);
v_code_2988_ = lean_ctor_get(v_v_2977_, 2);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_v_2977_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_2990_ = v_v_2977_;
v_isShared_2991_ = v_isSharedCheck_3115_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_code_2988_);
lean_inc(v_params_2987_);
lean_inc(v_ctorName_2986_);
lean_dec(v_v_2977_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3115_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
uint8_t v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2992_ = 0;
v___x_2993_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2994_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2992_, v_params_2987_, v___y_2971_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; uint8_t v___x_2999_; 
lean_dec_ref_known(v___x_2994_, 1);
v___x_2995_ = lean_box(0);
v___x_2996_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_2997_ = lean_array_get(v___x_2993_, v_params_2987_, v___x_2978_);
lean_dec_ref(v_params_2987_);
v___x_2998_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__1));
v___x_2999_ = lean_name_eq(v_ctorName_2986_, v___x_2998_);
lean_dec(v_ctorName_2986_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; lean_object* v_fvarId_3001_; lean_object* v_binderName_3002_; lean_object* v_lctx_3003_; lean_object* v_nextIdx_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3035_; 
v___x_3000_ = lean_st_ref_take(v___y_2971_);
v_fvarId_3001_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_fvarId_3001_);
v_binderName_3002_ = lean_ctor_get(v___x_2997_, 1);
lean_inc(v_binderName_3002_);
lean_dec(v___x_2997_);
v_lctx_3003_ = lean_ctor_get(v___x_3000_, 0);
v_nextIdx_3004_ = lean_ctor_get(v___x_3000_, 1);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3006_ = v___x_3000_;
v_isShared_3007_ = v_isSharedCheck_3035_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_nextIdx_3004_);
lean_inc(v_lctx_3003_);
lean_dec(v___x_3000_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3035_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3016_; 
v___x_3008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__3));
v___x_3009_ = lean_unsigned_to_nat(1u);
v___x_3010_ = lean_mk_empty_array_with_capacity(v___x_3009_);
lean_inc(v___x_2965_);
v___x_3011_ = lean_array_push(v___x_3010_, v___x_2965_);
v___x_3012_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3008_);
lean_ctor_set(v___x_3012_, 1, v___x_2995_);
lean_ctor_set(v___x_3012_, 2, v___x_3011_);
v___x_3013_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3013_, 0, v_fvarId_3001_);
lean_ctor_set(v___x_3013_, 1, v_binderName_3002_);
lean_ctor_set(v___x_3013_, 2, v___x_2996_);
lean_ctor_set(v___x_3013_, 3, v___x_3012_);
lean_inc_ref(v___x_3013_);
v___x_3014_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2992_, v_lctx_3003_, v___x_3013_);
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 0, v___x_3014_);
v___x_3016_ = v___x_3006_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3014_);
lean_ctor_set(v_reuseFailAlloc_3034_, 1, v_nextIdx_3004_);
v___x_3016_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = lean_st_ref_set(v___y_2971_, v___x_3016_);
v___x_3018_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2988_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3024_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
v___x_3020_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__27));
v___x_3021_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__20___closed__0));
v___x_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3013_);
lean_ctor_set(v___x_3022_, 1, v_a_3019_);
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 2, v___x_3022_);
lean_ctor_set(v___x_2990_, 1, v___x_3021_);
lean_ctor_set(v___x_2990_, 0, v___x_3020_);
v___x_3024_ = v___x_2990_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3020_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v___x_3021_);
lean_ctor_set(v_reuseFailAlloc_3025_, 2, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
v_a_2981_ = v___x_3024_;
goto v___jp_2980_;
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec_ref_known(v___x_3013_, 4);
lean_del_object(v___x_2990_);
lean_dec_ref(v_bs_x27_2979_);
lean_dec(v___x_2965_);
v_a_3026_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3018_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3018_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
}
}
else
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__5));
v___x_3037_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___closed__3));
v___x_3038_ = lean_unsigned_to_nat(1u);
v___x_3039_ = lean_mk_empty_array_with_capacity(v___x_3038_);
lean_inc(v___x_2965_);
v___x_3040_ = lean_array_push(v___x_3039_, v___x_2965_);
v___x_3041_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3037_);
lean_ctor_set(v___x_3041_, 1, v___x_2995_);
lean_ctor_set(v___x_3041_, 2, v___x_3040_);
v___x_3042_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2992_, v___x_3036_, v___x_2996_, v___x_3041_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref_known(v___x_3042_, 1);
v___x_3044_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__1));
v___x_3045_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__3));
v___x_3046_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2992_, v___x_3044_, v___x_2996_, v___x_3045_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; lean_object* v_fvarId_3048_; lean_object* v_fvarId_3049_; lean_object* v___x_3050_; lean_object* v_fvarId_3051_; lean_object* v_binderName_3052_; lean_object* v_lctx_3053_; lean_object* v_nextIdx_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3090_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3047_);
lean_dec_ref_known(v___x_3046_, 1);
v_fvarId_3048_ = lean_ctor_get(v_a_3043_, 0);
v_fvarId_3049_ = lean_ctor_get(v_a_3047_, 0);
v___x_3050_ = lean_st_ref_take(v___y_2971_);
v_fvarId_3051_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_fvarId_3051_);
v_binderName_3052_ = lean_ctor_get(v___x_2997_, 1);
lean_inc(v_binderName_3052_);
lean_dec(v___x_2997_);
v_lctx_3053_ = lean_ctor_get(v___x_3050_, 0);
v_nextIdx_3054_ = lean_ctor_get(v___x_3050_, 1);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3056_ = v___x_3050_;
v_isShared_3057_ = v_isSharedCheck_3090_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_nextIdx_3054_);
lean_inc(v_lctx_3053_);
lean_dec(v___x_3050_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3090_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3069_; 
v___x_3058_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__5));
lean_inc(v_fvarId_3048_);
v___x_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3059_, 0, v_fvarId_3048_);
lean_inc(v_fvarId_3049_);
v___x_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3060_, 0, v_fvarId_3049_);
v___x_3061_ = lean_unsigned_to_nat(2u);
v___x_3062_ = lean_mk_empty_array_with_capacity(v___x_3061_);
v___x_3063_ = lean_array_push(v___x_3062_, v___x_3059_);
v___x_3064_ = lean_array_push(v___x_3063_, v___x_3060_);
v___x_3065_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3058_);
lean_ctor_set(v___x_3065_, 1, v___x_2995_);
lean_ctor_set(v___x_3065_, 2, v___x_3064_);
v___x_3066_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3066_, 0, v_fvarId_3051_);
lean_ctor_set(v___x_3066_, 1, v_binderName_3052_);
lean_ctor_set(v___x_3066_, 2, v___x_2996_);
lean_ctor_set(v___x_3066_, 3, v___x_3065_);
lean_inc_ref(v___x_3066_);
v___x_3067_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2992_, v_lctx_3053_, v___x_3066_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 0, v___x_3067_);
v___x_3069_ = v___x_3056_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3067_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v_nextIdx_3054_);
v___x_3069_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = lean_st_ref_set(v___y_2971_, v___x_3069_);
v___x_3071_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2988_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3079_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_a_3072_);
lean_dec_ref_known(v___x_3071_, 1);
v___x_3073_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_3074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__20___closed__0));
v___x_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3066_);
lean_ctor_set(v___x_3075_, 1, v_a_3072_);
v___x_3076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3076_, 0, v_a_3047_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
v___x_3077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3077_, 0, v_a_3043_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 2, v___x_3077_);
lean_ctor_set(v___x_2990_, 1, v___x_3074_);
lean_ctor_set(v___x_2990_, 0, v___x_3073_);
v___x_3079_ = v___x_2990_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3073_);
lean_ctor_set(v_reuseFailAlloc_3080_, 1, v___x_3074_);
lean_ctor_set(v_reuseFailAlloc_3080_, 2, v___x_3077_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
v_a_2981_ = v___x_3079_;
goto v___jp_2980_;
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec_ref_known(v___x_3066_, 4);
lean_dec(v_a_3047_);
lean_dec(v_a_3043_);
lean_del_object(v___x_2990_);
lean_dec_ref(v_bs_x27_2979_);
lean_dec(v___x_2965_);
v_a_3081_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3071_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3071_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
}
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec(v_a_3043_);
lean_dec(v___x_2997_);
lean_del_object(v___x_2990_);
lean_dec_ref(v_code_2988_);
lean_dec_ref(v_bs_x27_2979_);
lean_dec(v___x_2965_);
v_a_3091_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3046_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3046_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_dec(v___x_2997_);
lean_del_object(v___x_2990_);
lean_dec_ref(v_code_2988_);
lean_dec_ref(v_bs_x27_2979_);
lean_dec(v___x_2965_);
v_a_3099_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3042_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3042_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_del_object(v___x_2990_);
lean_dec_ref(v_code_2988_);
lean_dec_ref(v_params_2987_);
lean_dec(v_ctorName_2986_);
lean_dec_ref(v_bs_x27_2979_);
lean_dec(v___x_2965_);
v_a_3107_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_2994_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_2994_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
}
}
else
{
lean_object* v_code_3116_; lean_object* v___x_3117_; 
v_code_3116_ = lean_ctor_get(v_v_2977_, 0);
lean_inc_ref(v_code_3116_);
v___x_3117_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3116_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v___x_3119_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3118_);
lean_dec_ref_known(v___x_3117_, 1);
v___x_3119_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_2977_, v_a_3118_);
v_a_2981_ = v___x_3119_;
goto v___jp_2980_;
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec_ref_known(v_v_2977_, 1);
lean_dec_ref(v_bs_x27_2979_);
lean_dec(v___x_2965_);
v_a_3120_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3117_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3117_);
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
v___jp_2980_:
{
size_t v___x_2982_; size_t v___x_2983_; lean_object* v___x_2984_; 
v___x_2982_ = ((size_t)1ULL);
v___x_2983_ = lean_usize_add(v_i_2967_, v___x_2982_);
v___x_2984_ = lean_array_uset(v_bs_x27_2979_, v_i_2967_, v_a_2981_);
v_i_2967_ = v___x_2983_;
v_bs_2968_ = v___x_2984_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg(lean_object* v_c_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_){
_start:
{
lean_object* v_resultType_3135_; lean_object* v_discr_3136_; lean_object* v_alts_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3234_; 
v_resultType_3135_ = lean_ctor_get(v_c_3128_, 1);
v_discr_3136_ = lean_ctor_get(v_c_3128_, 2);
v_alts_3137_ = lean_ctor_get(v_c_3128_, 3);
v_isSharedCheck_3234_ = !lean_is_exclusive(v_c_3128_);
if (v_isSharedCheck_3234_ == 0)
{
lean_object* v_unused_3235_; 
v_unused_3235_ = lean_ctor_get(v_c_3128_, 0);
lean_dec(v_unused_3235_);
v___x_3139_ = v_c_3128_;
v_isShared_3140_ = v_isSharedCheck_3234_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_alts_3137_);
lean_inc(v_discr_3136_);
lean_inc(v_resultType_3135_);
lean_dec(v_c_3128_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3234_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3141_; 
v___x_3141_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3135_, v_a_3132_, v_a_3133_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; uint8_t v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_a_3142_);
lean_dec_ref_known(v___x_3141_, 1);
v___x_3143_ = 0;
v___x_3144_ = lean_box(0);
v___x_3145_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3146_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__1));
v___x_3147_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__24));
v___x_3148_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3143_, v___x_3146_, v___x_3145_, v___x_3147_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v_a_3149_; lean_object* v_fvarId_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc(v_a_3149_);
lean_dec_ref_known(v___x_3148_, 1);
v_fvarId_3150_ = lean_ctor_get(v_a_3149_, 0);
v___x_3151_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__5));
v___x_3152_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6, &l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6);
v___x_3153_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__8));
lean_inc(v_fvarId_3150_);
v___x_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3154_, 0, v_fvarId_3150_);
v___x_3155_ = lean_unsigned_to_nat(1u);
v___x_3156_ = lean_mk_empty_array_with_capacity(v___x_3155_);
v___x_3157_ = lean_array_push(v___x_3156_, v___x_3154_);
v___x_3158_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3153_);
lean_ctor_set(v___x_3158_, 1, v___x_3144_);
lean_ctor_set(v___x_3158_, 2, v___x_3157_);
v___x_3159_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3143_, v___x_3151_, v___x_3152_, v___x_3158_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v_fvarId_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref_known(v___x_3159_, 1);
v_fvarId_3161_ = lean_ctor_get(v_a_3160_, 0);
v___x_3162_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__10));
v___x_3163_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
v___x_3164_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5);
v___x_3165_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12));
v___x_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3166_, 0, v_discr_3136_);
lean_inc(v_fvarId_3161_);
v___x_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3167_, 0, v_fvarId_3161_);
v___x_3168_ = lean_unsigned_to_nat(2u);
v___x_3169_ = lean_mk_empty_array_with_capacity(v___x_3168_);
lean_inc_ref(v___x_3166_);
v___x_3170_ = lean_array_push(v___x_3169_, v___x_3166_);
v___x_3171_ = lean_array_push(v___x_3170_, v___x_3167_);
v___x_3172_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3165_);
lean_ctor_set(v___x_3172_, 1, v___x_3144_);
lean_ctor_set(v___x_3172_, 2, v___x_3171_);
v___x_3173_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3143_, v___x_3162_, v___x_3164_, v___x_3172_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v_a_3174_; size_t v_sz_3175_; size_t v___x_3176_; lean_object* v___x_3177_; 
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
lean_inc(v_a_3174_);
lean_dec_ref_known(v___x_3173_, 1);
v_sz_3175_ = lean_array_size(v_alts_3137_);
v___x_3176_ = ((size_t)0ULL);
v___x_3177_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16(v___x_3166_, v_sz_3175_, v___x_3176_, v_alts_3137_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3193_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3180_ = v___x_3177_;
v_isShared_3181_ = v_isSharedCheck_3193_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3177_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3193_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v_fvarId_3182_; lean_object* v___x_3184_; 
v_fvarId_3182_ = lean_ctor_get(v_a_3174_, 0);
lean_inc(v_fvarId_3182_);
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 3, v_a_3178_);
lean_ctor_set(v___x_3139_, 2, v_fvarId_3182_);
lean_ctor_set(v___x_3139_, 1, v_a_3142_);
lean_ctor_set(v___x_3139_, 0, v___x_3163_);
v___x_3184_ = v___x_3139_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3163_);
lean_ctor_set(v_reuseFailAlloc_3192_, 1, v_a_3142_);
lean_ctor_set(v_reuseFailAlloc_3192_, 2, v_fvarId_3182_);
lean_ctor_set(v_reuseFailAlloc_3192_, 3, v_a_3178_);
v___x_3184_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3190_; 
v___x_3185_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3184_);
v___x_3186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3186_, 0, v_a_3174_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
v___x_3187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3187_, 0, v_a_3160_);
lean_ctor_set(v___x_3187_, 1, v___x_3186_);
v___x_3188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3188_, 0, v_a_3149_);
lean_ctor_set(v___x_3188_, 1, v___x_3187_);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 0, v___x_3188_);
v___x_3190_ = v___x_3180_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3188_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_dec(v_a_3174_);
lean_dec(v_a_3160_);
lean_dec(v_a_3149_);
lean_dec(v_a_3142_);
lean_del_object(v___x_3139_);
v_a_3194_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3177_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3177_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec_ref_known(v___x_3166_, 1);
lean_dec(v_a_3160_);
lean_dec(v_a_3149_);
lean_dec(v_a_3142_);
lean_del_object(v___x_3139_);
lean_dec_ref(v_alts_3137_);
v_a_3202_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3173_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3173_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
lean_dec(v_a_3149_);
lean_dec(v_a_3142_);
lean_del_object(v___x_3139_);
lean_dec_ref(v_alts_3137_);
lean_dec(v_discr_3136_);
v_a_3210_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___x_3159_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3159_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
lean_dec(v_a_3142_);
lean_del_object(v___x_3139_);
lean_dec_ref(v_alts_3137_);
lean_dec(v_discr_3136_);
v_a_3218_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3148_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3148_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_del_object(v___x_3139_);
lean_dec_ref(v_alts_3137_);
lean_dec(v_discr_3136_);
v_a_3226_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3141_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3141_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18(lean_object* v___x_3245_, size_t v_sz_3246_, size_t v_i_3247_, lean_object* v_bs_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
uint8_t v___x_3255_; 
v___x_3255_ = lean_usize_dec_lt(v_i_3247_, v_sz_3246_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; 
lean_dec(v___x_3245_);
v___x_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3256_, 0, v_bs_3248_);
return v___x_3256_;
}
else
{
lean_object* v_v_3257_; lean_object* v___x_3258_; lean_object* v_bs_x27_3259_; lean_object* v_a_3261_; 
v_v_3257_ = lean_array_uget(v_bs_3248_, v_i_3247_);
v___x_3258_ = lean_unsigned_to_nat(0u);
v_bs_x27_3259_ = lean_array_uset(v_bs_3248_, v_i_3247_, v___x_3258_);
if (lean_obj_tag(v_v_3257_) == 0)
{
lean_object* v_ctorName_3266_; lean_object* v_params_3267_; lean_object* v_code_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3355_; 
v_ctorName_3266_ = lean_ctor_get(v_v_3257_, 0);
v_params_3267_ = lean_ctor_get(v_v_3257_, 1);
v_code_3268_ = lean_ctor_get(v_v_3257_, 2);
v_isSharedCheck_3355_ = !lean_is_exclusive(v_v_3257_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3270_ = v_v_3257_;
v_isShared_3271_ = v_isSharedCheck_3355_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_code_3268_);
lean_inc(v_params_3267_);
lean_inc(v_ctorName_3266_);
lean_dec(v_v_3257_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3355_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
uint8_t v___x_3272_; lean_object* v___x_3273_; 
v___x_3272_ = 0;
v___x_3273_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3272_, v_params_3267_, v___y_3251_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v___x_3274_; uint8_t v___x_3275_; 
lean_dec_ref_known(v___x_3273_, 1);
v___x_3274_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__18));
v___x_3275_ = lean_name_eq(v_ctorName_3266_, v___x_3274_);
lean_dec(v_ctorName_3266_);
if (v___x_3275_ == 0)
{
lean_object* v___x_3276_; 
lean_dec_ref(v_params_3267_);
v___x_3276_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3268_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3281_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3277_);
lean_dec_ref_known(v___x_3276_, 1);
v___x_3278_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_3279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__20___closed__0));
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 2, v_a_3277_);
lean_ctor_set(v___x_3270_, 1, v___x_3279_);
lean_ctor_set(v___x_3270_, 0, v___x_3278_);
v___x_3281_ = v___x_3270_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3278_);
lean_ctor_set(v_reuseFailAlloc_3282_, 1, v___x_3279_);
lean_ctor_set(v_reuseFailAlloc_3282_, 2, v_a_3277_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
v_a_3261_ = v___x_3281_;
goto v___jp_3260_;
}
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_del_object(v___x_3270_);
lean_dec_ref(v_bs_x27_3259_);
lean_dec(v___x_3245_);
v_a_3283_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3276_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3276_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
else
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3291_ = lean_box(0);
v___x_3292_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3293_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_3294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__1));
v___x_3295_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__3));
v___x_3296_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3272_, v___x_3294_, v___x_3292_, v___x_3295_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v_fvarId_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v_fvarId_3301_; lean_object* v_binderName_3302_; lean_object* v_lctx_3303_; lean_object* v_nextIdx_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3338_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref_known(v___x_3296_, 1);
v_fvarId_3298_ = lean_ctor_get(v_a_3297_, 0);
v___x_3299_ = lean_st_ref_take(v___y_3251_);
v___x_3300_ = lean_array_get(v___x_3293_, v_params_3267_, v___x_3258_);
lean_dec_ref(v_params_3267_);
v_fvarId_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc(v_fvarId_3301_);
v_binderName_3302_ = lean_ctor_get(v___x_3300_, 1);
lean_inc(v_binderName_3302_);
lean_dec(v___x_3300_);
v_lctx_3303_ = lean_ctor_get(v___x_3299_, 0);
v_nextIdx_3304_ = lean_ctor_get(v___x_3299_, 1);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3306_ = v___x_3299_;
v_isShared_3307_ = v_isSharedCheck_3338_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_nextIdx_3304_);
lean_inc(v_lctx_3303_);
lean_dec(v___x_3299_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3338_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3318_; 
v___x_3308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__5));
lean_inc(v_fvarId_3298_);
v___x_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3309_, 0, v_fvarId_3298_);
v___x_3310_ = lean_unsigned_to_nat(2u);
v___x_3311_ = lean_mk_empty_array_with_capacity(v___x_3310_);
lean_inc(v___x_3245_);
v___x_3312_ = lean_array_push(v___x_3311_, v___x_3245_);
v___x_3313_ = lean_array_push(v___x_3312_, v___x_3309_);
v___x_3314_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3308_);
lean_ctor_set(v___x_3314_, 1, v___x_3291_);
lean_ctor_set(v___x_3314_, 2, v___x_3313_);
v___x_3315_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3315_, 0, v_fvarId_3301_);
lean_ctor_set(v___x_3315_, 1, v_binderName_3302_);
lean_ctor_set(v___x_3315_, 2, v___x_3292_);
lean_ctor_set(v___x_3315_, 3, v___x_3314_);
lean_inc_ref(v___x_3315_);
v___x_3316_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3272_, v_lctx_3303_, v___x_3315_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 0, v___x_3316_);
v___x_3318_ = v___x_3306_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3316_);
lean_ctor_set(v_reuseFailAlloc_3337_, 1, v_nextIdx_3304_);
v___x_3318_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3319_ = lean_st_ref_set(v___y_3251_, v___x_3318_);
v___x_3320_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3268_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v_a_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3327_; 
v_a_3321_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_a_3321_);
lean_dec_ref_known(v___x_3320_, 1);
v___x_3322_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__27));
v___x_3323_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__20___closed__0));
v___x_3324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3315_);
lean_ctor_set(v___x_3324_, 1, v_a_3321_);
v___x_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3325_, 0, v_a_3297_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 2, v___x_3325_);
lean_ctor_set(v___x_3270_, 1, v___x_3323_);
lean_ctor_set(v___x_3270_, 0, v___x_3322_);
v___x_3327_ = v___x_3270_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3322_);
lean_ctor_set(v_reuseFailAlloc_3328_, 1, v___x_3323_);
lean_ctor_set(v_reuseFailAlloc_3328_, 2, v___x_3325_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
v_a_3261_ = v___x_3327_;
goto v___jp_3260_;
}
}
else
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
lean_dec_ref_known(v___x_3315_, 4);
lean_dec(v_a_3297_);
lean_del_object(v___x_3270_);
lean_dec_ref(v_bs_x27_3259_);
lean_dec(v___x_3245_);
v_a_3329_ = lean_ctor_get(v___x_3320_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___x_3320_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3320_);
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
else
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3346_; 
lean_del_object(v___x_3270_);
lean_dec_ref(v_code_3268_);
lean_dec_ref(v_params_3267_);
lean_dec_ref(v_bs_x27_3259_);
lean_dec(v___x_3245_);
v_a_3339_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___x_3296_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3296_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3344_; 
if (v_isShared_3342_ == 0)
{
v___x_3344_ = v___x_3341_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3339_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_del_object(v___x_3270_);
lean_dec_ref(v_code_3268_);
lean_dec_ref(v_params_3267_);
lean_dec(v_ctorName_3266_);
lean_dec_ref(v_bs_x27_3259_);
lean_dec(v___x_3245_);
v_a_3347_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3273_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3273_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
}
else
{
lean_object* v_code_3356_; lean_object* v___x_3357_; 
v_code_3356_ = lean_ctor_get(v_v_3257_, 0);
lean_inc_ref(v_code_3356_);
v___x_3357_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3356_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3359_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3358_);
lean_dec_ref_known(v___x_3357_, 1);
v___x_3359_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_3257_, v_a_3358_);
v_a_3261_ = v___x_3359_;
goto v___jp_3260_;
}
else
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3367_; 
lean_dec_ref_known(v_v_3257_, 1);
lean_dec_ref(v_bs_x27_3259_);
lean_dec(v___x_3245_);
v_a_3360_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3362_ = v___x_3357_;
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3357_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3365_; 
if (v_isShared_3363_ == 0)
{
v___x_3365_ = v___x_3362_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_a_3360_);
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
v___jp_3260_:
{
size_t v___x_3262_; size_t v___x_3263_; lean_object* v___x_3264_; 
v___x_3262_ = ((size_t)1ULL);
v___x_3263_ = lean_usize_add(v_i_3247_, v___x_3262_);
v___x_3264_ = lean_array_uset(v_bs_x27_3259_, v_i_3247_, v_a_3261_);
v_i_3247_ = v___x_3263_;
v_bs_3248_ = v___x_3264_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg(lean_object* v_c_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_){
_start:
{
lean_object* v_resultType_3375_; lean_object* v_discr_3376_; lean_object* v_alts_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3454_; 
v_resultType_3375_ = lean_ctor_get(v_c_3368_, 1);
v_discr_3376_ = lean_ctor_get(v_c_3368_, 2);
v_alts_3377_ = lean_ctor_get(v_c_3368_, 3);
v_isSharedCheck_3454_ = !lean_is_exclusive(v_c_3368_);
if (v_isSharedCheck_3454_ == 0)
{
lean_object* v_unused_3455_; 
v_unused_3455_ = lean_ctor_get(v_c_3368_, 0);
lean_dec(v_unused_3455_);
v___x_3379_ = v_c_3368_;
v_isShared_3380_ = v_isSharedCheck_3454_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_alts_3377_);
lean_inc(v_discr_3376_);
lean_inc(v_resultType_3375_);
lean_dec(v_c_3368_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3454_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3381_; 
v___x_3381_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3375_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; uint8_t v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
lean_dec_ref_known(v___x_3381_, 1);
v___x_3383_ = 0;
v___x_3384_ = lean_box(0);
v___x_3385_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3386_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__2));
v___x_3387_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__24));
v___x_3388_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3383_, v___x_3386_, v___x_3385_, v___x_3387_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v_fvarId_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref_known(v___x_3388_, 1);
v_fvarId_3390_ = lean_ctor_get(v_a_3389_, 0);
v___x_3391_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__4));
v___x_3392_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
v___x_3393_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5);
v___x_3394_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7));
v___x_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3395_, 0, v_discr_3376_);
lean_inc(v_fvarId_3390_);
v___x_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3396_, 0, v_fvarId_3390_);
v___x_3397_ = lean_unsigned_to_nat(2u);
v___x_3398_ = lean_mk_empty_array_with_capacity(v___x_3397_);
lean_inc_ref(v___x_3395_);
v___x_3399_ = lean_array_push(v___x_3398_, v___x_3395_);
v___x_3400_ = lean_array_push(v___x_3399_, v___x_3396_);
v___x_3401_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3394_);
lean_ctor_set(v___x_3401_, 1, v___x_3384_);
lean_ctor_set(v___x_3401_, 2, v___x_3400_);
v___x_3402_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3383_, v___x_3391_, v___x_3393_, v___x_3401_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_object* v_a_3403_; size_t v_sz_3404_; size_t v___x_3405_; lean_object* v___x_3406_; 
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
lean_inc(v_a_3403_);
lean_dec_ref_known(v___x_3402_, 1);
v_sz_3404_ = lean_array_size(v_alts_3377_);
v___x_3405_ = ((size_t)0ULL);
v___x_3406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18(v___x_3395_, v_sz_3404_, v___x_3405_, v_alts_3377_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3421_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3409_ = v___x_3406_;
v_isShared_3410_ = v_isSharedCheck_3421_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3406_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3421_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v_fvarId_3411_; lean_object* v___x_3413_; 
v_fvarId_3411_ = lean_ctor_get(v_a_3403_, 0);
lean_inc(v_fvarId_3411_);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 3, v_a_3407_);
lean_ctor_set(v___x_3379_, 2, v_fvarId_3411_);
lean_ctor_set(v___x_3379_, 1, v_a_3382_);
lean_ctor_set(v___x_3379_, 0, v___x_3392_);
v___x_3413_ = v___x_3379_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3392_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v_a_3382_);
lean_ctor_set(v_reuseFailAlloc_3420_, 2, v_fvarId_3411_);
lean_ctor_set(v_reuseFailAlloc_3420_, 3, v_a_3407_);
v___x_3413_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3418_; 
v___x_3414_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
v___x_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3415_, 0, v_a_3403_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
v___x_3416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3416_, 0, v_a_3389_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v___x_3416_);
v___x_3418_ = v___x_3409_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3416_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
else
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3429_; 
lean_dec(v_a_3403_);
lean_dec(v_a_3389_);
lean_dec(v_a_3382_);
lean_del_object(v___x_3379_);
v_a_3422_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___x_3406_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3406_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3427_; 
if (v_isShared_3425_ == 0)
{
v___x_3427_ = v___x_3424_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3422_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec_ref_known(v___x_3395_, 1);
lean_dec(v_a_3389_);
lean_dec(v_a_3382_);
lean_del_object(v___x_3379_);
lean_dec_ref(v_alts_3377_);
v_a_3430_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3402_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3402_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_dec(v_a_3382_);
lean_del_object(v___x_3379_);
lean_dec_ref(v_alts_3377_);
lean_dec(v_discr_3376_);
v_a_3438_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3388_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3388_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
lean_del_object(v___x_3379_);
lean_dec_ref(v_alts_3377_);
lean_dec(v_discr_3376_);
v_a_3446_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3381_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3381_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono(lean_object* v_code_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_){
_start:
{
lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3472_; lean_object* v___y_3473_; uint8_t v___y_3474_; lean_object* v___y_3479_; lean_object* v___y_3480_; uint8_t v___y_3481_; lean_object* v___y_3486_; lean_object* v___y_3487_; uint8_t v___y_3488_; lean_object* v_decl_3493_; lean_object* v_k_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; 
switch(lean_obj_tag(v_code_3456_))
{
case 0:
{
lean_object* v_decl_3539_; lean_object* v_k_3540_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v_value_3565_; 
v_decl_3539_ = lean_ctor_get(v_code_3456_, 0);
v_k_3540_ = lean_ctor_get(v_code_3456_, 1);
v_value_3565_ = lean_ctor_get(v_decl_3539_, 3);
lean_inc(v_value_3565_);
if (lean_obj_tag(v_value_3565_) == 3)
{
lean_object* v_declName_3566_; 
v_declName_3566_ = lean_ctor_get(v_value_3565_, 0);
lean_inc(v_declName_3566_);
if (lean_obj_tag(v_declName_3566_) == 1)
{
lean_object* v_pre_3567_; 
v_pre_3567_ = lean_ctor_get(v_declName_3566_, 0);
lean_inc(v_pre_3567_);
if (lean_obj_tag(v_pre_3567_) == 1)
{
lean_object* v_pre_3568_; 
v_pre_3568_ = lean_ctor_get(v_pre_3567_, 0);
if (lean_obj_tag(v_pre_3568_) == 0)
{
lean_object* v_type_3569_; lean_object* v_args_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3640_; 
v_type_3569_ = lean_ctor_get(v_decl_3539_, 2);
v_args_3570_ = lean_ctor_get(v_value_3565_, 2);
v_isSharedCheck_3640_ = !lean_is_exclusive(v_value_3565_);
if (v_isSharedCheck_3640_ == 0)
{
lean_object* v_unused_3641_; lean_object* v_unused_3642_; 
v_unused_3641_ = lean_ctor_get(v_value_3565_, 1);
lean_dec(v_unused_3641_);
v_unused_3642_ = lean_ctor_get(v_value_3565_, 0);
lean_dec(v_unused_3642_);
v___x_3572_ = v_value_3565_;
v_isShared_3573_ = v_isSharedCheck_3640_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_args_3570_);
lean_dec(v_value_3565_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3640_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v_str_3574_; lean_object* v_str_3575_; lean_object* v___x_3576_; uint8_t v___x_3577_; 
v_str_3574_ = lean_ctor_get(v_declName_3566_, 1);
lean_inc_ref(v_str_3574_);
lean_dec_ref_known(v_declName_3566_, 2);
v_str_3575_ = lean_ctor_get(v_pre_3567_, 1);
lean_inc_ref(v_str_3575_);
lean_dec_ref_known(v_pre_3567_, 2);
v___x_3576_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__14));
v___x_3577_ = lean_string_dec_eq(v_str_3575_, v___x_3576_);
lean_dec_ref(v_str_3575_);
if (v___x_3577_ == 0)
{
lean_dec_ref(v_str_3574_);
lean_del_object(v___x_3572_);
lean_dec_ref(v_args_3570_);
v___y_3542_ = v_a_3457_;
v___y_3543_ = v_a_3458_;
v___y_3544_ = v_a_3459_;
v___y_3545_ = v_a_3460_;
v___y_3546_ = v_a_3461_;
goto v___jp_3541_;
}
else
{
lean_object* v___x_3578_; uint8_t v___x_3579_; 
v___x_3578_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__17));
v___x_3579_ = lean_string_dec_eq(v_str_3574_, v___x_3578_);
lean_dec_ref(v_str_3574_);
if (v___x_3579_ == 0)
{
lean_del_object(v___x_3572_);
lean_dec_ref(v_args_3570_);
v___y_3542_ = v_a_3457_;
v___y_3543_ = v_a_3458_;
v___y_3544_ = v_a_3459_;
v___y_3545_ = v_a_3460_;
v___y_3546_ = v_a_3461_;
goto v___jp_3541_;
}
else
{
lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3637_; 
lean_inc_ref(v_type_3569_);
lean_inc_ref(v_k_3540_);
lean_inc_ref(v_decl_3539_);
v_isSharedCheck_3637_ = !lean_is_exclusive(v_code_3456_);
if (v_isSharedCheck_3637_ == 0)
{
lean_object* v_unused_3638_; lean_object* v_unused_3639_; 
v_unused_3638_ = lean_ctor_get(v_code_3456_, 1);
lean_dec(v_unused_3638_);
v_unused_3639_ = lean_ctor_get(v_code_3456_, 0);
lean_dec(v_unused_3639_);
v___x_3581_ = v_code_3456_;
v_isShared_3582_ = v_isSharedCheck_3637_;
goto v_resetjp_3580_;
}
else
{
lean_dec(v_code_3456_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3637_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; uint8_t v___x_3585_; 
v___x_3583_ = lean_array_get_size(v_args_3570_);
v___x_3584_ = lean_unsigned_to_nat(1u);
v___x_3585_ = lean_nat_dec_eq(v___x_3583_, v___x_3584_);
if (v___x_3585_ == 0)
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
lean_del_object(v___x_3581_);
lean_del_object(v___x_3572_);
lean_dec_ref(v_args_3570_);
lean_dec_ref(v_type_3569_);
lean_dec_ref(v_k_3540_);
lean_dec_ref(v_decl_3539_);
v___x_3586_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__5, &l_Lean_Compiler_LCNF_Code_toMono___closed__5_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__5);
v___x_3587_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3586_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
return v___x_3587_;
}
else
{
uint8_t v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3588_ = 0;
v___x_3589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___closed__3));
v___x_3590_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3));
v___x_3591_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_3588_, v___x_3589_, v___x_3590_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v_a_3592_; lean_object* v_fvarId_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3604_; 
v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_a_3592_);
lean_dec_ref_known(v___x_3591_, 1);
v_fvarId_3593_ = lean_ctor_get(v_a_3592_, 0);
v___x_3594_ = lean_unsigned_to_nat(0u);
v___x_3595_ = lean_array_fget(v_args_3570_, v___x_3594_);
lean_dec_ref(v_args_3570_);
v___x_3596_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__7));
v___x_3597_ = lean_box(0);
lean_inc(v_fvarId_3593_);
v___x_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3598_, 0, v_fvarId_3593_);
v___x_3599_ = lean_unsigned_to_nat(2u);
v___x_3600_ = lean_mk_empty_array_with_capacity(v___x_3599_);
v___x_3601_ = lean_array_push(v___x_3600_, v___x_3595_);
v___x_3602_ = lean_array_push(v___x_3601_, v___x_3598_);
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 2, v___x_3602_);
lean_ctor_set(v___x_3572_, 1, v___x_3597_);
lean_ctor_set(v___x_3572_, 0, v___x_3596_);
v___x_3604_ = v___x_3572_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v___x_3596_);
lean_ctor_set(v_reuseFailAlloc_3628_, 1, v___x_3597_);
lean_ctor_set(v_reuseFailAlloc_3628_, 2, v___x_3602_);
v___x_3604_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
lean_object* v___x_3605_; 
v___x_3605_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_3588_, v_decl_3539_, v_type_3569_, v___x_3604_, v_a_3459_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; lean_object* v___x_3607_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3606_);
lean_dec_ref_known(v___x_3605_, 1);
v___x_3607_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3540_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3619_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3610_ = v___x_3607_;
v_isShared_3611_ = v_isSharedCheck_3619_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3607_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3619_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 1, v_a_3608_);
lean_ctor_set(v___x_3581_, 0, v_a_3606_);
v___x_3613_ = v___x_3581_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3606_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v_a_3608_);
v___x_3613_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___x_3614_; lean_object* v___x_3616_; 
v___x_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3614_, 0, v_a_3592_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 0, v___x_3614_);
v___x_3616_ = v___x_3610_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3614_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
else
{
lean_dec(v_a_3606_);
lean_dec(v_a_3592_);
lean_del_object(v___x_3581_);
return v___x_3607_;
}
}
else
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3627_; 
lean_dec(v_a_3592_);
lean_del_object(v___x_3581_);
lean_dec_ref(v_k_3540_);
v_a_3620_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___x_3605_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3605_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3625_; 
if (v_isShared_3623_ == 0)
{
v___x_3625_ = v___x_3622_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
}
else
{
lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3636_; 
lean_del_object(v___x_3581_);
lean_del_object(v___x_3572_);
lean_dec_ref(v_args_3570_);
lean_dec_ref(v_type_3569_);
lean_dec_ref(v_k_3540_);
lean_dec_ref(v_decl_3539_);
v_a_3629_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3631_ = v___x_3591_;
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3591_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3634_; 
if (v_isShared_3632_ == 0)
{
v___x_3634_ = v___x_3631_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_a_3629_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
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
lean_dec_ref_known(v_pre_3567_, 2);
lean_dec_ref_known(v_declName_3566_, 2);
lean_dec_ref_known(v_value_3565_, 3);
v___y_3542_ = v_a_3457_;
v___y_3543_ = v_a_3458_;
v___y_3544_ = v_a_3459_;
v___y_3545_ = v_a_3460_;
v___y_3546_ = v_a_3461_;
goto v___jp_3541_;
}
}
else
{
lean_dec(v_pre_3567_);
lean_dec_ref_known(v_declName_3566_, 2);
lean_dec_ref_known(v_value_3565_, 3);
v___y_3542_ = v_a_3457_;
v___y_3543_ = v_a_3458_;
v___y_3544_ = v_a_3459_;
v___y_3545_ = v_a_3460_;
v___y_3546_ = v_a_3461_;
goto v___jp_3541_;
}
}
else
{
lean_dec_ref_known(v_value_3565_, 3);
lean_dec(v_declName_3566_);
v___y_3542_ = v_a_3457_;
v___y_3543_ = v_a_3458_;
v___y_3544_ = v_a_3459_;
v___y_3545_ = v_a_3460_;
v___y_3546_ = v_a_3461_;
goto v___jp_3541_;
}
}
else
{
lean_dec(v_value_3565_);
v___y_3542_ = v_a_3457_;
v___y_3543_ = v_a_3458_;
v___y_3544_ = v_a_3459_;
v___y_3545_ = v_a_3460_;
v___y_3546_ = v_a_3461_;
goto v___jp_3541_;
}
v___jp_3541_:
{
lean_object* v___x_3547_; 
lean_inc_ref(v_decl_3539_);
v___x_3547_ = l_Lean_Compiler_LCNF_LetDecl_toMono(v_decl_3539_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_a_3548_; lean_object* v___x_3549_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
lean_dec_ref_known(v___x_3547_, 1);
lean_inc_ref(v_k_3540_);
v___x_3549_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3540_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_a_3550_; size_t v___x_3551_; size_t v___x_3552_; uint8_t v___x_3553_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_a_3550_);
lean_dec_ref_known(v___x_3549_, 1);
v___x_3551_ = lean_ptr_addr(v_k_3540_);
v___x_3552_ = lean_ptr_addr(v_a_3550_);
v___x_3553_ = lean_usize_dec_eq(v___x_3551_, v___x_3552_);
if (v___x_3553_ == 0)
{
v___y_3472_ = v_a_3550_;
v___y_3473_ = v_a_3548_;
v___y_3474_ = v___x_3553_;
goto v___jp_3471_;
}
else
{
size_t v___x_3554_; size_t v___x_3555_; uint8_t v___x_3556_; 
v___x_3554_ = lean_ptr_addr(v_decl_3539_);
v___x_3555_ = lean_ptr_addr(v_a_3548_);
v___x_3556_ = lean_usize_dec_eq(v___x_3554_, v___x_3555_);
v___y_3472_ = v_a_3550_;
v___y_3473_ = v_a_3548_;
v___y_3474_ = v___x_3556_;
goto v___jp_3471_;
}
}
else
{
lean_dec(v_a_3548_);
lean_dec_ref_known(v_code_3456_, 2);
return v___x_3549_;
}
}
else
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3564_; 
lean_dec_ref_known(v_code_3456_, 2);
v_a_3557_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3559_ = v___x_3547_;
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3547_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3557_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_3643_; lean_object* v_args_3644_; size_t v_sz_3645_; size_t v___x_3646_; lean_object* v___x_3647_; 
v_fvarId_3643_ = lean_ctor_get(v_code_3456_, 0);
v_args_3644_ = lean_ctor_get(v_code_3456_, 1);
v_sz_3645_ = lean_array_size(v_args_3644_);
v___x_3646_ = ((size_t)0ULL);
lean_inc_ref(v_args_3644_);
v___x_3647_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_3645_, v___x_3646_, v_args_3644_, v_a_3457_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3673_; 
v_a_3648_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3650_ = v___x_3647_;
v_isShared_3651_ = v_isSharedCheck_3673_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3647_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3673_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
uint8_t v___y_3653_; uint8_t v___x_3669_; 
v___x_3669_ = l_Lean_instBEqFVarId_beq(v_fvarId_3643_, v_fvarId_3643_);
if (v___x_3669_ == 0)
{
v___y_3653_ = v___x_3669_;
goto v___jp_3652_;
}
else
{
size_t v___x_3670_; size_t v___x_3671_; uint8_t v___x_3672_; 
v___x_3670_ = lean_ptr_addr(v_args_3644_);
v___x_3671_ = lean_ptr_addr(v_a_3648_);
v___x_3672_ = lean_usize_dec_eq(v___x_3670_, v___x_3671_);
v___y_3653_ = v___x_3672_;
goto v___jp_3652_;
}
v___jp_3652_:
{
if (v___y_3653_ == 0)
{
lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3663_; 
lean_inc(v_fvarId_3643_);
v_isSharedCheck_3663_ = !lean_is_exclusive(v_code_3456_);
if (v_isSharedCheck_3663_ == 0)
{
lean_object* v_unused_3664_; lean_object* v_unused_3665_; 
v_unused_3664_ = lean_ctor_get(v_code_3456_, 1);
lean_dec(v_unused_3664_);
v_unused_3665_ = lean_ctor_get(v_code_3456_, 0);
lean_dec(v_unused_3665_);
v___x_3655_ = v_code_3456_;
v_isShared_3656_ = v_isSharedCheck_3663_;
goto v_resetjp_3654_;
}
else
{
lean_dec(v_code_3456_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3663_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3658_; 
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 1, v_a_3648_);
v___x_3658_ = v___x_3655_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_fvarId_3643_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_a_3648_);
v___x_3658_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3660_; 
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 0, v___x_3658_);
v___x_3660_ = v___x_3650_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3658_);
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
else
{
lean_object* v___x_3667_; 
lean_dec(v_a_3648_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 0, v_code_3456_);
v___x_3667_ = v___x_3650_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_code_3456_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
}
}
else
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
lean_dec_ref_known(v_code_3456_, 2);
v_a_3674_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3647_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3647_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
case 4:
{
lean_object* v_cases_3682_; lean_object* v_typeName_3683_; lean_object* v_resultType_3684_; lean_object* v_discr_3685_; lean_object* v_alts_3686_; lean_object* v___x_3687_; uint8_t v___x_3688_; 
v_cases_3682_ = lean_ctor_get(v_code_3456_, 0);
lean_inc_ref(v_cases_3682_);
v_typeName_3683_ = lean_ctor_get(v_cases_3682_, 0);
v_resultType_3684_ = lean_ctor_get(v_cases_3682_, 1);
v_discr_3685_ = lean_ctor_get(v_cases_3682_, 2);
v_alts_3686_ = lean_ctor_get(v_cases_3682_, 3);
v___x_3687_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__8));
v___x_3688_ = lean_name_eq(v_typeName_3683_, v___x_3687_);
if (v___x_3688_ == 0)
{
lean_object* v___x_3689_; uint8_t v___x_3690_; 
v___x_3689_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0));
v___x_3690_ = lean_name_eq(v_typeName_3683_, v___x_3689_);
if (v___x_3690_ == 0)
{
lean_object* v___x_3691_; uint8_t v___x_3692_; 
v___x_3691_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3));
v___x_3692_ = lean_name_eq(v_typeName_3683_, v___x_3691_);
if (v___x_3692_ == 0)
{
lean_object* v___x_3693_; uint8_t v___x_3694_; 
v___x_3693_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__10));
v___x_3694_ = lean_name_eq(v_typeName_3683_, v___x_3693_);
if (v___x_3694_ == 0)
{
lean_object* v___x_3695_; uint8_t v___x_3696_; 
v___x_3695_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__12));
v___x_3696_ = lean_name_eq(v_typeName_3683_, v___x_3695_);
if (v___x_3696_ == 0)
{
lean_object* v___x_3697_; uint8_t v___x_3698_; 
v___x_3697_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__14));
v___x_3698_ = lean_name_eq(v_typeName_3683_, v___x_3697_);
if (v___x_3698_ == 0)
{
lean_object* v___x_3699_; uint8_t v___x_3700_; 
v___x_3699_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__16));
v___x_3700_ = lean_name_eq(v_typeName_3683_, v___x_3699_);
if (v___x_3700_ == 0)
{
lean_object* v___x_3701_; uint8_t v___x_3702_; 
v___x_3701_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__17));
v___x_3702_ = lean_name_eq(v_typeName_3683_, v___x_3701_);
if (v___x_3702_ == 0)
{
lean_object* v___x_3703_; uint8_t v___x_3704_; 
v___x_3703_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__18));
v___x_3704_ = lean_name_eq(v_typeName_3683_, v___x_3703_);
if (v___x_3704_ == 0)
{
lean_object* v___x_3705_; uint8_t v___x_3706_; 
v___x_3705_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__19));
v___x_3706_ = lean_name_eq(v_typeName_3683_, v___x_3705_);
if (v___x_3706_ == 0)
{
lean_object* v___x_3707_; uint8_t v___x_3708_; 
v___x_3707_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__20));
v___x_3708_ = lean_name_eq(v_typeName_3683_, v___x_3707_);
if (v___x_3708_ == 0)
{
lean_object* v___x_3709_; uint8_t v___x_3710_; 
v___x_3709_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__21));
v___x_3710_ = lean_name_eq(v_typeName_3683_, v___x_3709_);
if (v___x_3710_ == 0)
{
lean_object* v___x_3711_; uint8_t v___x_3712_; 
v___x_3711_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__22));
v___x_3712_ = lean_name_eq(v_typeName_3683_, v___x_3711_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3713_; 
lean_inc(v_typeName_3683_);
v___x_3713_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_typeName_3683_, v_a_3460_, v_a_3461_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_a_3714_);
lean_dec_ref_known(v___x_3713_, 1);
if (lean_obj_tag(v_a_3714_) == 1)
{
lean_object* v_val_3715_; lean_object* v___x_3716_; 
lean_dec_ref_known(v_code_3456_, 1);
v_val_3715_ = lean_ctor_get(v_a_3714_, 0);
lean_inc(v_val_3715_);
lean_dec_ref_known(v_a_3714_, 1);
v___x_3716_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_val_3715_, v_cases_3682_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
lean_dec(v_val_3715_);
return v___x_3716_;
}
else
{
lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3809_; 
lean_inc_ref(v_alts_3686_);
lean_inc(v_discr_3685_);
lean_inc_ref(v_resultType_3684_);
lean_inc(v_typeName_3683_);
lean_dec(v_a_3714_);
v_isSharedCheck_3809_ = !lean_is_exclusive(v_cases_3682_);
if (v_isSharedCheck_3809_ == 0)
{
lean_object* v_unused_3810_; lean_object* v_unused_3811_; lean_object* v_unused_3812_; lean_object* v_unused_3813_; 
v_unused_3810_ = lean_ctor_get(v_cases_3682_, 3);
lean_dec(v_unused_3810_);
v_unused_3811_ = lean_ctor_get(v_cases_3682_, 2);
lean_dec(v_unused_3811_);
v_unused_3812_ = lean_ctor_get(v_cases_3682_, 1);
lean_dec(v_unused_3812_);
v_unused_3813_ = lean_ctor_get(v_cases_3682_, 0);
lean_dec(v_unused_3813_);
v___x_3718_ = v_cases_3682_;
v_isShared_3719_ = v_isSharedCheck_3809_;
goto v_resetjp_3717_;
}
else
{
lean_dec(v_cases_3682_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3809_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3720_; 
lean_inc_ref(v_resultType_3684_);
v___x_3720_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3684_, v_a_3460_, v_a_3461_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3800_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3723_ = v___x_3720_;
v_isShared_3724_ = v_isSharedCheck_3800_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3720_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3800_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3725_; lean_object* v_env_3726_; lean_object* v___x_3753_; 
v___x_3725_ = lean_st_ref_get(v_a_3461_);
v_env_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc_ref_n(v_env_3726_, 2);
lean_dec(v___x_3725_);
lean_inc(v_typeName_3683_);
v___x_3753_ = l_Lean_Environment_find_x3f(v_env_3726_, v_typeName_3683_, v___x_3712_);
if (lean_obj_tag(v___x_3753_) == 1)
{
lean_object* v_val_3754_; 
v_val_3754_ = lean_ctor_get(v___x_3753_, 0);
lean_inc(v_val_3754_);
lean_dec_ref_known(v___x_3753_, 1);
if (lean_obj_tag(v_val_3754_) == 5)
{
lean_object* v_val_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3799_; 
v_val_3755_ = lean_ctor_get(v_val_3754_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v_val_3754_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3757_ = v_val_3754_;
v_isShared_3758_ = v_isSharedCheck_3799_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_val_3755_);
lean_dec(v_val_3754_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3799_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v_toConstantVal_3759_; lean_object* v_name_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v_toConstantVal_3759_ = lean_ctor_get(v_val_3755_, 0);
lean_inc_ref(v_toConstantVal_3759_);
lean_dec_ref(v_val_3755_);
v_name_3760_ = lean_ctor_get(v_toConstantVal_3759_, 0);
lean_inc(v_name_3760_);
lean_dec_ref(v_toConstantVal_3759_);
v___x_3761_ = l_Lean_mkCasesOnName(v_name_3760_);
lean_inc_ref(v_env_3726_);
v___x_3762_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_3726_, v___x_3761_);
if (lean_obj_tag(v___x_3762_) == 0)
{
if (v___x_3712_ == 0)
{
size_t v_sz_3763_; size_t v___x_3764_; lean_object* v___x_3765_; 
lean_dec_ref(v_env_3726_);
lean_del_object(v___x_3718_);
v_sz_3763_ = lean_array_size(v_alts_3686_);
v___x_3764_ = ((size_t)0ULL);
lean_inc_ref(v_alts_3686_);
v___x_3765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v_sz_3763_, v___x_3764_, v_alts_3686_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3790_; 
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3768_ = v___x_3765_;
v_isShared_3769_ = v_isSharedCheck_3790_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3765_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3790_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
uint8_t v___y_3779_; size_t v___x_3784_; size_t v___x_3785_; uint8_t v___x_3786_; 
v___x_3784_ = lean_ptr_addr(v_alts_3686_);
lean_dec_ref(v_alts_3686_);
v___x_3785_ = lean_ptr_addr(v_a_3766_);
v___x_3786_ = lean_usize_dec_eq(v___x_3784_, v___x_3785_);
if (v___x_3786_ == 0)
{
lean_dec_ref(v_resultType_3684_);
v___y_3779_ = v___x_3786_;
goto v___jp_3778_;
}
else
{
size_t v___x_3787_; size_t v___x_3788_; uint8_t v___x_3789_; 
v___x_3787_ = lean_ptr_addr(v_resultType_3684_);
lean_dec_ref(v_resultType_3684_);
v___x_3788_ = lean_ptr_addr(v_a_3721_);
v___x_3789_ = lean_usize_dec_eq(v___x_3787_, v___x_3788_);
v___y_3779_ = v___x_3789_;
goto v___jp_3778_;
}
v___jp_3770_:
{
lean_object* v___x_3771_; lean_object* v___x_3773_; 
v___x_3771_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3771_, 0, v_typeName_3683_);
lean_ctor_set(v___x_3771_, 1, v_a_3721_);
lean_ctor_set(v___x_3771_, 2, v_discr_3685_);
lean_ctor_set(v___x_3771_, 3, v_a_3766_);
if (v_isShared_3758_ == 0)
{
lean_ctor_set_tag(v___x_3757_, 4);
lean_ctor_set(v___x_3757_, 0, v___x_3771_);
v___x_3773_ = v___x_3757_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3771_);
v___x_3773_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
lean_object* v___x_3775_; 
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 0, v___x_3773_);
v___x_3775_ = v___x_3768_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3773_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
v___jp_3778_:
{
if (v___y_3779_ == 0)
{
lean_del_object(v___x_3723_);
lean_dec_ref_known(v_code_3456_, 1);
goto v___jp_3770_;
}
else
{
uint8_t v___x_3780_; 
v___x_3780_ = l_Lean_instBEqFVarId_beq(v_discr_3685_, v_discr_3685_);
if (v___x_3780_ == 0)
{
lean_del_object(v___x_3723_);
lean_dec_ref_known(v_code_3456_, 1);
goto v___jp_3770_;
}
else
{
lean_object* v___x_3782_; 
lean_del_object(v___x_3768_);
lean_dec(v_a_3766_);
lean_del_object(v___x_3757_);
lean_dec(v_a_3721_);
lean_dec(v_discr_3685_);
lean_dec(v_typeName_3683_);
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 0, v_code_3456_);
v___x_3782_ = v___x_3723_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_code_3456_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
}
}
else
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
lean_del_object(v___x_3757_);
lean_del_object(v___x_3723_);
lean_dec(v_a_3721_);
lean_dec_ref(v_alts_3686_);
lean_dec(v_discr_3685_);
lean_dec_ref(v_resultType_3684_);
lean_dec(v_typeName_3683_);
lean_dec_ref_known(v_code_3456_, 1);
v_a_3791_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3765_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3765_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
else
{
lean_del_object(v___x_3757_);
lean_del_object(v___x_3723_);
lean_dec_ref(v_resultType_3684_);
lean_dec_ref_known(v_code_3456_, 1);
goto v___jp_3727_;
}
}
else
{
lean_dec_ref_known(v___x_3762_, 1);
lean_del_object(v___x_3757_);
lean_del_object(v___x_3723_);
lean_dec_ref(v_resultType_3684_);
lean_dec_ref_known(v_code_3456_, 1);
goto v___jp_3727_;
}
}
}
else
{
lean_dec(v_val_3754_);
lean_dec_ref(v_env_3726_);
lean_del_object(v___x_3723_);
lean_dec(v_a_3721_);
lean_del_object(v___x_3718_);
lean_dec_ref(v_alts_3686_);
lean_dec(v_discr_3685_);
lean_dec_ref(v_resultType_3684_);
lean_dec(v_typeName_3683_);
lean_dec_ref_known(v_code_3456_, 1);
v___y_3464_ = v_a_3457_;
v___y_3465_ = v_a_3458_;
v___y_3466_ = v_a_3459_;
v___y_3467_ = v_a_3460_;
v___y_3468_ = v_a_3461_;
goto v___jp_3463_;
}
}
else
{
lean_dec(v___x_3753_);
lean_dec_ref(v_env_3726_);
lean_del_object(v___x_3723_);
lean_dec(v_a_3721_);
lean_del_object(v___x_3718_);
lean_dec_ref(v_alts_3686_);
lean_dec(v_discr_3685_);
lean_dec_ref(v_resultType_3684_);
lean_dec(v_typeName_3683_);
lean_dec_ref_known(v_code_3456_, 1);
v___y_3464_ = v_a_3457_;
v___y_3465_ = v_a_3458_;
v___y_3466_ = v_a_3459_;
v___y_3467_ = v_a_3460_;
v___y_3468_ = v_a_3461_;
goto v___jp_3463_;
}
v___jp_3727_:
{
size_t v_sz_3728_; size_t v___x_3729_; lean_object* v___x_3730_; 
v_sz_3728_ = lean_array_size(v_alts_3686_);
v___x_3729_ = ((size_t)0ULL);
v___x_3730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(v_env_3726_, v___x_3712_, v_sz_3728_, v___x_3729_, v_alts_3686_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3744_; 
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3733_ = v___x_3730_;
v_isShared_3734_ = v_isSharedCheck_3744_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3730_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3744_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3738_; 
v___x_3735_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4));
v___x_3736_ = l_Lean_Name_append(v_typeName_3683_, v___x_3735_);
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 3, v_a_3731_);
lean_ctor_set(v___x_3718_, 1, v_a_3721_);
lean_ctor_set(v___x_3718_, 0, v___x_3736_);
v___x_3738_ = v___x_3718_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3736_);
lean_ctor_set(v_reuseFailAlloc_3743_, 1, v_a_3721_);
lean_ctor_set(v_reuseFailAlloc_3743_, 2, v_discr_3685_);
lean_ctor_set(v_reuseFailAlloc_3743_, 3, v_a_3731_);
v___x_3738_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
lean_object* v___x_3739_; lean_object* v___x_3741_; 
v___x_3739_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 0, v___x_3739_);
v___x_3741_ = v___x_3733_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3739_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
else
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
lean_dec(v_a_3721_);
lean_del_object(v___x_3718_);
lean_dec(v_discr_3685_);
lean_dec(v_typeName_3683_);
v_a_3745_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3730_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3730_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
}
}
else
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
lean_del_object(v___x_3718_);
lean_dec_ref(v_alts_3686_);
lean_dec(v_discr_3685_);
lean_dec_ref(v_resultType_3684_);
lean_dec(v_typeName_3683_);
lean_dec_ref_known(v_code_3456_, 1);
v_a_3801_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3803_ = v___x_3720_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3720_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3801_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
}
}
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_dec_ref_known(v_code_3456_, 1);
lean_dec_ref(v_cases_3682_);
v_a_3814_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3713_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3713_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
else
{
lean_object* v___x_3822_; 
lean_dec_ref_known(v_code_3456_, 1);
v___x_3822_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_cases_3682_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
return v___x_3822_;
}
}
else
{
lean_object* v___x_3823_; 
lean_dec_ref_known(v_code_3456_, 1);
v___x_3823_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_cases_3682_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
lean_dec_ref(v_cases_3682_);
return v___x_3823_;
}
}
else
{
lean_object* v___x_3824_; 
lean_dec_ref_known(v_code_3456_, 1);
v___x_3824_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_cases_3682_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
return v___x_3824_;
}
}
else
{
lean_object* v___x_3825_; 
lean_dec_ref_known(v_code_3456_, 1);
v___x_3825_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_cases_3682_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
return v___x_3825_;
}
}
else
{
lean_object* v___x_3826_; 
lean_dec_ref_known(v_code_3456_, 1);
v___x_3826_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_cases_3682_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
return v___x_3826_;
}
}
else
{
lean_object* v___x_3827_; 
lean_dec_ref_known(v_code_3456_, 1);
v___x_3827_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_cases_3682_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
return v___x_3827_;
}
}
else
{
lean_object* v___x_3828_; 
lean_dec_ref_known(v_code_3456_, 1);
v___x_3828_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3682_, v___x_3699_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
return v___x_3828_;
}
}
else
{
lean_object* v___x_3829_; 
lean_dec_ref_known(v_code_3456_, 1);
v___x_3829_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3682_, v___x_3697_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
return v___x_3829_;
}
}
else
{
lean_object* v___x_3830_; 
lean_dec_ref_known(v_code_3456_, 1);
v___x_3830_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3682_, v___x_3695_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
return v___x_3830_;
}
}
else
{
lean_object* v___x_3831_; 
lean_dec_ref_known(v_code_3456_, 1);
v___x_3831_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3682_, v___x_3693_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
return v___x_3831_;
}
}
else
{
lean_object* v___x_3832_; 
lean_dec_ref_known(v_code_3456_, 1);
v___x_3832_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_cases_3682_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
return v___x_3832_;
}
}
else
{
lean_object* v___x_3833_; 
lean_dec_ref_known(v_code_3456_, 1);
v___x_3833_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_cases_3682_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
return v___x_3833_;
}
}
else
{
lean_object* v___x_3834_; 
lean_dec_ref_known(v_code_3456_, 1);
v___x_3834_ = l_Lean_Compiler_LCNF_decToMono___redArg(v_cases_3682_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
return v___x_3834_;
}
}
case 5:
{
lean_object* v___x_3835_; 
v___x_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3835_, 0, v_code_3456_);
return v___x_3835_;
}
case 6:
{
lean_object* v_type_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3860_; 
v_type_3836_ = lean_ctor_get(v_code_3456_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v_code_3456_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3838_ = v_code_3456_;
v_isShared_3839_ = v_isSharedCheck_3860_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_type_3836_);
lean_dec(v_code_3456_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3860_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3840_; 
v___x_3840_ = l_Lean_Compiler_LCNF_toMonoType(v_type_3836_, v_a_3460_, v_a_3461_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3851_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3843_ = v___x_3840_;
v_isShared_3844_ = v_isSharedCheck_3851_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3840_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3851_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 0, v_a_3841_);
v___x_3846_ = v___x_3838_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
lean_object* v___x_3848_; 
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 0, v___x_3846_);
v___x_3848_ = v___x_3843_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3846_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
lean_del_object(v___x_3838_);
v_a_3852_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3840_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3840_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
}
default: 
{
lean_object* v_decl_3861_; lean_object* v_k_3862_; 
v_decl_3861_ = lean_ctor_get(v_code_3456_, 0);
v_k_3862_ = lean_ctor_get(v_code_3456_, 1);
lean_inc_ref(v_k_3862_);
lean_inc_ref(v_decl_3861_);
v_decl_3493_ = v_decl_3861_;
v_k_3494_ = v_k_3862_;
v___y_3495_ = v_a_3457_;
v___y_3496_ = v_a_3458_;
v___y_3497_ = v_a_3459_;
v___y_3498_ = v_a_3460_;
v___y_3499_ = v_a_3461_;
goto v___jp_3492_;
}
}
v___jp_3463_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3469_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__1, &l_Lean_Compiler_LCNF_Code_toMono___closed__1_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__1);
v___x_3470_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3469_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
return v___x_3470_;
}
v___jp_3471_:
{
if (v___y_3474_ == 0)
{
lean_object* v___x_3475_; lean_object* v___x_3476_; 
lean_dec_ref(v_code_3456_);
v___x_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___y_3473_);
lean_ctor_set(v___x_3475_, 1, v___y_3472_);
v___x_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3475_);
return v___x_3476_;
}
else
{
lean_object* v___x_3477_; 
lean_dec_ref(v___y_3473_);
lean_dec_ref(v___y_3472_);
v___x_3477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3477_, 0, v_code_3456_);
return v___x_3477_;
}
}
v___jp_3478_:
{
if (v___y_3481_ == 0)
{
lean_object* v___x_3482_; lean_object* v___x_3483_; 
lean_dec_ref(v_code_3456_);
v___x_3482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___y_3480_);
lean_ctor_set(v___x_3482_, 1, v___y_3479_);
v___x_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
return v___x_3483_;
}
else
{
lean_object* v___x_3484_; 
lean_dec_ref(v___y_3480_);
lean_dec_ref(v___y_3479_);
v___x_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3484_, 0, v_code_3456_);
return v___x_3484_;
}
}
v___jp_3485_:
{
if (v___y_3488_ == 0)
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
lean_dec_ref(v_code_3456_);
v___x_3489_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3489_, 0, v___y_3487_);
lean_ctor_set(v___x_3489_, 1, v___y_3486_);
v___x_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
return v___x_3490_;
}
else
{
lean_object* v___x_3491_; 
lean_dec_ref(v___y_3487_);
lean_dec_ref(v___y_3486_);
v___x_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3491_, 0, v_code_3456_);
return v___x_3491_;
}
}
v___jp_3492_:
{
lean_object* v___x_3500_; 
v___x_3500_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_3493_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v___x_3502_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v___x_3500_, 1);
v___x_3502_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
if (lean_obj_tag(v___x_3502_) == 0)
{
switch(lean_obj_tag(v_code_3456_))
{
case 1:
{
lean_object* v_a_3503_; lean_object* v_decl_3504_; lean_object* v_k_3505_; size_t v___x_3506_; size_t v___x_3507_; uint8_t v___x_3508_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3503_);
lean_dec_ref_known(v___x_3502_, 1);
v_decl_3504_ = lean_ctor_get(v_code_3456_, 0);
v_k_3505_ = lean_ctor_get(v_code_3456_, 1);
v___x_3506_ = lean_ptr_addr(v_k_3505_);
v___x_3507_ = lean_ptr_addr(v_a_3503_);
v___x_3508_ = lean_usize_dec_eq(v___x_3506_, v___x_3507_);
if (v___x_3508_ == 0)
{
v___y_3479_ = v_a_3503_;
v___y_3480_ = v_a_3501_;
v___y_3481_ = v___x_3508_;
goto v___jp_3478_;
}
else
{
size_t v___x_3509_; size_t v___x_3510_; uint8_t v___x_3511_; 
v___x_3509_ = lean_ptr_addr(v_decl_3504_);
v___x_3510_ = lean_ptr_addr(v_a_3501_);
v___x_3511_ = lean_usize_dec_eq(v___x_3509_, v___x_3510_);
v___y_3479_ = v_a_3503_;
v___y_3480_ = v_a_3501_;
v___y_3481_ = v___x_3511_;
goto v___jp_3478_;
}
}
case 2:
{
lean_object* v_a_3512_; lean_object* v_decl_3513_; lean_object* v_k_3514_; size_t v___x_3515_; size_t v___x_3516_; uint8_t v___x_3517_; 
v_a_3512_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3512_);
lean_dec_ref_known(v___x_3502_, 1);
v_decl_3513_ = lean_ctor_get(v_code_3456_, 0);
v_k_3514_ = lean_ctor_get(v_code_3456_, 1);
v___x_3515_ = lean_ptr_addr(v_k_3514_);
v___x_3516_ = lean_ptr_addr(v_a_3512_);
v___x_3517_ = lean_usize_dec_eq(v___x_3515_, v___x_3516_);
if (v___x_3517_ == 0)
{
v___y_3486_ = v_a_3512_;
v___y_3487_ = v_a_3501_;
v___y_3488_ = v___x_3517_;
goto v___jp_3485_;
}
else
{
size_t v___x_3518_; size_t v___x_3519_; uint8_t v___x_3520_; 
v___x_3518_ = lean_ptr_addr(v_decl_3513_);
v___x_3519_ = lean_ptr_addr(v_a_3501_);
v___x_3520_ = lean_usize_dec_eq(v___x_3518_, v___x_3519_);
v___y_3486_ = v_a_3512_;
v___y_3487_ = v_a_3501_;
v___y_3488_ = v___x_3520_;
goto v___jp_3485_;
}
}
default: 
{
lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3529_; 
lean_dec(v_a_3501_);
lean_dec_ref(v_code_3456_);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3529_ == 0)
{
lean_object* v_unused_3530_; 
v_unused_3530_ = lean_ctor_get(v___x_3502_, 0);
lean_dec(v_unused_3530_);
v___x_3522_ = v___x_3502_;
v_isShared_3523_ = v_isSharedCheck_3529_;
goto v_resetjp_3521_;
}
else
{
lean_dec(v___x_3502_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3529_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3527_; 
v___x_3524_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__4, &l_Lean_Compiler_LCNF_Code_toMono___closed__4_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__4);
v___x_3525_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__2(v___x_3524_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3525_);
v___x_3527_ = v___x_3522_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
}
else
{
lean_dec(v_a_3501_);
lean_dec_ref(v_code_3456_);
return v___x_3502_;
}
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
lean_dec_ref(v_k_3494_);
lean_dec_ref(v_code_3456_);
v_a_3531_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3500_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3500_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__20(size_t v_sz_3863_, size_t v_i_3864_, lean_object* v_bs_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_){
_start:
{
uint8_t v___x_3872_; 
v___x_3872_ = lean_usize_dec_lt(v_i_3864_, v_sz_3863_);
if (v___x_3872_ == 0)
{
lean_object* v___x_3873_; 
v___x_3873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3873_, 0, v_bs_3865_);
return v___x_3873_;
}
else
{
lean_object* v_v_3874_; lean_object* v___x_3875_; lean_object* v_bs_x27_3876_; lean_object* v_a_3878_; 
v_v_3874_ = lean_array_uget(v_bs_3865_, v_i_3864_);
v___x_3875_ = lean_unsigned_to_nat(0u);
v_bs_x27_3876_ = lean_array_uset(v_bs_3865_, v_i_3864_, v___x_3875_);
if (lean_obj_tag(v_v_3874_) == 0)
{
lean_object* v_ctorName_3883_; lean_object* v_params_3884_; lean_object* v_code_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3919_; 
v_ctorName_3883_ = lean_ctor_get(v_v_3874_, 0);
v_params_3884_ = lean_ctor_get(v_v_3874_, 1);
v_code_3885_ = lean_ctor_get(v_v_3874_, 2);
v_isSharedCheck_3919_ = !lean_is_exclusive(v_v_3874_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3887_ = v_v_3874_;
v_isShared_3888_ = v_isSharedCheck_3919_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_code_3885_);
lean_inc(v_params_3884_);
lean_inc(v_ctorName_3883_);
lean_dec(v_v_3874_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3919_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
uint8_t v___x_3889_; lean_object* v___x_3890_; 
v___x_3889_ = 0;
v___x_3890_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3889_, v_params_3884_, v___y_3868_);
lean_dec_ref(v_params_3884_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v___y_3892_; lean_object* v___x_3907_; uint8_t v___x_3908_; 
lean_dec_ref_known(v___x_3890_, 1);
v___x_3907_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__4));
v___x_3908_ = lean_name_eq(v_ctorName_3883_, v___x_3907_);
lean_dec(v_ctorName_3883_);
if (v___x_3908_ == 0)
{
lean_object* v___x_3909_; 
v___x_3909_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__27));
v___y_3892_ = v___x_3909_;
goto v___jp_3891_;
}
else
{
lean_object* v___x_3910_; 
v___x_3910_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___y_3892_ = v___x_3910_;
goto v___jp_3891_;
}
v___jp_3891_:
{
lean_object* v___x_3893_; 
v___x_3893_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3885_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v___x_3895_; lean_object* v___x_3897_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_a_3894_);
lean_dec_ref_known(v___x_3893_, 1);
v___x_3895_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__20___closed__0));
lean_inc(v___y_3892_);
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 2, v_a_3894_);
lean_ctor_set(v___x_3887_, 1, v___x_3895_);
lean_ctor_set(v___x_3887_, 0, v___y_3892_);
v___x_3897_ = v___x_3887_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___y_3892_);
lean_ctor_set(v_reuseFailAlloc_3898_, 1, v___x_3895_);
lean_ctor_set(v_reuseFailAlloc_3898_, 2, v_a_3894_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
v_a_3878_ = v___x_3897_;
goto v___jp_3877_;
}
}
else
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3906_; 
lean_del_object(v___x_3887_);
lean_dec_ref(v_bs_x27_3876_);
v_a_3899_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3901_ = v___x_3893_;
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3893_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3899_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
}
else
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3918_; 
lean_del_object(v___x_3887_);
lean_dec_ref(v_code_3885_);
lean_dec(v_ctorName_3883_);
lean_dec_ref(v_bs_x27_3876_);
v_a_3911_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3913_ = v___x_3890_;
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3890_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3916_; 
if (v_isShared_3914_ == 0)
{
v___x_3916_ = v___x_3913_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
}
}
else
{
lean_object* v_code_3920_; lean_object* v___x_3921_; 
v_code_3920_ = lean_ctor_get(v_v_3874_, 0);
lean_inc_ref(v_code_3920_);
v___x_3921_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3920_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_a_3922_; lean_object* v___x_3923_; 
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_a_3922_);
lean_dec_ref_known(v___x_3921_, 1);
v___x_3923_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_3874_, v_a_3922_);
v_a_3878_ = v___x_3923_;
goto v___jp_3877_;
}
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
lean_dec_ref_known(v_v_3874_, 1);
lean_dec_ref(v_bs_x27_3876_);
v_a_3924_ = lean_ctor_get(v___x_3921_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3921_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3921_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
v___jp_3877_:
{
size_t v___x_3879_; size_t v___x_3880_; lean_object* v___x_3881_; 
v___x_3879_ = ((size_t)1ULL);
v___x_3880_ = lean_usize_add(v_i_3864_, v___x_3879_);
v___x_3881_ = lean_array_uset(v_bs_x27_3876_, v_i_3864_, v_a_3878_);
v_i_3864_ = v___x_3880_;
v_bs_3865_ = v___x_3881_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___redArg(lean_object* v_c_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_){
_start:
{
lean_object* v_resultType_3939_; lean_object* v_discr_3940_; lean_object* v_alts_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3979_; 
v_resultType_3939_ = lean_ctor_get(v_c_3932_, 1);
v_discr_3940_ = lean_ctor_get(v_c_3932_, 2);
v_alts_3941_ = lean_ctor_get(v_c_3932_, 3);
v_isSharedCheck_3979_ = !lean_is_exclusive(v_c_3932_);
if (v_isSharedCheck_3979_ == 0)
{
lean_object* v_unused_3980_; 
v_unused_3980_ = lean_ctor_get(v_c_3932_, 0);
lean_dec(v_unused_3980_);
v___x_3943_ = v_c_3932_;
v_isShared_3944_ = v_isSharedCheck_3979_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_alts_3941_);
lean_inc(v_discr_3940_);
lean_inc(v_resultType_3939_);
lean_dec(v_c_3932_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3979_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3945_; 
v___x_3945_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3939_, v_a_3936_, v_a_3937_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v_a_3946_; size_t v_sz_3947_; size_t v___x_3948_; lean_object* v___x_3949_; 
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc(v_a_3946_);
lean_dec_ref_known(v___x_3945_, 1);
v_sz_3947_ = lean_array_size(v_alts_3941_);
v___x_3948_ = ((size_t)0ULL);
v___x_3949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__20(v_sz_3947_, v___x_3948_, v_alts_3941_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_);
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_object* v_a_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3962_; 
v_a_3950_ = lean_ctor_get(v___x_3949_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3952_ = v___x_3949_;
v_isShared_3953_ = v_isSharedCheck_3962_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_a_3950_);
lean_dec(v___x_3949_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3962_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3954_; lean_object* v___x_3956_; 
v___x_3954_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
if (v_isShared_3944_ == 0)
{
lean_ctor_set(v___x_3943_, 3, v_a_3950_);
lean_ctor_set(v___x_3943_, 1, v_a_3946_);
lean_ctor_set(v___x_3943_, 0, v___x_3954_);
v___x_3956_ = v___x_3943_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v___x_3954_);
lean_ctor_set(v_reuseFailAlloc_3961_, 1, v_a_3946_);
lean_ctor_set(v_reuseFailAlloc_3961_, 2, v_discr_3940_);
lean_ctor_set(v_reuseFailAlloc_3961_, 3, v_a_3950_);
v___x_3956_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
lean_object* v___x_3957_; lean_object* v___x_3959_; 
v___x_3957_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3956_);
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 0, v___x_3957_);
v___x_3959_ = v___x_3952_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v___x_3957_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
lean_dec(v_a_3946_);
lean_del_object(v___x_3943_);
lean_dec(v_discr_3940_);
v_a_3963_ = lean_ctor_get(v___x_3949_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3949_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3949_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
else
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
lean_del_object(v___x_3943_);
lean_dec_ref(v_alts_3941_);
lean_dec(v_discr_3940_);
v_a_3971_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3945_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3945_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___redArg___boxed(lean_object* v_c_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l_Lean_Compiler_LCNF_decToMono___redArg(v_c_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_);
lean_dec(v_a_3986_);
lean_dec_ref(v_a_3985_);
lean_dec(v_a_3984_);
lean_dec_ref(v_a_3983_);
lean_dec(v_a_3982_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono___boxed(lean_object* v_decl_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_3989_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_);
lean_dec(v_a_3994_);
lean_dec_ref(v_a_3993_);
lean_dec(v_a_3992_);
lean_dec_ref(v_a_3991_);
lean_dec(v_a_3990_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___boxed(lean_object* v_sz_3997_, lean_object* v_i_3998_, lean_object* v_bs_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_){
_start:
{
size_t v_sz_boxed_4006_; size_t v_i_boxed_4007_; lean_object* v_res_4008_; 
v_sz_boxed_4006_ = lean_unbox_usize(v_sz_3997_);
lean_dec(v_sz_3997_);
v_i_boxed_4007_ = lean_unbox_usize(v_i_3998_);
lean_dec(v_i_3998_);
v_res_4008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v_sz_boxed_4006_, v_i_boxed_4007_, v_bs_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
lean_dec(v___y_4000_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__20___boxed(lean_object* v_sz_4009_, lean_object* v_i_4010_, lean_object* v_bs_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
size_t v_sz_boxed_4018_; size_t v_i_boxed_4019_; lean_object* v_res_4020_; 
v_sz_boxed_4018_ = lean_unbox_usize(v_sz_4009_);
lean_dec(v_sz_4009_);
v_i_boxed_4019_ = lean_unbox_usize(v_i_4010_);
lean_dec(v_i_4010_);
v_res_4020_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__20(v_sz_boxed_4018_, v_i_boxed_4019_, v_bs_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v___y_4012_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___boxed(lean_object* v_c_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_){
_start:
{
lean_object* v_res_4028_; 
v_res_4028_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_);
lean_dec(v_a_4026_);
lean_dec_ref(v_a_4025_);
lean_dec(v_a_4024_);
lean_dec_ref(v_a_4023_);
lean_dec(v_a_4022_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___boxed(lean_object* v_c_4029_, lean_object* v_uintName_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_){
_start:
{
lean_object* v_res_4037_; 
v_res_4037_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_4029_, v_uintName_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_);
lean_dec(v_a_4035_);
lean_dec_ref(v_a_4034_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
return v_res_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___boxed(lean_object* v_c_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
lean_dec(v_a_4043_);
lean_dec_ref(v_a_4042_);
lean_dec(v_a_4041_);
lean_dec_ref(v_a_4040_);
lean_dec(v_a_4039_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___boxed(lean_object* v_c_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_);
lean_dec(v_a_4051_);
lean_dec_ref(v_a_4050_);
lean_dec(v_a_4049_);
lean_dec_ref(v_a_4048_);
lean_dec(v_a_4047_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___boxed(lean_object* v_c_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_){
_start:
{
lean_object* v_res_4061_; 
v_res_4061_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_);
lean_dec(v_a_4059_);
lean_dec_ref(v_a_4058_);
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
lean_dec(v_a_4055_);
return v_res_4061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___boxed(lean_object* v___x_4062_, lean_object* v___x_4063_, lean_object* v_sz_4064_, lean_object* v_i_4065_, lean_object* v_bs_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
uint8_t v___x_43414__boxed_4073_; size_t v_sz_boxed_4074_; size_t v_i_boxed_4075_; lean_object* v_res_4076_; 
v___x_43414__boxed_4073_ = lean_unbox(v___x_4063_);
v_sz_boxed_4074_ = lean_unbox_usize(v_sz_4064_);
lean_dec(v_sz_4064_);
v_i_boxed_4075_ = lean_unbox_usize(v_i_4065_);
lean_dec(v_i_4065_);
v_res_4076_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(v___x_4062_, v___x_43414__boxed_4073_, v_sz_boxed_4074_, v_i_boxed_4075_, v_bs_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec(v___y_4067_);
return v_res_4076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___boxed(lean_object* v_c_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_);
lean_dec(v_a_4082_);
lean_dec_ref(v_a_4081_);
lean_dec(v_a_4080_);
lean_dec_ref(v_a_4079_);
lean_dec(v_a_4078_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___boxed(lean_object* v_c_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_4085_, v_a_4086_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_);
lean_dec(v_a_4090_);
lean_dec_ref(v_a_4089_);
lean_dec(v_a_4088_);
lean_dec_ref(v_a_4087_);
lean_dec(v_a_4086_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___boxed(lean_object* v_c_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
lean_dec(v_a_4098_);
lean_dec_ref(v_a_4097_);
lean_dec(v_a_4096_);
lean_dec_ref(v_a_4095_);
lean_dec(v_a_4094_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___boxed(lean_object* v_info_4101_, lean_object* v_c_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_){
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_info_4101_, v_c_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_);
lean_dec(v_a_4107_);
lean_dec_ref(v_a_4106_);
lean_dec(v_a_4105_);
lean_dec_ref(v_a_4104_);
lean_dec(v_a_4103_);
lean_dec_ref(v_info_4101_);
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18___boxed(lean_object* v___x_4110_, lean_object* v_sz_4111_, lean_object* v_i_4112_, lean_object* v_bs_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
size_t v_sz_boxed_4120_; size_t v_i_boxed_4121_; lean_object* v_res_4122_; 
v_sz_boxed_4120_ = lean_unbox_usize(v_sz_4111_);
lean_dec(v_sz_4111_);
v_i_boxed_4121_ = lean_unbox_usize(v_i_4112_);
lean_dec(v_i_4112_);
v_res_4122_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__18(v___x_4110_, v_sz_boxed_4120_, v_i_boxed_4121_, v_bs_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v___y_4114_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___boxed(lean_object* v_c_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_);
lean_dec(v_a_4128_);
lean_dec_ref(v_a_4127_);
lean_dec(v_a_4126_);
lean_dec_ref(v_a_4125_);
lean_dec(v_a_4124_);
lean_dec_ref(v_c_4123_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16___boxed(lean_object* v___x_4131_, lean_object* v_sz_4132_, lean_object* v_i_4133_, lean_object* v_bs_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_){
_start:
{
size_t v_sz_boxed_4141_; size_t v_i_boxed_4142_; lean_object* v_res_4143_; 
v_sz_boxed_4141_ = lean_unbox_usize(v_sz_4132_);
lean_dec(v_sz_4132_);
v_i_boxed_4142_ = lean_unbox_usize(v_i_4133_);
lean_dec(v_i_4133_);
v_res_4143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__16(v___x_4131_, v_sz_boxed_4141_, v_i_boxed_4142_, v_bs_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
lean_dec(v___y_4139_);
lean_dec_ref(v___y_4138_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec(v___y_4135_);
return v_res_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono___boxed(lean_object* v_code_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_){
_start:
{
lean_object* v_res_4151_; 
v_res_4151_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_);
lean_dec(v_a_4149_);
lean_dec_ref(v_a_4148_);
lean_dec(v_a_4147_);
lean_dec_ref(v_a_4146_);
lean_dec(v_a_4145_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono(lean_object* v_c_4152_, lean_object* v_x_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_){
_start:
{
lean_object* v___x_4160_; 
v___x_4160_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_4152_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___boxed(lean_object* v_c_4161_, lean_object* v_x_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_){
_start:
{
lean_object* v_res_4169_; 
v_res_4169_ = l_Lean_Compiler_LCNF_casesTaskToMono(v_c_4161_, v_x_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_a_4165_);
lean_dec_ref(v_a_4164_);
lean_dec(v_a_4163_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono(lean_object* v_c_4170_, lean_object* v_x_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_){
_start:
{
lean_object* v___x_4178_; 
v___x_4178_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_4170_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_);
return v___x_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___boxed(lean_object* v_c_4179_, lean_object* v_x_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_){
_start:
{
lean_object* v_res_4187_; 
v_res_4187_ = l_Lean_Compiler_LCNF_casesThunkToMono(v_c_4179_, v_x_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
lean_dec(v_a_4185_);
lean_dec_ref(v_a_4184_);
lean_dec(v_a_4183_);
lean_dec_ref(v_a_4182_);
lean_dec(v_a_4181_);
lean_dec_ref(v_c_4179_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono(lean_object* v_c_4188_, lean_object* v_x_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_){
_start:
{
lean_object* v___x_4196_; 
v___x_4196_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_4188_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___boxed(lean_object* v_c_4197_, lean_object* v_x_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l_Lean_Compiler_LCNF_casesStringToMono(v_c_4197_, v_x_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_);
lean_dec(v_a_4203_);
lean_dec_ref(v_a_4202_);
lean_dec(v_a_4201_);
lean_dec_ref(v_a_4200_);
lean_dec(v_a_4199_);
return v_res_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono(lean_object* v_c_4206_, lean_object* v_x_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_){
_start:
{
lean_object* v___x_4214_; 
v___x_4214_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_4206_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_);
return v___x_4214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___boxed(lean_object* v_c_4215_, lean_object* v_x_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono(v_c_4215_, v_x_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_);
lean_dec(v_a_4221_);
lean_dec_ref(v_a_4220_);
lean_dec(v_a_4219_);
lean_dec_ref(v_a_4218_);
lean_dec(v_a_4217_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono(lean_object* v_c_4224_, lean_object* v_x_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_){
_start:
{
lean_object* v___x_4232_; 
v___x_4232_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_4224_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_, v_a_4230_);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___boxed(lean_object* v_c_4233_, lean_object* v_x_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_){
_start:
{
lean_object* v_res_4241_; 
v_res_4241_ = l_Lean_Compiler_LCNF_casesByteArrayToMono(v_c_4233_, v_x_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_);
lean_dec(v_a_4239_);
lean_dec_ref(v_a_4238_);
lean_dec(v_a_4237_);
lean_dec_ref(v_a_4236_);
lean_dec(v_a_4235_);
return v_res_4241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono(lean_object* v_c_4242_, lean_object* v_x_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_){
_start:
{
lean_object* v___x_4250_; 
v___x_4250_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_4242_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___boxed(lean_object* v_c_4251_, lean_object* v_x_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_){
_start:
{
lean_object* v_res_4259_; 
v_res_4259_ = l_Lean_Compiler_LCNF_casesArrayToMono(v_c_4251_, v_x_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_);
lean_dec(v_a_4257_);
lean_dec_ref(v_a_4256_);
lean_dec(v_a_4255_);
lean_dec_ref(v_a_4254_);
lean_dec(v_a_4253_);
return v_res_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono(lean_object* v_c_4260_, lean_object* v_uintName_4261_, lean_object* v_x_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_){
_start:
{
lean_object* v___x_4269_; 
v___x_4269_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_4260_, v_uintName_4261_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_);
return v___x_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___boxed(lean_object* v_c_4270_, lean_object* v_uintName_4271_, lean_object* v_x_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_Lean_Compiler_LCNF_casesUIntToMono(v_c_4270_, v_uintName_4271_, v_x_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_);
lean_dec(v_a_4277_);
lean_dec_ref(v_a_4276_);
lean_dec(v_a_4275_);
lean_dec_ref(v_a_4274_);
lean_dec(v_a_4273_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono(lean_object* v_c_4280_, lean_object* v_x_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_){
_start:
{
lean_object* v___x_4288_; 
v___x_4288_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_4280_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_);
return v___x_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___boxed(lean_object* v_c_4289_, lean_object* v_x_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_){
_start:
{
lean_object* v_res_4297_; 
v_res_4297_ = l_Lean_Compiler_LCNF_casesIntToMono(v_c_4289_, v_x_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_);
lean_dec(v_a_4295_);
lean_dec_ref(v_a_4294_);
lean_dec(v_a_4293_);
lean_dec_ref(v_a_4292_);
lean_dec(v_a_4291_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono(lean_object* v_c_4298_, lean_object* v_x_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_){
_start:
{
lean_object* v___x_4306_; 
v___x_4306_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_4298_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___boxed(lean_object* v_c_4307_, lean_object* v_x_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_){
_start:
{
lean_object* v_res_4315_; 
v_res_4315_ = l_Lean_Compiler_LCNF_casesNatToMono(v_c_4307_, v_x_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_);
lean_dec(v_a_4313_);
lean_dec_ref(v_a_4312_);
lean_dec(v_a_4311_);
lean_dec_ref(v_a_4310_);
lean_dec(v_a_4309_);
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono(lean_object* v_c_4316_, lean_object* v_x_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_){
_start:
{
lean_object* v___x_4324_; 
v___x_4324_ = l_Lean_Compiler_LCNF_decToMono___redArg(v_c_4316_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___boxed(lean_object* v_c_4325_, lean_object* v_x_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_){
_start:
{
lean_object* v_res_4333_; 
v_res_4333_ = l_Lean_Compiler_LCNF_decToMono(v_c_4325_, v_x_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_);
lean_dec(v_a_4331_);
lean_dec_ref(v_a_4330_);
lean_dec(v_a_4329_);
lean_dec_ref(v_a_4328_);
lean_dec(v_a_4327_);
return v_res_4333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(size_t v_sz_4334_, size_t v_i_4335_, lean_object* v_bs_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
lean_object* v___x_4343_; 
v___x_4343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_4334_, v_i_4335_, v_bs_4336_, v___y_4337_, v___y_4339_, v___y_4340_, v___y_4341_);
return v___x_4343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___boxed(lean_object* v_sz_4344_, lean_object* v_i_4345_, lean_object* v_bs_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_){
_start:
{
size_t v_sz_boxed_4353_; size_t v_i_boxed_4354_; lean_object* v_res_4355_; 
v_sz_boxed_4353_ = lean_unbox_usize(v_sz_4344_);
lean_dec(v_sz_4344_);
v_i_boxed_4354_ = lean_unbox_usize(v_i_4345_);
lean_dec(v_i_4345_);
v_res_4355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(v_sz_boxed_4353_, v_i_boxed_4354_, v_bs_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
lean_dec(v___y_4351_);
lean_dec_ref(v___y_4350_);
lean_dec(v___y_4349_);
lean_dec_ref(v___y_4348_);
lean_dec(v___y_4347_);
return v_res_4355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(lean_object* v_f_4356_, lean_object* v_v_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_){
_start:
{
if (lean_obj_tag(v_v_4357_) == 0)
{
lean_object* v_code_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4388_; 
v_code_4364_ = lean_ctor_get(v_v_4357_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v_v_4357_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4366_ = v_v_4357_;
v_isShared_4367_ = v_isSharedCheck_4388_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_code_4364_);
lean_dec(v_v_4357_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4388_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4368_; 
lean_inc(v___y_4362_);
lean_inc_ref(v___y_4361_);
lean_inc(v___y_4360_);
lean_inc_ref(v___y_4359_);
lean_inc(v___y_4358_);
v___x_4368_ = lean_apply_7(v_f_4356_, v_code_4364_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, lean_box(0));
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_object* v_a_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4379_; 
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4371_ = v___x_4368_;
v_isShared_4372_ = v_isSharedCheck_4379_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_a_4369_);
lean_dec(v___x_4368_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4379_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v___x_4374_; 
if (v_isShared_4367_ == 0)
{
lean_ctor_set(v___x_4366_, 0, v_a_4369_);
v___x_4374_ = v___x_4366_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_a_4369_);
v___x_4374_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
lean_object* v___x_4376_; 
if (v_isShared_4372_ == 0)
{
lean_ctor_set(v___x_4371_, 0, v___x_4374_);
v___x_4376_ = v___x_4371_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v___x_4374_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
return v___x_4376_;
}
}
}
}
else
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4387_; 
lean_del_object(v___x_4366_);
v_a_4380_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4382_ = v___x_4368_;
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4368_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4385_; 
if (v_isShared_4383_ == 0)
{
v___x_4385_ = v___x_4382_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_a_4380_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
}
}
else
{
lean_object* v___x_4389_; 
lean_dec_ref(v_f_4356_);
v___x_4389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4389_, 0, v_v_4357_);
return v___x_4389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg___boxed(lean_object* v_f_4390_, lean_object* v_v_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v_res_4398_; 
v_res_4398_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_4390_, v_v_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
lean_dec(v___y_4396_);
lean_dec_ref(v___y_4395_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
lean_dec(v___y_4392_);
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(uint8_t v_pu_4399_, lean_object* v_f_4400_, lean_object* v_v_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
lean_object* v___x_4408_; 
v___x_4408_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_4400_, v_v_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
return v___x_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___boxed(lean_object* v_pu_4409_, lean_object* v_f_4410_, lean_object* v_v_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_){
_start:
{
uint8_t v_pu_boxed_4418_; lean_object* v_res_4419_; 
v_pu_boxed_4418_ = lean_unbox(v_pu_4409_);
v_res_4419_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(v_pu_boxed_4418_, v_f_4410_, v_v_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
lean_dec(v___y_4412_);
return v_res_4419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(lean_object* v_decl_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_){
_start:
{
lean_object* v_toSignature_4428_; lean_object* v_value_4429_; uint8_t v_recursive_4430_; lean_object* v_inlineAttr_x3f_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4501_; 
v_toSignature_4428_ = lean_ctor_get(v_decl_4421_, 0);
v_value_4429_ = lean_ctor_get(v_decl_4421_, 1);
v_recursive_4430_ = lean_ctor_get_uint8(v_decl_4421_, sizeof(void*)*3);
v_inlineAttr_x3f_4431_ = lean_ctor_get(v_decl_4421_, 2);
v_isSharedCheck_4501_ = !lean_is_exclusive(v_decl_4421_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4433_ = v_decl_4421_;
v_isShared_4434_ = v_isSharedCheck_4501_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_inlineAttr_x3f_4431_);
lean_inc(v_value_4429_);
lean_inc(v_toSignature_4428_);
lean_dec(v_decl_4421_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4501_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v_name_4435_; lean_object* v_type_4436_; lean_object* v_params_4437_; uint8_t v_safe_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4499_; 
v_name_4435_ = lean_ctor_get(v_toSignature_4428_, 0);
v_type_4436_ = lean_ctor_get(v_toSignature_4428_, 2);
v_params_4437_ = lean_ctor_get(v_toSignature_4428_, 3);
v_safe_4438_ = lean_ctor_get_uint8(v_toSignature_4428_, sizeof(void*)*4);
v_isSharedCheck_4499_ = !lean_is_exclusive(v_toSignature_4428_);
if (v_isSharedCheck_4499_ == 0)
{
lean_object* v_unused_4500_; 
v_unused_4500_ = lean_ctor_get(v_toSignature_4428_, 1);
lean_dec(v_unused_4500_);
v___x_4440_ = v_toSignature_4428_;
v_isShared_4441_ = v_isSharedCheck_4499_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_params_4437_);
lean_inc(v_type_4436_);
lean_inc(v_name_4435_);
lean_dec(v_toSignature_4428_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4499_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4442_; 
v___x_4442_ = l_Lean_Compiler_LCNF_toMonoType(v_type_4436_, v_a_4425_, v_a_4426_);
if (lean_obj_tag(v___x_4442_) == 0)
{
lean_object* v_a_4443_; size_t v_sz_4444_; size_t v___x_4445_; lean_object* v___x_4446_; 
v_a_4443_ = lean_ctor_get(v___x_4442_, 0);
lean_inc(v_a_4443_);
lean_dec_ref_known(v___x_4442_, 1);
v_sz_4444_ = lean_array_size(v_params_4437_);
v___x_4445_ = ((size_t)0ULL);
v___x_4446_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_4444_, v___x_4445_, v_params_4437_, v_a_4422_, v_a_4424_, v_a_4425_, v_a_4426_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_object* v_a_4447_; lean_object* v___f_4448_; lean_object* v___x_4449_; 
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
lean_inc(v_a_4447_);
lean_dec_ref_known(v___x_4446_, 1);
v___f_4448_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___closed__0));
v___x_4449_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v___f_4448_, v_value_4429_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_);
if (lean_obj_tag(v___x_4449_) == 0)
{
lean_object* v_a_4450_; lean_object* v___x_4451_; lean_object* v___x_4453_; 
v_a_4450_ = lean_ctor_get(v___x_4449_, 0);
lean_inc(v_a_4450_);
lean_dec_ref_known(v___x_4449_, 1);
v___x_4451_ = lean_box(0);
if (v_isShared_4441_ == 0)
{
lean_ctor_set(v___x_4440_, 3, v_a_4447_);
lean_ctor_set(v___x_4440_, 2, v_a_4443_);
lean_ctor_set(v___x_4440_, 1, v___x_4451_);
v___x_4453_ = v___x_4440_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_name_4435_);
lean_ctor_set(v_reuseFailAlloc_4474_, 1, v___x_4451_);
lean_ctor_set(v_reuseFailAlloc_4474_, 2, v_a_4443_);
lean_ctor_set(v_reuseFailAlloc_4474_, 3, v_a_4447_);
lean_ctor_set_uint8(v_reuseFailAlloc_4474_, sizeof(void*)*4, v_safe_4438_);
v___x_4453_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
lean_object* v___x_4455_; 
if (v_isShared_4434_ == 0)
{
lean_ctor_set(v___x_4433_, 1, v_a_4450_);
lean_ctor_set(v___x_4433_, 0, v___x_4453_);
v___x_4455_ = v___x_4433_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v___x_4453_);
lean_ctor_set(v_reuseFailAlloc_4473_, 1, v_a_4450_);
lean_ctor_set(v_reuseFailAlloc_4473_, 2, v_inlineAttr_x3f_4431_);
lean_ctor_set_uint8(v_reuseFailAlloc_4473_, sizeof(void*)*3, v_recursive_4430_);
v___x_4455_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
lean_object* v___x_4456_; 
lean_inc_ref(v___x_4455_);
v___x_4456_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_4455_, v_a_4426_);
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4463_; 
v_isSharedCheck_4463_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4463_ == 0)
{
lean_object* v_unused_4464_; 
v_unused_4464_ = lean_ctor_get(v___x_4456_, 0);
lean_dec(v_unused_4464_);
v___x_4458_ = v___x_4456_;
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
else
{
lean_dec(v___x_4456_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4461_; 
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 0, v___x_4455_);
v___x_4461_ = v___x_4458_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v___x_4455_);
v___x_4461_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
return v___x_4461_;
}
}
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
lean_dec_ref(v___x_4455_);
v_a_4465_ = lean_ctor_get(v___x_4456_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4456_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4456_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
}
}
}
else
{
lean_object* v_a_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4482_; 
lean_dec(v_a_4447_);
lean_dec(v_a_4443_);
lean_del_object(v___x_4440_);
lean_dec(v_name_4435_);
lean_del_object(v___x_4433_);
lean_dec(v_inlineAttr_x3f_4431_);
v_a_4475_ = lean_ctor_get(v___x_4449_, 0);
v_isSharedCheck_4482_ = !lean_is_exclusive(v___x_4449_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4477_ = v___x_4449_;
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_a_4475_);
lean_dec(v___x_4449_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4480_; 
if (v_isShared_4478_ == 0)
{
v___x_4480_ = v___x_4477_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_a_4475_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
}
}
else
{
lean_object* v_a_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4490_; 
lean_dec(v_a_4443_);
lean_del_object(v___x_4440_);
lean_dec(v_name_4435_);
lean_del_object(v___x_4433_);
lean_dec(v_inlineAttr_x3f_4431_);
lean_dec_ref(v_value_4429_);
v_a_4483_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4490_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4485_ = v___x_4446_;
v_isShared_4486_ = v_isSharedCheck_4490_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_a_4483_);
lean_dec(v___x_4446_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4490_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4488_; 
if (v_isShared_4486_ == 0)
{
v___x_4488_ = v___x_4485_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v_a_4483_);
v___x_4488_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
return v___x_4488_;
}
}
}
}
else
{
lean_object* v_a_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4498_; 
lean_del_object(v___x_4440_);
lean_dec_ref(v_params_4437_);
lean_dec(v_name_4435_);
lean_del_object(v___x_4433_);
lean_dec(v_inlineAttr_x3f_4431_);
lean_dec_ref(v_value_4429_);
v_a_4491_ = lean_ctor_get(v___x_4442_, 0);
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4442_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4493_ = v___x_4442_;
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_a_4491_);
lean_dec(v___x_4442_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4496_; 
if (v_isShared_4494_ == 0)
{
v___x_4496_ = v___x_4493_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_a_4491_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___boxed(lean_object* v_decl_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_){
_start:
{
lean_object* v_res_4509_; 
v_res_4509_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_, v_a_4507_);
lean_dec(v_a_4507_);
lean_dec_ref(v_a_4506_);
lean_dec(v_a_4505_);
lean_dec_ref(v_a_4504_);
lean_dec(v_a_4503_);
return v_res_4509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono(lean_object* v_decl_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_){
_start:
{
lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4516_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_4517_ = lean_st_mk_ref(v___x_4516_);
v___x_4518_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_4510_, v___x_4517_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_);
if (lean_obj_tag(v___x_4518_) == 0)
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4527_; 
v_a_4519_ = lean_ctor_get(v___x_4518_, 0);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4518_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4521_ = v___x_4518_;
v_isShared_4522_ = v_isSharedCheck_4527_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4518_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4527_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4523_; lean_object* v___x_4525_; 
v___x_4523_ = lean_st_ref_get(v___x_4517_);
lean_dec(v___x_4517_);
lean_dec(v___x_4523_);
if (v_isShared_4522_ == 0)
{
v___x_4525_ = v___x_4521_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_a_4519_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
return v___x_4525_;
}
}
}
else
{
lean_dec(v___x_4517_);
return v___x_4518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono___boxed(lean_object* v_decl_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_){
_start:
{
lean_object* v_res_4534_; 
v_res_4534_ = l_Lean_Compiler_LCNF_Decl_toMono(v_decl_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_);
lean_dec(v_a_4532_);
lean_dec_ref(v_a_4531_);
lean_dec(v_a_4530_);
lean_dec_ref(v_a_4529_);
return v_res_4534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(size_t v_sz_4535_, size_t v_i_4536_, lean_object* v_bs_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_){
_start:
{
uint8_t v___x_4543_; 
v___x_4543_ = lean_usize_dec_lt(v_i_4536_, v_sz_4535_);
if (v___x_4543_ == 0)
{
lean_object* v___x_4544_; 
v___x_4544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4544_, 0, v_bs_4537_);
return v___x_4544_;
}
else
{
lean_object* v_v_4545_; lean_object* v___x_4546_; 
v_v_4545_ = lean_array_uget_borrowed(v_bs_4537_, v_i_4536_);
lean_inc(v_v_4545_);
v___x_4546_ = l_Lean_Compiler_LCNF_Decl_toMono(v_v_4545_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
if (lean_obj_tag(v___x_4546_) == 0)
{
lean_object* v_a_4547_; lean_object* v___x_4548_; lean_object* v_bs_x27_4549_; size_t v___x_4550_; size_t v___x_4551_; lean_object* v___x_4552_; 
v_a_4547_ = lean_ctor_get(v___x_4546_, 0);
lean_inc(v_a_4547_);
lean_dec_ref_known(v___x_4546_, 1);
v___x_4548_ = lean_unsigned_to_nat(0u);
v_bs_x27_4549_ = lean_array_uset(v_bs_4537_, v_i_4536_, v___x_4548_);
v___x_4550_ = ((size_t)1ULL);
v___x_4551_ = lean_usize_add(v_i_4536_, v___x_4550_);
v___x_4552_ = lean_array_uset(v_bs_x27_4549_, v_i_4536_, v_a_4547_);
v_i_4536_ = v___x_4551_;
v_bs_4537_ = v___x_4552_;
goto _start;
}
else
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4561_; 
lean_dec_ref(v_bs_4537_);
v_a_4554_ = lean_ctor_get(v___x_4546_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4546_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4556_ = v___x_4546_;
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v___x_4546_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4559_; 
if (v_isShared_4557_ == 0)
{
v___x_4559_ = v___x_4556_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4554_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0___boxed(lean_object* v_sz_4562_, lean_object* v_i_4563_, lean_object* v_bs_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
size_t v_sz_boxed_4570_; size_t v_i_boxed_4571_; lean_object* v_res_4572_; 
v_sz_boxed_4570_ = lean_unbox_usize(v_sz_4562_);
lean_dec(v_sz_4562_);
v_i_boxed_4571_ = lean_unbox_usize(v_i_4563_);
lean_dec(v_i_4563_);
v_res_4572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_boxed_4570_, v_i_boxed_4571_, v_bs_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
lean_dec(v___y_4568_);
lean_dec_ref(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
return v_res_4572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0(lean_object* v_x_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
size_t v_sz_4579_; size_t v___x_4580_; lean_object* v___x_4581_; 
v_sz_4579_ = lean_array_size(v_x_4573_);
v___x_4580_ = ((size_t)0ULL);
v___x_4581_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_4579_, v___x_4580_, v_x_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
return v___x_4581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0___boxed(lean_object* v_x_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_){
_start:
{
lean_object* v_res_4588_; 
v_res_4588_ = l_Lean_Compiler_LCNF_toMono___lam__0(v_x_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4671_; uint8_t v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4671_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_));
v___x_4672_ = 1;
v___x_4673_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_));
v___x_4674_ = l_Lean_registerTraceClass(v___x_4671_, v___x_4672_, v___x_4673_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2____boxed(lean_object* v_a_4675_){
_start:
{
lean_object* v_res_4676_; 
v_res_4676_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_();
return v_res_4676_;
}
}
lean_object* runtime_initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_NoncomputableAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ToMono(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
