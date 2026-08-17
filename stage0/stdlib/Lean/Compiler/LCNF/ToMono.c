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
lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(uint8_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default(uint8_t);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
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
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argsToMonoRedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argsToMonoRedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NOption"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__19 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__19_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__20 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__20_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__19_value),LEAN_SCALAR_PTR_LITERAL(21, 120, 174, 159, 13, 218, 111, 37)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__21_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__20_value),LEAN_SCALAR_PTR_LITERAL(167, 241, 117, 234, 215, 201, 251, 103)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__21 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__21_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__22 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__22_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__19_value),LEAN_SCALAR_PTR_LITERAL(21, 120, 174, 159, 13, 218, 111, 37)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__23_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__22_value),LEAN_SCALAR_PTR_LITERAL(107, 31, 205, 245, 3, 195, 74, 76)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__23 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__23_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "someInternal"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__24 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__24_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__19_value),LEAN_SCALAR_PTR_LITERAL(21, 120, 174, 159, 13, 218, 111, 37)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__25_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__24_value),LEAN_SCALAR_PTR_LITERAL(115, 47, 96, 85, 166, 135, 148, 147)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__25 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__25_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "noneInternal"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__26 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__26_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__19_value),LEAN_SCALAR_PTR_LITERAL(21, 120, 174, 159, 13, 218, 111, 37)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__27_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__26_value),LEAN_SCALAR_PTR_LITERAL(162, 30, 133, 50, 138, 74, 166, 151)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__27 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__27_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Compiler.LCNF.ToMono"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__28 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__28_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Compiler.LCNF.LetValue.toMono"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__29 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__29_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__30 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__30_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_LetValue_toMono___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__31;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__32 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__32_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__32_value)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__33 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__33_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__34 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__34_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__35 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__35_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__34_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__36_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__35_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__36 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__36_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__37 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__37_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__38 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__38_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__34_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__39_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__38_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__39 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__39_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__40 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__40_value;
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
static const lean_ctor_object l_Lean_Compiler_LCNF_decToMono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__34_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Compiler_LCNF_decToMono___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_decToMono___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__2_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__7_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__6_value),LEAN_SCALAR_PTR_LITERAL(210, 189, 86, 121, 130, 22, 242, 236)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected constructor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_impl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__3_value),LEAN_SCALAR_PTR_LITERAL(130, 78, 106, 49, 240, 167, 66, 80)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__19_value),LEAN_SCALAR_PTR_LITERAL(21, 120, 174, 159, 13, 218, 111, 37)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__8_value;
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
static const lean_string_object l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Float"};
static const lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(56, 69, 114, 85, 163, 177, 220, 67)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__21 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__21_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Float32"};
static const lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 232, 182, 48, 64, 193, 160, 231)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__22 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__22_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Thunk"};
static const lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(85, 24, 139, 128, 157, 117, 211, 220)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__23 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__23_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Task"};
static const lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(189, 131, 95, 48, 7, 243, 177, 18)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__24 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__24_value;
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
static lean_once_cell_t l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5;
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
static lean_once_cell_t l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5;
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
static const lean_string_object l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isSome"};
static const lean_object* l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 244, 173, 58, 227, 42, 165, 142)}};
static const lean_object* l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2;
static const lean_string_object l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "isSomeInternal"};
static const lean_object* l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__19_value),LEAN_SCALAR_PTR_LITERAL(21, 120, 174, 159, 13, 218, 111, 37)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(156, 203, 233, 225, 201, 141, 105, 8)}};
static const lean_object* l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__4_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "getInternal"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__19_value),LEAN_SCALAR_PTR_LITERAL(21, 120, 174, 159, 13, 218, 111, 37)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 44, 141, 84, 124, 109, 66, 195)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNOptionToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "decLt"};
static const lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(168, 105, 33, 134, 172, 206, 181, 195)}};
static const lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "negSucc"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 236, 205, 0, 179, 53, 99, 201)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natAbs"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 186, 174, 182, 213, 167, 94, 168)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "abs"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__4_value),LEAN_SCALAR_PTR_LITERAL(11, 180, 28, 55, 197, 20, 206, 35)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "one"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 166, 239, 19, 130, 98, 40, 185)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sub"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__4_value),LEAN_SCALAR_PTR_LITERAL(9, 137, 41, 185, 216, 152, 145, 196)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__15_value),LEAN_SCALAR_PTR_LITERAL(147, 155, 141, 233, 87, 0, 52, 207)}};
static const lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isZero"};
static const lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(65, 194, 46, 57, 180, 54, 219, 130)}};
static const lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__4_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "decEq"};
static const lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(13, 188, 70, 193, 211, 173, 121, 176)}};
static const lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__25 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__25_value;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__26 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__26_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__27_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__26_value),LEAN_SCALAR_PTR_LITERAL(196, 237, 71, 156, 244, 3, 80, 55)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__27 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__27_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNOptionToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNOptionToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_131_ = lean_st_ref_put(v_a_104_, v___x_130_);
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
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0(void){
_start:
{
uint8_t v___x_427_; lean_object* v___x_428_; 
v___x_427_ = 0;
v___x_428_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg(lean_object* v_params_429_, lean_object* v_fvarId_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_fvarId_435_; uint8_t v___x_436_; 
v___x_433_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___boxed(lean_object* v_params_441_, lean_object* v_fvarId_442_, lean_object* v_a_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg(v_params_441_, v_fvarId_442_, v_a_443_);
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
v___x_472_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg(v_params_446_, v_fvarId_471_, v_snd_466_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0(lean_object* v_params_561_, lean_object* v_fvarId_562_, lean_object* v_inst_563_, lean_object* v_a_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg(v_params_561_, v_fvarId_562_, v_a_564_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___boxed(lean_object* v_params_572_, lean_object* v_fvarId_573_, lean_object* v_inst_574_, lean_object* v_a_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0(v_params_572_, v_fvarId_573_, v_inst_574_, v_a_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
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
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_15758__overap_808_; lean_object* v___x_809_; 
v___x_805_ = l_StateRefT_x27_instMonad___redArg(v___x_804_);
v___x_806_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5);
v___x_807_ = l_instInhabitedOfMonad___redArg(v___x_805_, v___x_806_);
v___x_15758__overap_808_ = lean_panic_fn_borrowed(v___x_807_, v_msg_749_);
lean_dec(v___x_807_);
lean_inc(v___y_754_);
lean_inc_ref(v___y_753_);
lean_inc(v___y_752_);
lean_inc_ref(v___y_751_);
lean_inc(v___y_750_);
v___x_809_ = lean_apply_6(v___x_15758__overap_808_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, lean_box(0));
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
static lean_object* _init_l_Lean_Compiler_LCNF_LetValue_toMono___closed__31(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_910_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_911_ = lean_unsigned_to_nat(6u);
v___x_912_ = lean_unsigned_to_nat(109u);
v___x_913_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__29));
v___x_914_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_915_ = l_mkPanicMessageWithDecl(v___x_914_, v___x_913_, v___x_912_, v___x_911_, v___x_910_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono(lean_object* v_e_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
switch(lean_obj_tag(v_e_937_))
{
case 2:
{
lean_object* v_typeName_944_; lean_object* v_idx_945_; lean_object* v_struct_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v_typeName_944_ = lean_ctor_get(v_e_937_, 0);
v_idx_945_ = lean_ctor_get(v_e_937_, 1);
v_struct_946_ = lean_ctor_get(v_e_937_, 2);
v___x_947_ = lean_st_ref_get(v_a_938_);
v___x_948_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_947_, v_struct_946_);
lean_dec(v___x_947_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
lean_inc(v_typeName_944_);
v___x_949_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_typeName_944_, v_a_941_, v_a_942_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_969_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_969_ == 0)
{
v___x_952_ = v___x_949_;
v_isShared_953_ = v_isSharedCheck_969_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_949_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_969_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
if (lean_obj_tag(v_a_950_) == 1)
{
lean_object* v_val_954_; lean_object* v_fieldIdx_955_; uint8_t v___x_956_; 
lean_inc(v_struct_946_);
lean_inc(v_idx_945_);
lean_dec_ref_known(v_e_937_, 3);
v_val_954_ = lean_ctor_get(v_a_950_, 0);
lean_inc(v_val_954_);
lean_dec_ref_known(v_a_950_, 1);
v_fieldIdx_955_ = lean_ctor_get(v_val_954_, 2);
lean_inc(v_fieldIdx_955_);
lean_dec(v_val_954_);
v___x_956_ = lean_nat_dec_eq(v_fieldIdx_955_, v_idx_945_);
lean_dec(v_idx_945_);
lean_dec(v_fieldIdx_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_959_; 
lean_dec(v_struct_946_);
v___x_957_ = lean_box(1);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v___x_957_);
v___x_959_ = v___x_952_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
else
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_961_ = ((lean_object*)(l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0));
v___x_962_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_962_, 0, v_struct_946_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v___x_962_);
v___x_964_ = v___x_952_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
else
{
lean_object* v___x_967_; 
lean_dec(v_a_950_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v_e_937_);
v___x_967_ = v___x_952_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_e_937_);
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
lean_dec_ref_known(v_e_937_, 3);
v_a_970_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_949_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_949_);
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
else
{
lean_object* v___x_978_; lean_object* v___x_979_; 
lean_dec_ref_known(v_e_937_, 3);
v___x_978_ = lean_box(1);
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
return v___x_979_;
}
}
case 3:
{
lean_object* v_declName_980_; lean_object* v_args_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1236_; 
v_declName_980_ = lean_ctor_get(v_e_937_, 0);
v_args_981_ = lean_ctor_get(v_e_937_, 2);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_e_937_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; 
v_unused_1237_ = lean_ctor_get(v_e_937_, 1);
lean_dec(v_unused_1237_);
v___x_983_ = v_e_937_;
v_isShared_984_ = v_isSharedCheck_1236_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_args_981_);
lean_inc(v_declName_980_);
lean_dec(v_e_937_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1236_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v_type_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; uint8_t v___y_1023_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1103_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__4));
v___x_1104_ = lean_name_eq(v_declName_980_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__6));
v___x_1106_ = lean_name_eq(v_declName_980_, v___x_1105_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__8));
v___x_1108_ = lean_name_eq(v_declName_980_, v___x_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1109_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__11));
v___x_1110_ = lean_name_eq(v_declName_980_, v___x_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__13));
v___x_1112_ = lean_name_eq(v_declName_980_, v___x_1111_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1113_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__16));
v___x_1114_ = lean_name_eq(v_declName_980_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__18));
v___x_1116_ = lean_name_eq(v_declName_980_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_1118_ = lean_name_eq(v_declName_980_, v___x_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__23));
v___x_1120_ = lean_name_eq(v_declName_980_, v___x_1119_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v_env_1122_; lean_object* v___x_1123_; 
v___x_1121_ = lean_st_ref_get(v_a_942_);
v_env_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc_ref(v_env_1122_);
lean_dec(v___x_1121_);
lean_inc(v_declName_980_);
v___x_1123_ = l_Lean_Environment_find_x3f(v_env_1122_, v_declName_980_, v___x_1120_);
if (lean_obj_tag(v___x_1123_) == 1)
{
lean_object* v_val_1124_; 
v_val_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_val_1124_);
lean_dec_ref_known(v___x_1123_, 1);
if (lean_obj_tag(v_val_1124_) == 6)
{
lean_object* v_val_1125_; lean_object* v_induct_1126_; lean_object* v_numParams_1127_; lean_object* v___x_1128_; 
lean_del_object(v___x_983_);
lean_dec(v_declName_980_);
v_val_1125_ = lean_ctor_get(v_val_1124_, 0);
lean_inc_ref(v_val_1125_);
lean_dec_ref_known(v_val_1124_, 1);
v_induct_1126_ = lean_ctor_get(v_val_1125_, 1);
v_numParams_1127_ = lean_ctor_get(v_val_1125_, 3);
lean_inc(v_induct_1126_);
v___x_1128_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_induct_1126_, v_a_941_, v_a_942_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1128_, 1);
if (lean_obj_tag(v_a_1129_) == 1)
{
lean_object* v_val_1130_; lean_object* v_fieldIdx_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_inc(v_numParams_1127_);
lean_dec_ref(v_val_1125_);
v_val_1130_ = lean_ctor_get(v_a_1129_, 0);
lean_inc(v_val_1130_);
lean_dec_ref_known(v_a_1129_, 1);
v_fieldIdx_1131_ = lean_ctor_get(v_val_1130_, 2);
lean_inc(v_fieldIdx_1131_);
lean_dec(v_val_1130_);
v___x_1132_ = lean_box(0);
v___x_1133_ = lean_nat_add(v_numParams_1127_, v_fieldIdx_1131_);
lean_dec(v_fieldIdx_1131_);
lean_dec(v_numParams_1127_);
v___x_1134_ = lean_array_get(v___x_1132_, v_args_981_, v___x_1133_);
lean_dec(v___x_1133_);
lean_dec_ref(v_args_981_);
v___x_1135_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_1134_);
lean_dec(v___x_1134_);
v_e_937_ = v___x_1135_;
goto _start;
}
else
{
lean_object* v___x_1137_; 
lean_dec(v_a_1129_);
v___x_1137_ = l_Lean_Compiler_LCNF_ctorAppToMono(v_val_1125_, v_args_981_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
return v___x_1137_;
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec_ref(v_val_1125_);
lean_dec_ref(v_args_981_);
v_a_1138_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1128_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1128_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
else
{
lean_dec(v_val_1124_);
v___y_1046_ = v_a_938_;
v___y_1047_ = v_a_939_;
v___y_1048_ = v_a_940_;
v___y_1049_ = v_a_941_;
v___y_1050_ = v_a_942_;
goto v___jp_1045_;
}
}
else
{
lean_dec(v___x_1123_);
v___y_1046_ = v_a_938_;
v___y_1047_ = v_a_939_;
v___y_1048_ = v_a_940_;
v___y_1049_ = v_a_941_;
v___y_1050_ = v_a_942_;
goto v___jp_1045_;
}
}
else
{
size_t v_sz_1146_; size_t v___x_1147_; lean_object* v___x_1148_; 
lean_del_object(v___x_983_);
lean_dec(v_declName_980_);
v_sz_1146_ = lean_array_size(v_args_981_);
v___x_1147_ = ((size_t)0ULL);
v___x_1148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_1146_, v___x_1147_, v_args_981_, v_a_938_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1159_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1151_ = v___x_1148_;
v_isShared_1152_ = v_isSharedCheck_1159_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1159_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1153_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__25));
v___x_1154_ = lean_box(0);
v___x_1155_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
lean_ctor_set(v___x_1155_, 2, v_a_1149_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1155_);
v___x_1157_ = v___x_1151_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
v_a_1160_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1148_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1148_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
else
{
size_t v_sz_1168_; size_t v___x_1169_; lean_object* v___x_1170_; 
lean_del_object(v___x_983_);
lean_dec(v_declName_980_);
v_sz_1168_ = lean_array_size(v_args_981_);
v___x_1169_ = ((size_t)0ULL);
v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_1168_, v___x_1169_, v_args_981_, v_a_938_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1181_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1181_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1181_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1175_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__27));
v___x_1176_ = lean_box(0);
v___x_1177_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1175_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
lean_ctor_set(v___x_1177_, 2, v_a_1171_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v___x_1177_);
v___x_1179_ = v___x_1173_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
v_a_1182_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1170_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1170_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
else
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
lean_del_object(v___x_983_);
lean_dec_ref(v_args_981_);
lean_dec(v_declName_980_);
v___x_1190_ = lean_obj_once(&l_Lean_Compiler_LCNF_LetValue_toMono___closed__31, &l_Lean_Compiler_LCNF_LetValue_toMono___closed__31_once, _init_l_Lean_Compiler_LCNF_LetValue_toMono___closed__31);
v___x_1191_ = l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(v___x_1190_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
return v___x_1191_;
}
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_del_object(v___x_983_);
lean_dec_ref(v_args_981_);
lean_dec(v_declName_980_);
v___x_1192_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__33));
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
return v___x_1193_;
}
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_del_object(v___x_983_);
lean_dec(v_declName_980_);
v___x_1194_ = lean_box(0);
v___x_1195_ = lean_unsigned_to_nat(2u);
v___x_1196_ = lean_array_get_borrowed(v___x_1194_, v_args_981_, v___x_1195_);
if (lean_obj_tag(v___x_1196_) == 1)
{
lean_object* v_fvarId_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v_extraArgs_1201_; lean_object* v___x_1202_; 
v_fvarId_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_fvarId_1197_);
v___x_1198_ = lean_array_get_size(v_args_981_);
v___x_1199_ = lean_unsigned_to_nat(3u);
v___x_1200_ = lean_nat_sub(v___x_1198_, v___x_1199_);
v_extraArgs_1201_ = lean_mk_empty_array_with_capacity(v___x_1200_);
lean_dec(v___x_1200_);
v___x_1202_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v___x_1198_, v_args_981_, v___x_1199_, v_extraArgs_1201_, v_a_938_);
lean_dec_ref(v_args_981_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1211_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1205_ = v___x_1202_;
v_isShared_1206_ = v_isSharedCheck_1211_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1211_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1207_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1207_, 0, v_fvarId_1197_);
lean_ctor_set(v___x_1207_, 1, v_a_1203_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1207_);
v___x_1209_ = v___x_1205_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec(v_fvarId_1197_);
v_a_1212_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1202_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1202_);
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
else
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_dec_ref(v_args_981_);
v___x_1220_ = lean_box(1);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
}
}
else
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
lean_del_object(v___x_983_);
lean_dec(v_declName_980_);
v___x_1222_ = lean_box(0);
v___x_1223_ = lean_unsigned_to_nat(2u);
v___x_1224_ = lean_array_get(v___x_1222_, v_args_981_, v___x_1223_);
lean_dec_ref(v_args_981_);
v___x_1225_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_1224_);
lean_dec(v___x_1224_);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
return v___x_1226_;
}
}
else
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_del_object(v___x_983_);
lean_dec(v_declName_980_);
v___x_1227_ = lean_box(0);
v___x_1228_ = lean_unsigned_to_nat(1u);
v___x_1229_ = lean_array_get(v___x_1227_, v_args_981_, v___x_1228_);
lean_dec_ref(v_args_981_);
v___x_1230_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_1229_);
lean_dec(v___x_1229_);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
return v___x_1231_;
}
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_del_object(v___x_983_);
lean_dec_ref(v_args_981_);
lean_dec(v_declName_980_);
v___x_1232_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__37));
v___x_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
return v___x_1233_;
}
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_del_object(v___x_983_);
lean_dec_ref(v_args_981_);
lean_dec(v_declName_980_);
v___x_1234_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__40));
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
return v___x_1235_;
}
v___jp_985_:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_Compiler_LCNF_argsToMonoWithFnType(v_args_981_, v_type_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec_ref(v_args_981_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1004_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1004_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1004_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_997_ = lean_box(0);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 2, v_a_993_);
lean_ctor_set(v___x_983_, 1, v___x_997_);
v___x_999_ = v___x_983_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_declName_980_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1003_, 2, v_a_993_);
v___x_999_ = v_reuseFailAlloc_1003_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1001_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_999_);
v___x_1001_ = v___x_995_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
lean_del_object(v___x_983_);
lean_dec(v_declName_980_);
v_a_1005_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_992_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_992_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
v___jp_1013_:
{
if (v___y_1023_ == 0)
{
lean_object* v_toSignature_1024_; lean_object* v_type_1025_; 
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1017_);
lean_dec_ref(v___y_1015_);
v_toSignature_1024_ = lean_ctor_get(v___y_1018_, 0);
lean_inc_ref(v_toSignature_1024_);
lean_dec_ref(v___y_1018_);
v_type_1025_ = lean_ctor_get(v_toSignature_1024_, 2);
lean_inc_ref(v_type_1025_);
lean_dec_ref(v_toSignature_1024_);
v_type_986_ = v_type_1025_;
v___y_987_ = v___y_1021_;
v___y_988_ = v___y_1014_;
v___y_989_ = v___y_1016_;
v___y_990_ = v___y_1020_;
v___y_991_ = v___y_1019_;
goto v___jp_985_;
}
else
{
lean_object* v___x_1026_; 
lean_dec_ref(v___y_1018_);
lean_del_object(v___x_983_);
lean_dec(v_declName_980_);
v___x_1026_ = l_Lean_Compiler_LCNF_argsToMonoRedArg(v_args_981_, v___y_1017_, v___y_1015_, v___y_1021_, v___y_1014_, v___y_1016_, v___y_1020_, v___y_1019_);
lean_dec_ref(v___y_1015_);
lean_dec_ref(v___y_1017_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1036_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1036_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1036_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1031_ = lean_box(0);
v___x_1032_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1032_, 0, v___y_1022_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
lean_ctor_set(v___x_1032_, 2, v_a_1027_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1032_);
v___x_1034_ = v___x_1029_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec(v___y_1022_);
v_a_1037_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1026_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1026_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
v___jp_1045_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = lean_st_ref_get(v___y_1050_);
lean_dec(v___x_1051_);
lean_inc(v_declName_980_);
v___x_1052_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_980_, v___y_1050_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1052_, 1);
if (lean_obj_tag(v_a_1053_) == 1)
{
lean_object* v_val_1054_; lean_object* v_toSignature_1055_; lean_object* v_value_1056_; lean_object* v_type_1057_; lean_object* v_params_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v_val_1054_ = lean_ctor_get(v_a_1053_, 0);
lean_inc(v_val_1054_);
lean_dec_ref_known(v_a_1053_, 1);
v_toSignature_1055_ = lean_ctor_get(v_val_1054_, 0);
v_value_1056_ = lean_ctor_get(v_val_1054_, 1);
v_type_1057_ = lean_ctor_get(v_toSignature_1055_, 2);
v_params_1058_ = lean_ctor_get(v_toSignature_1055_, 3);
lean_inc_ref(v_params_1058_);
v___x_1059_ = lean_array_get_size(v_params_1058_);
v___x_1060_ = lean_array_get_size(v_args_981_);
v___x_1061_ = lean_nat_dec_le(v___x_1059_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_inc_ref(v_type_1057_);
lean_dec_ref(v_params_1058_);
lean_dec(v_val_1054_);
v_type_986_ = v_type_1057_;
v___y_987_ = v___y_1046_;
v___y_988_ = v___y_1047_;
v___y_989_ = v___y_1048_;
v___y_990_ = v___y_1049_;
v___y_991_ = v___y_1050_;
goto v___jp_985_;
}
else
{
if (lean_obj_tag(v_value_1056_) == 0)
{
lean_object* v_code_1062_; 
v_code_1062_ = lean_ctor_get(v_value_1056_, 0);
if (lean_obj_tag(v_code_1062_) == 0)
{
lean_object* v_decl_1063_; lean_object* v_value_1064_; 
v_decl_1063_ = lean_ctor_get(v_code_1062_, 0);
v_value_1064_ = lean_ctor_get(v_decl_1063_, 3);
if (lean_obj_tag(v_value_1064_) == 3)
{
lean_object* v_k_1065_; 
v_k_1065_ = lean_ctor_get(v_code_1062_, 1);
if (lean_obj_tag(v_k_1065_) == 5)
{
lean_object* v_fvarId_1066_; lean_object* v_declName_1067_; lean_object* v_args_1068_; lean_object* v_fvarId_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v_fvarId_1066_ = lean_ctor_get(v_decl_1063_, 0);
v_declName_1067_ = lean_ctor_get(v_value_1064_, 0);
v_args_1068_ = lean_ctor_get(v_value_1064_, 2);
lean_inc_ref(v_args_1068_);
v_fvarId_1069_ = lean_ctor_get(v_k_1065_, 0);
v___x_1070_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__1));
lean_inc(v_declName_980_);
v___x_1071_ = l_Lean_Name_append(v_declName_980_, v___x_1070_);
v___x_1072_ = lean_name_eq(v_declName_1067_, v___x_1071_);
if (v___x_1072_ == 0)
{
v___y_1014_ = v___y_1047_;
v___y_1015_ = v_args_1068_;
v___y_1016_ = v___y_1048_;
v___y_1017_ = v_params_1058_;
v___y_1018_ = v_val_1054_;
v___y_1019_ = v___y_1050_;
v___y_1020_ = v___y_1049_;
v___y_1021_ = v___y_1046_;
v___y_1022_ = v___x_1071_;
v___y_1023_ = v___x_1072_;
goto v___jp_1013_;
}
else
{
uint8_t v___x_1073_; 
v___x_1073_ = l_Lean_instBEqFVarId_beq(v_fvarId_1069_, v_fvarId_1066_);
v___y_1014_ = v___y_1047_;
v___y_1015_ = v_args_1068_;
v___y_1016_ = v___y_1048_;
v___y_1017_ = v_params_1058_;
v___y_1018_ = v_val_1054_;
v___y_1019_ = v___y_1050_;
v___y_1020_ = v___y_1049_;
v___y_1021_ = v___y_1046_;
v___y_1022_ = v___x_1071_;
v___y_1023_ = v___x_1073_;
goto v___jp_1013_;
}
}
else
{
lean_inc_ref(v_type_1057_);
lean_dec_ref(v_params_1058_);
lean_dec(v_val_1054_);
v_type_986_ = v_type_1057_;
v___y_987_ = v___y_1046_;
v___y_988_ = v___y_1047_;
v___y_989_ = v___y_1048_;
v___y_990_ = v___y_1049_;
v___y_991_ = v___y_1050_;
goto v___jp_985_;
}
}
else
{
lean_inc_ref(v_type_1057_);
lean_dec_ref(v_params_1058_);
lean_dec(v_val_1054_);
v_type_986_ = v_type_1057_;
v___y_987_ = v___y_1046_;
v___y_988_ = v___y_1047_;
v___y_989_ = v___y_1048_;
v___y_990_ = v___y_1049_;
v___y_991_ = v___y_1050_;
goto v___jp_985_;
}
}
else
{
lean_inc_ref(v_type_1057_);
lean_dec_ref(v_params_1058_);
lean_dec(v_val_1054_);
v_type_986_ = v_type_1057_;
v___y_987_ = v___y_1046_;
v___y_988_ = v___y_1047_;
v___y_989_ = v___y_1048_;
v___y_990_ = v___y_1049_;
v___y_991_ = v___y_1050_;
goto v___jp_985_;
}
}
else
{
lean_inc_ref(v_type_1057_);
lean_dec_ref(v_params_1058_);
lean_dec(v_val_1054_);
v_type_986_ = v_type_1057_;
v___y_987_ = v___y_1046_;
v___y_988_ = v___y_1047_;
v___y_989_ = v___y_1048_;
v___y_990_ = v___y_1049_;
v___y_991_ = v___y_1050_;
goto v___jp_985_;
}
}
}
else
{
size_t v_sz_1074_; size_t v___x_1075_; lean_object* v___x_1076_; 
lean_dec(v_a_1053_);
lean_del_object(v___x_983_);
v_sz_1074_ = lean_array_size(v_args_981_);
v___x_1075_ = ((size_t)0ULL);
v___x_1076_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_1074_, v___x_1075_, v_args_981_, v___y_1046_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1086_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1086_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1086_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1081_ = lean_box(0);
v___x_1082_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1082_, 0, v_declName_980_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
lean_ctor_set(v___x_1082_, 2, v_a_1077_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1082_);
v___x_1084_ = v___x_1079_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec(v_declName_980_);
v_a_1087_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1076_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1076_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_del_object(v___x_983_);
lean_dec_ref(v_args_981_);
lean_dec(v_declName_980_);
v_a_1095_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1052_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1052_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
}
case 4:
{
lean_object* v_fvarId_1238_; lean_object* v_args_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1269_; 
v_fvarId_1238_ = lean_ctor_get(v_e_937_, 0);
v_args_1239_ = lean_ctor_get(v_e_937_, 1);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_e_937_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1241_ = v_e_937_;
v_isShared_1242_ = v_isSharedCheck_1269_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_args_1239_);
lean_inc(v_fvarId_1238_);
lean_dec(v_e_937_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1269_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1243_ = lean_st_ref_get(v_a_938_);
v___x_1244_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_1243_, v_fvarId_1238_);
lean_dec(v___x_1243_);
if (v___x_1244_ == 0)
{
size_t v_sz_1245_; size_t v___x_1246_; lean_object* v___x_1247_; 
v_sz_1245_ = lean_array_size(v_args_1239_);
v___x_1246_ = ((size_t)0ULL);
v___x_1247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_1245_, v___x_1246_, v_args_1239_, v_a_938_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1258_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1250_ = v___x_1247_;
v_isShared_1251_ = v_isSharedCheck_1258_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1258_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 1, v_a_1248_);
v___x_1253_ = v___x_1241_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_fvarId_1238_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1255_; 
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1253_);
v___x_1255_ = v___x_1250_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_del_object(v___x_1241_);
lean_dec(v_fvarId_1238_);
v_a_1259_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1247_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1247_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
lean_del_object(v___x_1241_);
lean_dec_ref(v_args_1239_);
lean_dec(v_fvarId_1238_);
v___x_1267_ = lean_box(1);
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
return v___x_1268_;
}
}
}
default: 
{
lean_object* v___x_1270_; 
v___x_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1270_, 0, v_e_937_);
return v___x_1270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___boxed(lean_object* v_e_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_Compiler_LCNF_LetValue_toMono(v_e_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1(lean_object* v_upperBound_1279_, lean_object* v_args_1280_, lean_object* v_inst_1281_, lean_object* v_R_1282_, lean_object* v_a_1283_, lean_object* v_b_1284_, lean_object* v_c_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v_upperBound_1279_, v_args_1280_, v_a_1283_, v_b_1284_, v___y_1286_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___boxed(lean_object* v_upperBound_1293_, lean_object* v_args_1294_, lean_object* v_inst_1295_, lean_object* v_R_1296_, lean_object* v_a_1297_, lean_object* v_b_1298_, lean_object* v_c_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1(v_upperBound_1293_, v_args_1294_, v_inst_1295_, v_R_1296_, v_a_1297_, v_b_1298_, v_c_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v_args_1294_);
lean_dec(v_upperBound_1293_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono(lean_object* v_decl_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v_type_1314_; lean_object* v_value_1315_; lean_object* v___x_1316_; 
v_type_1314_ = lean_ctor_get(v_decl_1307_, 2);
v_value_1315_ = lean_ctor_get(v_decl_1307_, 3);
lean_inc_ref(v_type_1314_);
v___x_1316_ = l_Lean_Compiler_LCNF_toMonoType(v_type_1314_, v_a_1311_, v_a_1312_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1318_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_a_1317_);
lean_dec_ref_known(v___x_1316_, 1);
lean_inc(v_value_1315_);
v___x_1318_ = l_Lean_Compiler_LCNF_LetValue_toMono(v_value_1315_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; uint8_t v___x_1320_; lean_object* v___x_1321_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
v___x_1320_ = 0;
v___x_1321_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_1320_, v_decl_1307_, v_a_1317_, v_a_1319_, v_a_1310_);
return v___x_1321_;
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec(v_a_1317_);
lean_dec_ref(v_decl_1307_);
v_a_1322_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1318_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1318_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec_ref(v_decl_1307_);
v_a_1330_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1316_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1316_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono___boxed(lean_object* v_decl_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_Compiler_LCNF_LetDecl_toMono(v_decl_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_);
lean_dec(v_a_1343_);
lean_dec_ref(v_a_1342_);
lean_dec(v_a_1341_);
lean_dec_ref(v_a_1340_);
lean_dec(v_a_1339_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(lean_object* v_msg_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v_toApplicative_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1417_; 
v___x_1353_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1354_ = l_StateRefT_x27_instMonad___redArg(v___x_1353_);
v_toApplicative_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1417_ == 0)
{
lean_object* v_unused_1418_; 
v_unused_1418_ = lean_ctor_get(v___x_1354_, 1);
lean_dec(v_unused_1418_);
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1417_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_toApplicative_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1417_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v_toFunctor_1359_; lean_object* v_toSeq_1360_; lean_object* v_toSeqLeft_1361_; lean_object* v_toSeqRight_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1415_; 
v_toFunctor_1359_ = lean_ctor_get(v_toApplicative_1355_, 0);
v_toSeq_1360_ = lean_ctor_get(v_toApplicative_1355_, 2);
v_toSeqLeft_1361_ = lean_ctor_get(v_toApplicative_1355_, 3);
v_toSeqRight_1362_ = lean_ctor_get(v_toApplicative_1355_, 4);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_toApplicative_1355_);
if (v_isSharedCheck_1415_ == 0)
{
lean_object* v_unused_1416_; 
v_unused_1416_ = lean_ctor_get(v_toApplicative_1355_, 1);
lean_dec(v_unused_1416_);
v___x_1364_ = v_toApplicative_1355_;
v_isShared_1365_ = v_isSharedCheck_1415_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_toSeqRight_1362_);
lean_inc(v_toSeqLeft_1361_);
lean_inc(v_toSeq_1360_);
lean_inc(v_toFunctor_1359_);
lean_dec(v_toApplicative_1355_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1415_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___f_1366_; lean_object* v___f_1367_; lean_object* v___f_1368_; lean_object* v___f_1369_; lean_object* v___x_1370_; lean_object* v___f_1371_; lean_object* v___f_1372_; lean_object* v___f_1373_; lean_object* v___x_1375_; 
v___f_1366_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1367_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1359_);
v___f_1368_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1368_, 0, v_toFunctor_1359_);
v___f_1369_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1369_, 0, v_toFunctor_1359_);
v___x_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___f_1368_);
lean_ctor_set(v___x_1370_, 1, v___f_1369_);
v___f_1371_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1371_, 0, v_toSeqRight_1362_);
v___f_1372_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1372_, 0, v_toSeqLeft_1361_);
v___f_1373_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1373_, 0, v_toSeq_1360_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 4, v___f_1371_);
lean_ctor_set(v___x_1364_, 3, v___f_1372_);
lean_ctor_set(v___x_1364_, 2, v___f_1373_);
lean_ctor_set(v___x_1364_, 1, v___f_1366_);
lean_ctor_set(v___x_1364_, 0, v___x_1370_);
v___x_1375_ = v___x_1364_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v___f_1366_);
lean_ctor_set(v_reuseFailAlloc_1414_, 2, v___f_1373_);
lean_ctor_set(v_reuseFailAlloc_1414_, 3, v___f_1372_);
lean_ctor_set(v_reuseFailAlloc_1414_, 4, v___f_1371_);
v___x_1375_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1377_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 1, v___f_1367_);
lean_ctor_set(v___x_1357_, 0, v___x_1375_);
v___x_1377_ = v___x_1357_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v___f_1367_);
v___x_1377_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
lean_object* v___x_1378_; lean_object* v_toApplicative_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1411_; 
v___x_1378_ = l_StateRefT_x27_instMonad___redArg(v___x_1377_);
v_toApplicative_1379_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v___x_1378_, 1);
lean_dec(v_unused_1412_);
v___x_1381_ = v___x_1378_;
v_isShared_1382_ = v_isSharedCheck_1411_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_toApplicative_1379_);
lean_dec(v___x_1378_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1411_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v_toFunctor_1383_; lean_object* v_toSeq_1384_; lean_object* v_toSeqLeft_1385_; lean_object* v_toSeqRight_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1409_; 
v_toFunctor_1383_ = lean_ctor_get(v_toApplicative_1379_, 0);
v_toSeq_1384_ = lean_ctor_get(v_toApplicative_1379_, 2);
v_toSeqLeft_1385_ = lean_ctor_get(v_toApplicative_1379_, 3);
v_toSeqRight_1386_ = lean_ctor_get(v_toApplicative_1379_, 4);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_toApplicative_1379_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; 
v_unused_1410_ = lean_ctor_get(v_toApplicative_1379_, 1);
lean_dec(v_unused_1410_);
v___x_1388_ = v_toApplicative_1379_;
v_isShared_1389_ = v_isSharedCheck_1409_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_toSeqRight_1386_);
lean_inc(v_toSeqLeft_1385_);
lean_inc(v_toSeq_1384_);
lean_inc(v_toFunctor_1383_);
lean_dec(v_toApplicative_1379_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1409_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___f_1390_; lean_object* v___f_1391_; lean_object* v___f_1392_; lean_object* v___f_1393_; lean_object* v___x_1394_; lean_object* v___f_1395_; lean_object* v___f_1396_; lean_object* v___f_1397_; lean_object* v___x_1399_; 
v___f_1390_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1391_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1383_);
v___f_1392_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1392_, 0, v_toFunctor_1383_);
v___f_1393_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1393_, 0, v_toFunctor_1383_);
v___x_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___f_1392_);
lean_ctor_set(v___x_1394_, 1, v___f_1393_);
v___f_1395_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1395_, 0, v_toSeqRight_1386_);
v___f_1396_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1396_, 0, v_toSeqLeft_1385_);
v___f_1397_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1397_, 0, v_toSeq_1384_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 4, v___f_1395_);
lean_ctor_set(v___x_1388_, 3, v___f_1396_);
lean_ctor_set(v___x_1388_, 2, v___f_1397_);
lean_ctor_set(v___x_1388_, 1, v___f_1390_);
lean_ctor_set(v___x_1388_, 0, v___x_1394_);
v___x_1399_ = v___x_1388_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v___f_1390_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v___f_1397_);
lean_ctor_set(v_reuseFailAlloc_1408_, 3, v___f_1396_);
lean_ctor_set(v_reuseFailAlloc_1408_, 4, v___f_1395_);
v___x_1399_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1401_; 
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 1, v___f_1391_);
lean_ctor_set(v___x_1381_, 0, v___x_1399_);
v___x_1401_ = v___x_1381_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1399_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v___f_1391_);
v___x_1401_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_4540__overap_1405_; lean_object* v___x_1406_; 
v___x_1402_ = l_StateRefT_x27_instMonad___redArg(v___x_1401_);
v___x_1403_ = lean_box(0);
v___x_1404_ = l_instInhabitedOfMonad___redArg(v___x_1402_, v___x_1403_);
v___x_4540__overap_1405_ = lean_panic_fn_borrowed(v___x_1404_, v_msg_1346_);
lean_dec(v___x_1404_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
lean_inc(v___y_1349_);
lean_inc_ref(v___y_1348_);
lean_inc(v___y_1347_);
v___x_1406_ = lean_apply_6(v___x_4540__overap_1405_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, lean_box(0));
return v___x_1406_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0___boxed(lean_object* v_msg_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v_msg_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
return v_res_1426_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1428_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_1429_ = lean_unsigned_to_nat(11u);
v___x_1430_ = lean_unsigned_to_nat(162u);
v___x_1431_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__0));
v___x_1432_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_1433_ = l_mkPanicMessageWithDecl(v___x_1432_, v___x_1431_, v___x_1430_, v___x_1429_, v___x_1428_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(lean_object* v_upperBound_1434_, lean_object* v_a_1435_, lean_object* v_b_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_a_1444_; uint8_t v___x_1448_; 
v___x_1448_ = lean_nat_dec_lt(v_a_1435_, v_upperBound_1434_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; 
lean_dec(v_a_1435_);
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v_b_1436_);
return v___x_1449_;
}
else
{
if (lean_obj_tag(v_b_1436_) == 7)
{
lean_object* v_body_1450_; 
v_body_1450_ = lean_ctor_get(v_b_1436_, 2);
lean_inc_ref(v_body_1450_);
lean_dec_ref_known(v_b_1436_, 3);
v_a_1444_ = v_body_1450_;
goto v___jp_1443_;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1);
v___x_1452_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v___x_1451_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_dec_ref_known(v___x_1452_, 1);
v_a_1444_ = v_b_1436_;
goto v___jp_1443_;
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec_ref(v_b_1436_);
lean_dec(v_a_1435_);
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
}
v___jp_1443_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = lean_unsigned_to_nat(1u);
v___x_1446_ = lean_nat_add(v_a_1435_, v___x_1445_);
lean_dec(v_a_1435_);
v_a_1435_ = v___x_1446_;
v_b_1436_ = v_a_1444_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___boxed(lean_object* v_upperBound_1461_, lean_object* v_a_1462_, lean_object* v_b_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_upperBound_1461_, v_a_1462_, v_b_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec(v_upperBound_1461_);
return v_res_1470_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1471_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_1472_ = lean_unsigned_to_nat(11u);
v___x_1473_ = lean_unsigned_to_nat(170u);
v___x_1474_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__0));
v___x_1475_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_1476_ = l_mkPanicMessageWithDecl(v___x_1475_, v___x_1474_, v___x_1473_, v___x_1472_, v___x_1471_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(lean_object* v_upperBound_1477_, lean_object* v_a_1478_, lean_object* v_b_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v_a_1487_; uint8_t v___x_1491_; 
v___x_1491_ = lean_nat_dec_lt(v_a_1478_, v_upperBound_1477_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; 
lean_dec(v_a_1478_);
v___x_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1492_, 0, v_b_1479_);
return v___x_1492_;
}
else
{
lean_object* v_fst_1493_; 
v_fst_1493_ = lean_ctor_get(v_b_1479_, 0);
lean_inc(v_fst_1493_);
if (lean_obj_tag(v_fst_1493_) == 7)
{
lean_object* v_snd_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1527_; 
v_snd_1494_ = lean_ctor_get(v_b_1479_, 1);
v_isSharedCheck_1527_ = !lean_is_exclusive(v_b_1479_);
if (v_isSharedCheck_1527_ == 0)
{
lean_object* v_unused_1528_; 
v_unused_1528_ = lean_ctor_get(v_b_1479_, 0);
lean_dec(v_unused_1528_);
v___x_1496_ = v_b_1479_;
v_isShared_1497_ = v_isSharedCheck_1527_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_snd_1494_);
lean_dec(v_b_1479_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1527_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v_binderName_1498_; lean_object* v_binderType_1499_; lean_object* v_body_1500_; lean_object* v___x_1501_; 
v_binderName_1498_ = lean_ctor_get(v_fst_1493_, 0);
lean_inc(v_binderName_1498_);
v_binderType_1499_ = lean_ctor_get(v_fst_1493_, 1);
lean_inc_ref(v_binderType_1499_);
v_body_1500_ = lean_ctor_get(v_fst_1493_, 2);
lean_inc_ref(v_body_1500_);
lean_dec_ref_known(v_fst_1493_, 3);
v___x_1501_ = l_Lean_Compiler_LCNF_toMonoType(v_binderType_1499_, v___y_1483_, v___y_1484_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; uint8_t v___x_1503_; uint8_t v___x_1504_; lean_object* v___x_1505_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1501_, 1);
v___x_1503_ = 0;
v___x_1504_ = 0;
v___x_1505_ = l_Lean_Compiler_LCNF_mkParam(v___x_1503_, v_binderName_1498_, v_a_1502_, v___x_1504_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref_known(v___x_1505_, 1);
v___x_1507_ = lean_array_push(v_snd_1494_, v_a_1506_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 1, v___x_1507_);
lean_ctor_set(v___x_1496_, 0, v_body_1500_);
v___x_1509_ = v___x_1496_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_body_1500_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
v_a_1487_ = v___x_1509_;
goto v___jp_1486_;
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec_ref(v_body_1500_);
lean_del_object(v___x_1496_);
lean_dec(v_snd_1494_);
lean_dec(v_a_1478_);
v_a_1511_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1505_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1505_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec_ref(v_body_1500_);
lean_dec(v_binderName_1498_);
lean_del_object(v___x_1496_);
lean_dec(v_snd_1494_);
lean_dec(v_a_1478_);
v_a_1519_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1501_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1501_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
else
{
lean_object* v_snd_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1546_; 
v_snd_1529_ = lean_ctor_get(v_b_1479_, 1);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_b_1479_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; 
v_unused_1547_ = lean_ctor_get(v_b_1479_, 0);
lean_dec(v_unused_1547_);
v___x_1531_ = v_b_1479_;
v_isShared_1532_ = v_isSharedCheck_1546_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_snd_1529_);
lean_dec(v_b_1479_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1546_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0);
v___x_1534_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v___x_1533_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v___x_1536_; 
lean_dec_ref_known(v___x_1534_, 1);
if (v_isShared_1532_ == 0)
{
v___x_1536_ = v___x_1531_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_fst_1493_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_snd_1529_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
v_a_1487_ = v___x_1536_;
goto v___jp_1486_;
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_del_object(v___x_1531_);
lean_dec(v_snd_1529_);
lean_dec(v_fst_1493_);
lean_dec(v_a_1478_);
v_a_1538_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1534_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1534_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
}
v___jp_1486_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_unsigned_to_nat(1u);
v___x_1489_ = lean_nat_add(v_a_1478_, v___x_1488_);
lean_dec(v_a_1478_);
v_a_1478_ = v___x_1489_;
v_b_1479_ = v_a_1487_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___boxed(lean_object* v_upperBound_1548_, lean_object* v_a_1549_, lean_object* v_b_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_upperBound_1548_, v_a_1549_, v_b_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec(v_upperBound_1548_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(lean_object* v_ctorType_1558_, lean_object* v_numParams_1559_, lean_object* v_numNewFields_1560_, lean_object* v_oldFields_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_unsigned_to_nat(0u);
v___x_1569_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_numParams_1559_, v___x_1568_, v_ctorType_1558_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
v___x_1571_ = lean_array_get_size(v_oldFields_1561_);
v___x_1572_ = lean_nat_add(v___x_1571_, v_numNewFields_1560_);
v___x_1573_ = lean_mk_empty_array_with_capacity(v___x_1572_);
lean_dec(v___x_1572_);
v___x_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1574_, 0, v_a_1570_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_numNewFields_1560_, v___x_1568_, v___x_1574_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1585_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1578_ = v___x_1575_;
v_isShared_1579_ = v_isSharedCheck_1585_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1575_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1585_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v_snd_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
v_snd_1580_ = lean_ctor_get(v_a_1576_, 1);
lean_inc(v_snd_1580_);
lean_dec(v_a_1576_);
v___x_1581_ = l_Array_append___redArg(v_snd_1580_, v_oldFields_1561_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v___x_1581_);
v___x_1583_ = v___x_1578_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
v_a_1586_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1575_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1575_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
v_a_1594_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1569_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1569_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields___boxed(lean_object* v_ctorType_1602_, lean_object* v_numParams_1603_, lean_object* v_numNewFields_1604_, lean_object* v_oldFields_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(v_ctorType_1602_, v_numParams_1603_, v_numNewFields_1604_, v_oldFields_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_);
lean_dec(v_a_1610_);
lean_dec_ref(v_a_1609_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
lean_dec(v_a_1606_);
lean_dec_ref(v_oldFields_1605_);
lean_dec(v_numNewFields_1604_);
lean_dec(v_numParams_1603_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1(lean_object* v_upperBound_1613_, lean_object* v_inst_1614_, lean_object* v_R_1615_, lean_object* v_a_1616_, lean_object* v_b_1617_, lean_object* v_c_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_upperBound_1613_, v_a_1616_, v_b_1617_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___boxed(lean_object* v_upperBound_1626_, lean_object* v_inst_1627_, lean_object* v_R_1628_, lean_object* v_a_1629_, lean_object* v_b_1630_, lean_object* v_c_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1(v_upperBound_1626_, v_inst_1627_, v_R_1628_, v_a_1629_, v_b_1630_, v_c_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec(v_upperBound_1626_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2(lean_object* v_upperBound_1639_, lean_object* v_inst_1640_, lean_object* v_R_1641_, lean_object* v_a_1642_, lean_object* v_b_1643_, lean_object* v_c_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_upperBound_1639_, v_a_1642_, v_b_1643_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___boxed(lean_object* v_upperBound_1652_, lean_object* v_inst_1653_, lean_object* v_R_1654_, lean_object* v_a_1655_, lean_object* v_b_1656_, lean_object* v_c_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2(v_upperBound_1652_, v_inst_1653_, v_R_1654_, v_a_1655_, v_b_1656_, v_c_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec(v_upperBound_1652_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(size_t v_sz_1665_, size_t v_i_1666_, lean_object* v_bs_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
uint8_t v___x_1673_; 
v___x_1673_ = lean_usize_dec_lt(v_i_1666_, v_sz_1665_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_bs_1667_);
return v___x_1674_;
}
else
{
lean_object* v_v_1675_; lean_object* v___x_1676_; 
v_v_1675_ = lean_array_uget_borrowed(v_bs_1667_, v_i_1666_);
lean_inc(v_v_1675_);
v___x_1676_ = l_Lean_Compiler_LCNF_Param_toMono___redArg(v_v_1675_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v___x_1678_; lean_object* v_bs_x27_1679_; size_t v___x_1680_; size_t v___x_1681_; lean_object* v___x_1682_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref_known(v___x_1676_, 1);
v___x_1678_ = lean_unsigned_to_nat(0u);
v_bs_x27_1679_ = lean_array_uset(v_bs_1667_, v_i_1666_, v___x_1678_);
v___x_1680_ = ((size_t)1ULL);
v___x_1681_ = lean_usize_add(v_i_1666_, v___x_1680_);
v___x_1682_ = lean_array_uset(v_bs_x27_1679_, v_i_1666_, v_a_1677_);
v_i_1666_ = v___x_1681_;
v_bs_1667_ = v___x_1682_;
goto _start;
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
lean_dec_ref(v_bs_1667_);
v_a_1684_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v___x_1676_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1676_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg___boxed(lean_object* v_sz_1692_, lean_object* v_i_1693_, lean_object* v_bs_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
size_t v_sz_boxed_1700_; size_t v_i_boxed_1701_; lean_object* v_res_1702_; 
v_sz_boxed_1700_ = lean_unbox_usize(v_sz_1692_);
lean_dec(v_sz_1692_);
v_i_boxed_1701_ = lean_unbox_usize(v_i_1693_);
lean_dec(v_i_1693_);
v_res_1702_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_boxed_1700_, v_i_boxed_1701_, v_bs_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec(v___y_1695_);
return v_res_1702_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0(void){
_start:
{
uint8_t v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = 0;
v___x_1704_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(lean_object* v_msg_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v_toApplicative_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1776_; 
v___x_1712_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1713_ = l_StateRefT_x27_instMonad___redArg(v___x_1712_);
v_toApplicative_1714_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1776_ == 0)
{
lean_object* v_unused_1777_; 
v_unused_1777_ = lean_ctor_get(v___x_1713_, 1);
lean_dec(v_unused_1777_);
v___x_1716_ = v___x_1713_;
v_isShared_1717_ = v_isSharedCheck_1776_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_toApplicative_1714_);
lean_dec(v___x_1713_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1776_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v_toFunctor_1718_; lean_object* v_toSeq_1719_; lean_object* v_toSeqLeft_1720_; lean_object* v_toSeqRight_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1774_; 
v_toFunctor_1718_ = lean_ctor_get(v_toApplicative_1714_, 0);
v_toSeq_1719_ = lean_ctor_get(v_toApplicative_1714_, 2);
v_toSeqLeft_1720_ = lean_ctor_get(v_toApplicative_1714_, 3);
v_toSeqRight_1721_ = lean_ctor_get(v_toApplicative_1714_, 4);
v_isSharedCheck_1774_ = !lean_is_exclusive(v_toApplicative_1714_);
if (v_isSharedCheck_1774_ == 0)
{
lean_object* v_unused_1775_; 
v_unused_1775_ = lean_ctor_get(v_toApplicative_1714_, 1);
lean_dec(v_unused_1775_);
v___x_1723_ = v_toApplicative_1714_;
v_isShared_1724_ = v_isSharedCheck_1774_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_toSeqRight_1721_);
lean_inc(v_toSeqLeft_1720_);
lean_inc(v_toSeq_1719_);
lean_inc(v_toFunctor_1718_);
lean_dec(v_toApplicative_1714_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1774_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___f_1725_; lean_object* v___f_1726_; lean_object* v___f_1727_; lean_object* v___f_1728_; lean_object* v___x_1729_; lean_object* v___f_1730_; lean_object* v___f_1731_; lean_object* v___f_1732_; lean_object* v___x_1734_; 
v___f_1725_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1726_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1718_);
v___f_1727_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1727_, 0, v_toFunctor_1718_);
v___f_1728_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1728_, 0, v_toFunctor_1718_);
v___x_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___f_1727_);
lean_ctor_set(v___x_1729_, 1, v___f_1728_);
v___f_1730_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1730_, 0, v_toSeqRight_1721_);
v___f_1731_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1731_, 0, v_toSeqLeft_1720_);
v___f_1732_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1732_, 0, v_toSeq_1719_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 4, v___f_1730_);
lean_ctor_set(v___x_1723_, 3, v___f_1731_);
lean_ctor_set(v___x_1723_, 2, v___f_1732_);
lean_ctor_set(v___x_1723_, 1, v___f_1725_);
lean_ctor_set(v___x_1723_, 0, v___x_1729_);
v___x_1734_ = v___x_1723_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v___f_1725_);
lean_ctor_set(v_reuseFailAlloc_1773_, 2, v___f_1732_);
lean_ctor_set(v_reuseFailAlloc_1773_, 3, v___f_1731_);
lean_ctor_set(v_reuseFailAlloc_1773_, 4, v___f_1730_);
v___x_1734_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1736_; 
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 1, v___f_1726_);
lean_ctor_set(v___x_1716_, 0, v___x_1734_);
v___x_1736_ = v___x_1716_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___f_1726_);
v___x_1736_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1737_; lean_object* v_toApplicative_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1770_; 
v___x_1737_ = l_StateRefT_x27_instMonad___redArg(v___x_1736_);
v_toApplicative_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1770_ == 0)
{
lean_object* v_unused_1771_; 
v_unused_1771_ = lean_ctor_get(v___x_1737_, 1);
lean_dec(v_unused_1771_);
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1770_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_toApplicative_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1770_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v_toFunctor_1742_; lean_object* v_toSeq_1743_; lean_object* v_toSeqLeft_1744_; lean_object* v_toSeqRight_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1768_; 
v_toFunctor_1742_ = lean_ctor_get(v_toApplicative_1738_, 0);
v_toSeq_1743_ = lean_ctor_get(v_toApplicative_1738_, 2);
v_toSeqLeft_1744_ = lean_ctor_get(v_toApplicative_1738_, 3);
v_toSeqRight_1745_ = lean_ctor_get(v_toApplicative_1738_, 4);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_toApplicative_1738_);
if (v_isSharedCheck_1768_ == 0)
{
lean_object* v_unused_1769_; 
v_unused_1769_ = lean_ctor_get(v_toApplicative_1738_, 1);
lean_dec(v_unused_1769_);
v___x_1747_ = v_toApplicative_1738_;
v_isShared_1748_ = v_isSharedCheck_1768_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_toSeqRight_1745_);
lean_inc(v_toSeqLeft_1744_);
lean_inc(v_toSeq_1743_);
lean_inc(v_toFunctor_1742_);
lean_dec(v_toApplicative_1738_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1768_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___f_1749_; lean_object* v___f_1750_; lean_object* v___f_1751_; lean_object* v___f_1752_; lean_object* v___x_1753_; lean_object* v___f_1754_; lean_object* v___f_1755_; lean_object* v___f_1756_; lean_object* v___x_1758_; 
v___f_1749_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1750_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1742_);
v___f_1751_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1751_, 0, v_toFunctor_1742_);
v___f_1752_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1752_, 0, v_toFunctor_1742_);
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___f_1751_);
lean_ctor_set(v___x_1753_, 1, v___f_1752_);
v___f_1754_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1754_, 0, v_toSeqRight_1745_);
v___f_1755_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1755_, 0, v_toSeqLeft_1744_);
v___f_1756_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1756_, 0, v_toSeq_1743_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 4, v___f_1754_);
lean_ctor_set(v___x_1747_, 3, v___f_1755_);
lean_ctor_set(v___x_1747_, 2, v___f_1756_);
lean_ctor_set(v___x_1747_, 1, v___f_1749_);
lean_ctor_set(v___x_1747_, 0, v___x_1753_);
v___x_1758_ = v___x_1747_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v___f_1749_);
lean_ctor_set(v_reuseFailAlloc_1767_, 2, v___f_1756_);
lean_ctor_set(v_reuseFailAlloc_1767_, 3, v___f_1755_);
lean_ctor_set(v_reuseFailAlloc_1767_, 4, v___f_1754_);
v___x_1758_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1760_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 1, v___f_1750_);
lean_ctor_set(v___x_1740_, 0, v___x_1758_);
v___x_1760_ = v___x_1740_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v___f_1750_);
v___x_1760_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_48580__overap_1764_; lean_object* v___x_1765_; 
v___x_1761_ = l_StateRefT_x27_instMonad___redArg(v___x_1760_);
v___x_1762_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0);
v___x_1763_ = l_instInhabitedOfMonad___redArg(v___x_1761_, v___x_1762_);
v___x_48580__overap_1764_ = lean_panic_fn_borrowed(v___x_1763_, v_msg_1705_);
lean_dec(v___x_1763_);
lean_inc(v___y_1710_);
lean_inc_ref(v___y_1709_);
lean_inc(v___y_1708_);
lean_inc_ref(v___y_1707_);
lean_inc(v___y_1706_);
v___x_1765_ = lean_apply_6(v___x_48580__overap_1764_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, lean_box(0));
return v___x_1765_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___boxed(lean_object* v_msg_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v_msg_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__2(lean_object* v_msg_1786_){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0);
v___x_1788_ = lean_panic_fn_borrowed(v___x_1787_, v_msg_1786_);
return v___x_1788_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0(void){
_start:
{
uint8_t v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = 0;
v___x_1790_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(lean_object* v_msg_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v_toApplicative_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1862_; 
v___x_1798_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1799_ = l_StateRefT_x27_instMonad___redArg(v___x_1798_);
v_toApplicative_1800_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; 
v_unused_1863_ = lean_ctor_get(v___x_1799_, 1);
lean_dec(v_unused_1863_);
v___x_1802_ = v___x_1799_;
v_isShared_1803_ = v_isSharedCheck_1862_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_toApplicative_1800_);
lean_dec(v___x_1799_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1862_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v_toFunctor_1804_; lean_object* v_toSeq_1805_; lean_object* v_toSeqLeft_1806_; lean_object* v_toSeqRight_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1860_; 
v_toFunctor_1804_ = lean_ctor_get(v_toApplicative_1800_, 0);
v_toSeq_1805_ = lean_ctor_get(v_toApplicative_1800_, 2);
v_toSeqLeft_1806_ = lean_ctor_get(v_toApplicative_1800_, 3);
v_toSeqRight_1807_ = lean_ctor_get(v_toApplicative_1800_, 4);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_toApplicative_1800_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; 
v_unused_1861_ = lean_ctor_get(v_toApplicative_1800_, 1);
lean_dec(v_unused_1861_);
v___x_1809_ = v_toApplicative_1800_;
v_isShared_1810_ = v_isSharedCheck_1860_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_toSeqRight_1807_);
lean_inc(v_toSeqLeft_1806_);
lean_inc(v_toSeq_1805_);
lean_inc(v_toFunctor_1804_);
lean_dec(v_toApplicative_1800_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1860_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___f_1811_; lean_object* v___f_1812_; lean_object* v___f_1813_; lean_object* v___f_1814_; lean_object* v___x_1815_; lean_object* v___f_1816_; lean_object* v___f_1817_; lean_object* v___f_1818_; lean_object* v___x_1820_; 
v___f_1811_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1812_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1804_);
v___f_1813_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1813_, 0, v_toFunctor_1804_);
v___f_1814_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1814_, 0, v_toFunctor_1804_);
v___x_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___f_1813_);
lean_ctor_set(v___x_1815_, 1, v___f_1814_);
v___f_1816_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1816_, 0, v_toSeqRight_1807_);
v___f_1817_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1817_, 0, v_toSeqLeft_1806_);
v___f_1818_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1818_, 0, v_toSeq_1805_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 4, v___f_1816_);
lean_ctor_set(v___x_1809_, 3, v___f_1817_);
lean_ctor_set(v___x_1809_, 2, v___f_1818_);
lean_ctor_set(v___x_1809_, 1, v___f_1811_);
lean_ctor_set(v___x_1809_, 0, v___x_1815_);
v___x_1820_ = v___x_1809_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1815_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v___f_1811_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v___f_1818_);
lean_ctor_set(v_reuseFailAlloc_1859_, 3, v___f_1817_);
lean_ctor_set(v_reuseFailAlloc_1859_, 4, v___f_1816_);
v___x_1820_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1822_; 
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 1, v___f_1812_);
lean_ctor_set(v___x_1802_, 0, v___x_1820_);
v___x_1822_ = v___x_1802_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1820_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v___f_1812_);
v___x_1822_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1823_; lean_object* v_toApplicative_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1856_; 
v___x_1823_ = l_StateRefT_x27_instMonad___redArg(v___x_1822_);
v_toApplicative_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1856_ == 0)
{
lean_object* v_unused_1857_; 
v_unused_1857_ = lean_ctor_get(v___x_1823_, 1);
lean_dec(v_unused_1857_);
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1856_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_toApplicative_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1856_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v_toFunctor_1828_; lean_object* v_toSeq_1829_; lean_object* v_toSeqLeft_1830_; lean_object* v_toSeqRight_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1854_; 
v_toFunctor_1828_ = lean_ctor_get(v_toApplicative_1824_, 0);
v_toSeq_1829_ = lean_ctor_get(v_toApplicative_1824_, 2);
v_toSeqLeft_1830_ = lean_ctor_get(v_toApplicative_1824_, 3);
v_toSeqRight_1831_ = lean_ctor_get(v_toApplicative_1824_, 4);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_toApplicative_1824_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; 
v_unused_1855_ = lean_ctor_get(v_toApplicative_1824_, 1);
lean_dec(v_unused_1855_);
v___x_1833_ = v_toApplicative_1824_;
v_isShared_1834_ = v_isSharedCheck_1854_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_toSeqRight_1831_);
lean_inc(v_toSeqLeft_1830_);
lean_inc(v_toSeq_1829_);
lean_inc(v_toFunctor_1828_);
lean_dec(v_toApplicative_1824_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1854_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___f_1835_; lean_object* v___f_1836_; lean_object* v___f_1837_; lean_object* v___f_1838_; lean_object* v___x_1839_; lean_object* v___f_1840_; lean_object* v___f_1841_; lean_object* v___f_1842_; lean_object* v___x_1844_; 
v___f_1835_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1836_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1828_);
v___f_1837_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1837_, 0, v_toFunctor_1828_);
v___f_1838_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1838_, 0, v_toFunctor_1828_);
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___f_1837_);
lean_ctor_set(v___x_1839_, 1, v___f_1838_);
v___f_1840_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1840_, 0, v_toSeqRight_1831_);
v___f_1841_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1841_, 0, v_toSeqLeft_1830_);
v___f_1842_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1842_, 0, v_toSeq_1829_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 4, v___f_1840_);
lean_ctor_set(v___x_1833_, 3, v___f_1841_);
lean_ctor_set(v___x_1833_, 2, v___f_1842_);
lean_ctor_set(v___x_1833_, 1, v___f_1835_);
lean_ctor_set(v___x_1833_, 0, v___x_1839_);
v___x_1844_ = v___x_1833_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v___f_1835_);
lean_ctor_set(v_reuseFailAlloc_1853_, 2, v___f_1842_);
lean_ctor_set(v_reuseFailAlloc_1853_, 3, v___f_1841_);
lean_ctor_set(v_reuseFailAlloc_1853_, 4, v___f_1840_);
v___x_1844_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1846_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 1, v___f_1836_);
lean_ctor_set(v___x_1826_, 0, v___x_1844_);
v___x_1846_ = v___x_1826_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1844_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v___f_1836_);
v___x_1846_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_48595__overap_1850_; lean_object* v___x_1851_; 
v___x_1847_ = l_StateRefT_x27_instMonad___redArg(v___x_1846_);
v___x_1848_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_1849_ = l_instInhabitedOfMonad___redArg(v___x_1847_, v___x_1848_);
v___x_48595__overap_1850_ = lean_panic_fn_borrowed(v___x_1849_, v_msg_1791_);
lean_dec(v___x_1849_);
lean_inc(v___y_1796_);
lean_inc_ref(v___y_1795_);
lean_inc(v___y_1794_);
lean_inc_ref(v___y_1793_);
lean_inc(v___y_1792_);
v___x_1851_ = lean_apply_6(v___x_48595__overap_1850_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, lean_box(0));
return v___x_1851_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___boxed(lean_object* v_msg_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(v_msg_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono(lean_object* v_decl_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_){
_start:
{
lean_object* v_params_1881_; lean_object* v_type_1882_; lean_object* v_value_1883_; lean_object* v___x_1884_; 
v_params_1881_ = lean_ctor_get(v_decl_1874_, 2);
v_type_1882_ = lean_ctor_get(v_decl_1874_, 3);
v_value_1883_ = lean_ctor_get(v_decl_1874_, 4);
lean_inc_ref(v_type_1882_);
v___x_1884_ = l_Lean_Compiler_LCNF_toMonoType(v_type_1882_, v_a_1878_, v_a_1879_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; size_t v_sz_1886_; size_t v___x_1887_; lean_object* v___x_1888_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref_known(v___x_1884_, 1);
v_sz_1886_ = lean_array_size(v_params_1881_);
v___x_1887_ = ((size_t)0ULL);
lean_inc_ref(v_params_1881_);
v___x_1888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_1886_, v___x_1887_, v_params_1881_, v_a_1875_, v_a_1877_, v_a_1878_, v_a_1879_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1890_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref_known(v___x_1888_, 1);
lean_inc_ref(v_value_1883_);
v___x_1890_ = l_Lean_Compiler_LCNF_Code_toMono(v_value_1883_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; uint8_t v___x_1892_; lean_object* v___x_1893_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc(v_a_1891_);
lean_dec_ref_known(v___x_1890_, 1);
v___x_1892_ = 0;
v___x_1893_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1892_, v_decl_1874_, v_a_1885_, v_a_1889_, v_a_1891_, v_a_1877_);
return v___x_1893_;
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec(v_a_1889_);
lean_dec(v_a_1885_);
lean_dec_ref(v_decl_1874_);
v_a_1894_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1890_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1890_);
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
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec(v_a_1885_);
lean_dec_ref(v_decl_1874_);
v_a_1902_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1888_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1888_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_dec_ref(v_decl_1874_);
v_a_1910_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1884_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1884_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__2(void){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1920_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_1921_ = lean_unsigned_to_nat(9u);
v___x_1922_ = lean_unsigned_to_nat(641u);
v___x_1923_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__1));
v___x_1924_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__0));
v___x_1925_ = l_mkPanicMessageWithDecl(v___x_1924_, v___x_1923_, v___x_1922_, v___x_1921_, v___x_1920_);
return v___x_1925_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__4(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1928_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__3));
v___x_1929_ = lean_unsigned_to_nat(66u);
v___x_1930_ = lean_unsigned_to_nat(441u);
v___x_1931_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_1932_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_1933_ = l_mkPanicMessageWithDecl(v___x_1932_, v___x_1931_, v___x_1930_, v___x_1929_, v___x_1928_);
return v___x_1933_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__5(void){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1934_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_1935_ = lean_unsigned_to_nat(27u);
v___x_1936_ = lean_unsigned_to_nat(393u);
v___x_1937_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_1938_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_1939_ = l_mkPanicMessageWithDecl(v___x_1938_, v___x_1937_, v___x_1936_, v___x_1935_, v___x_1934_);
return v___x_1939_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__1));
v___x_1953_ = lean_unsigned_to_nat(70u);
v___x_1954_ = lean_unsigned_to_nat(451u);
v___x_1955_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_1956_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_1957_ = l_mkPanicMessageWithDecl(v___x_1956_, v___x_1955_, v___x_1954_, v___x_1953_, v___x_1952_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(lean_object* v___x_1961_, uint8_t v___x_1962_, size_t v_sz_1963_, size_t v_i_1964_, lean_object* v_bs_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
uint8_t v___x_1972_; 
v___x_1972_ = lean_usize_dec_lt(v_i_1964_, v_sz_1963_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; 
lean_dec_ref(v___x_1961_);
v___x_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1973_, 0, v_bs_1965_);
return v___x_1973_;
}
else
{
lean_object* v_v_1974_; lean_object* v___x_1975_; lean_object* v_bs_x27_1976_; lean_object* v_a_1978_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; 
v_v_1974_ = lean_array_uget(v_bs_1965_, v_i_1964_);
v___x_1975_ = lean_unsigned_to_nat(0u);
v_bs_x27_1976_ = lean_array_uset(v_bs_1965_, v_i_1964_, v___x_1975_);
if (lean_obj_tag(v_v_1974_) == 0)
{
lean_object* v_ctorName_2000_; lean_object* v_params_2001_; lean_object* v_code_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2040_; 
v_ctorName_2000_ = lean_ctor_get(v_v_1974_, 0);
v_params_2001_ = lean_ctor_get(v_v_1974_, 1);
v_code_2002_ = lean_ctor_get(v_v_1974_, 2);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_v_1974_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2004_ = v_v_1974_;
v_isShared_2005_ = v_isSharedCheck_2040_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_code_2002_);
lean_inc(v_params_2001_);
lean_inc(v_ctorName_2000_);
lean_dec(v_v_1974_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2040_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4));
v___x_2007_ = l_Lean_Name_append(v_ctorName_2000_, v___x_2006_);
lean_inc(v___x_2007_);
lean_inc_ref(v___x_1961_);
v___x_2008_ = l_Lean_Environment_find_x3f(v___x_1961_, v___x_2007_, v___x_1962_);
if (lean_obj_tag(v___x_2008_) == 1)
{
lean_object* v_val_2009_; 
v_val_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_val_2009_);
lean_dec_ref_known(v___x_2008_, 1);
if (lean_obj_tag(v_val_2009_) == 6)
{
lean_object* v_val_2010_; lean_object* v_toConstantVal_2011_; lean_object* v_numParams_2012_; lean_object* v_numFields_2013_; lean_object* v_type_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v_val_2010_ = lean_ctor_get(v_val_2009_, 0);
lean_inc_ref(v_val_2010_);
lean_dec_ref_known(v_val_2009_, 1);
v_toConstantVal_2011_ = lean_ctor_get(v_val_2010_, 0);
lean_inc_ref(v_toConstantVal_2011_);
v_numParams_2012_ = lean_ctor_get(v_val_2010_, 3);
lean_inc(v_numParams_2012_);
v_numFields_2013_ = lean_ctor_get(v_val_2010_, 4);
lean_inc(v_numFields_2013_);
lean_dec_ref(v_val_2010_);
v_type_2014_ = lean_ctor_get(v_toConstantVal_2011_, 2);
lean_inc_ref(v_type_2014_);
lean_dec_ref(v_toConstantVal_2011_);
v___x_2015_ = lean_array_get_size(v_params_2001_);
v___x_2016_ = lean_nat_sub(v_numFields_2013_, v___x_2015_);
lean_dec(v_numFields_2013_);
v___x_2017_ = l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(v_type_2014_, v_numParams_2012_, v___x_2016_, v_params_2001_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec_ref(v_params_2001_);
lean_dec(v___x_2016_);
lean_dec(v_numParams_2012_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2019_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref_known(v___x_2017_, 1);
v___x_2019_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2002_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2022_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2019_, 1);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 2, v_a_2020_);
lean_ctor_set(v___x_2004_, 1, v_a_2018_);
lean_ctor_set(v___x_2004_, 0, v___x_2007_);
v___x_2022_ = v___x_2004_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_a_2018_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v_a_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
v_a_1978_ = v___x_2022_;
goto v___jp_1977_;
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec(v_a_2018_);
lean_dec(v___x_2007_);
lean_del_object(v___x_2004_);
lean_dec_ref(v_bs_x27_1976_);
lean_dec_ref(v___x_1961_);
v_a_2024_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_2019_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2019_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec(v___x_2007_);
lean_del_object(v___x_2004_);
lean_dec_ref(v_code_2002_);
lean_dec_ref(v_bs_x27_1976_);
lean_dec_ref(v___x_1961_);
v_a_2032_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2017_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2017_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
else
{
lean_dec(v_val_2009_);
lean_dec(v___x_2007_);
lean_del_object(v___x_2004_);
lean_dec_ref(v_code_2002_);
lean_dec_ref(v_params_2001_);
v___y_1984_ = v___y_1966_;
v___y_1985_ = v___y_1967_;
v___y_1986_ = v___y_1968_;
v___y_1987_ = v___y_1969_;
v___y_1988_ = v___y_1970_;
goto v___jp_1983_;
}
}
else
{
lean_dec(v___x_2008_);
lean_dec(v___x_2007_);
lean_del_object(v___x_2004_);
lean_dec_ref(v_code_2002_);
lean_dec_ref(v_params_2001_);
v___y_1984_ = v___y_1966_;
v___y_1985_ = v___y_1967_;
v___y_1986_ = v___y_1968_;
v___y_1987_ = v___y_1969_;
v___y_1988_ = v___y_1970_;
goto v___jp_1983_;
}
}
}
else
{
lean_object* v_code_2041_; lean_object* v___x_2042_; 
v_code_2041_ = lean_ctor_get(v_v_1974_, 0);
lean_inc_ref(v_code_2041_);
v___x_2042_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2041_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2044_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2042_, 1);
v___x_2044_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_1974_, v_a_2043_);
v_a_1978_ = v___x_2044_;
goto v___jp_1977_;
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec_ref_known(v_v_1974_, 1);
lean_dec_ref(v_bs_x27_1976_);
lean_dec_ref(v___x_1961_);
v_a_2045_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2042_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2042_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
v___jp_1977_:
{
size_t v___x_1979_; size_t v___x_1980_; lean_object* v___x_1981_; 
v___x_1979_ = ((size_t)1ULL);
v___x_1980_ = lean_usize_add(v_i_1964_, v___x_1979_);
v___x_1981_ = lean_array_uset(v_bs_x27_1976_, v_i_1964_, v_a_1978_);
v_i_1964_ = v___x_1980_;
v_bs_1965_ = v___x_1981_;
goto _start;
}
v___jp_1983_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2);
v___x_1990_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(v___x_1989_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1990_, 1);
v_a_1978_ = v_a_1991_;
goto v___jp_1977_;
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec_ref(v_bs_x27_1976_);
lean_dec_ref(v___x_1961_);
v_a_1992_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1990_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1990_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__1(void){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2098_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2099_ = lean_unsigned_to_nat(2u);
v___x_2100_ = lean_unsigned_to_nat(376u);
v___x_2101_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_2102_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2103_ = l_mkPanicMessageWithDecl(v___x_2102_, v___x_2101_, v___x_2100_, v___x_2099_, v___x_2098_);
return v___x_2103_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__3(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2105_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__2));
v___x_2106_ = lean_unsigned_to_nat(2u);
v___x_2107_ = lean_unsigned_to_nat(378u);
v___x_2108_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_2109_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2110_ = l_mkPanicMessageWithDecl(v___x_2109_, v___x_2108_, v___x_2107_, v___x_2106_, v___x_2105_);
return v___x_2110_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__5(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2112_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__4));
v___x_2113_ = lean_unsigned_to_nat(2u);
v___x_2114_ = lean_unsigned_to_nat(379u);
v___x_2115_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_2116_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2117_ = l_mkPanicMessageWithDecl(v___x_2116_, v___x_2115_, v___x_2114_, v___x_2113_, v___x_2112_);
return v___x_2117_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__6(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2118_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_2119_ = lean_unsigned_to_nat(41u);
v___x_2120_ = lean_unsigned_to_nat(377u);
v___x_2121_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_2122_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2123_ = l_mkPanicMessageWithDecl(v___x_2122_, v___x_2121_, v___x_2120_, v___x_2119_, v___x_2118_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono(lean_object* v_info_2124_, lean_object* v_c_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v_discr_2132_; lean_object* v_alts_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2211_; 
v_discr_2132_ = lean_ctor_get(v_c_2125_, 2);
v_alts_2133_ = lean_ctor_get(v_c_2125_, 3);
v_isSharedCheck_2211_ = !lean_is_exclusive(v_c_2125_);
if (v_isSharedCheck_2211_ == 0)
{
lean_object* v_unused_2212_; lean_object* v_unused_2213_; 
v_unused_2212_ = lean_ctor_get(v_c_2125_, 1);
lean_dec(v_unused_2212_);
v_unused_2213_ = lean_ctor_get(v_c_2125_, 0);
lean_dec(v_unused_2213_);
v___x_2135_ = v_c_2125_;
v_isShared_2136_ = v_isSharedCheck_2211_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_alts_2133_);
lean_inc(v_discr_2132_);
lean_dec(v_c_2125_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2211_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2137_ = lean_array_get_size(v_alts_2133_);
v___x_2138_ = lean_unsigned_to_nat(1u);
v___x_2139_ = lean_nat_dec_eq(v___x_2137_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
lean_del_object(v___x_2135_);
lean_dec_ref(v_alts_2133_);
lean_dec(v_discr_2132_);
v___x_2140_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__1, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__1_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__1);
v___x_2141_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2140_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
return v___x_2141_;
}
else
{
uint8_t v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2142_ = 0;
v___x_2143_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2144_ = lean_unsigned_to_nat(0u);
v___x_2145_ = lean_array_get(v___x_2143_, v_alts_2133_, v___x_2144_);
lean_dec_ref(v_alts_2133_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_ctorName_2146_; lean_object* v_params_2147_; lean_object* v_code_2148_; lean_object* v_ctorName_2149_; lean_object* v_fieldIdx_2150_; uint8_t v___x_2151_; 
v_ctorName_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_ctorName_2146_);
v_params_2147_ = lean_ctor_get(v___x_2145_, 1);
lean_inc_ref(v_params_2147_);
v_code_2148_ = lean_ctor_get(v___x_2145_, 2);
lean_inc_ref(v_code_2148_);
lean_dec_ref_known(v___x_2145_, 3);
v_ctorName_2149_ = lean_ctor_get(v_info_2124_, 0);
v_fieldIdx_2150_ = lean_ctor_get(v_info_2124_, 2);
v___x_2151_ = lean_name_eq(v_ctorName_2146_, v_ctorName_2149_);
lean_dec(v_ctorName_2146_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
lean_dec_ref(v_code_2148_);
lean_dec_ref(v_params_2147_);
lean_del_object(v___x_2135_);
lean_dec(v_discr_2132_);
v___x_2152_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__3, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__3_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__3);
v___x_2153_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2152_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
return v___x_2153_;
}
else
{
lean_object* v___x_2154_; uint8_t v___x_2155_; 
v___x_2154_ = lean_array_get_size(v_params_2147_);
v___x_2155_ = lean_nat_dec_lt(v_fieldIdx_2150_, v___x_2154_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
lean_dec_ref(v_code_2148_);
lean_dec_ref(v_params_2147_);
lean_del_object(v___x_2135_);
lean_dec(v_discr_2132_);
v___x_2156_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__5, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__5_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__5);
v___x_2157_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2156_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
return v___x_2157_;
}
else
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2159_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2142_, v_params_2147_, v_a_2128_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_p_2160_; lean_object* v_fvarId_2161_; lean_object* v_binderName_2162_; lean_object* v_type_2163_; lean_object* v___x_2164_; 
lean_dec_ref_known(v___x_2159_, 1);
v_p_2160_ = lean_array_get(v___x_2158_, v_params_2147_, v_fieldIdx_2150_);
lean_dec_ref(v_params_2147_);
v_fvarId_2161_ = lean_ctor_get(v_p_2160_, 0);
lean_inc(v_fvarId_2161_);
v_binderName_2162_ = lean_ctor_get(v_p_2160_, 1);
lean_inc(v_binderName_2162_);
v_type_2163_ = lean_ctor_get(v_p_2160_, 2);
lean_inc_ref(v_type_2163_);
lean_dec(v_p_2160_);
v___x_2164_ = l_Lean_Compiler_LCNF_toMonoType(v_type_2163_, v_a_2129_, v_a_2130_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2166_; lean_object* v_lctx_2167_; lean_object* v_nextIdx_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2192_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref_known(v___x_2164_, 1);
v___x_2166_ = lean_st_ref_take(v_a_2128_);
v_lctx_2167_ = lean_ctor_get(v___x_2166_, 0);
v_nextIdx_2168_ = lean_ctor_get(v___x_2166_, 1);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2170_ = v___x_2166_;
v_isShared_2171_ = v_isSharedCheck_2192_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_nextIdx_2168_);
lean_inc(v_lctx_2167_);
lean_dec(v___x_2166_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2192_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2175_; 
v___x_2172_ = ((lean_object*)(l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0));
v___x_2173_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2173_, 0, v_discr_2132_);
lean_ctor_set(v___x_2173_, 1, v___x_2172_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 3, v___x_2173_);
lean_ctor_set(v___x_2135_, 2, v_a_2165_);
lean_ctor_set(v___x_2135_, 1, v_binderName_2162_);
lean_ctor_set(v___x_2135_, 0, v_fvarId_2161_);
v___x_2175_ = v___x_2135_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_fvarId_2161_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_binderName_2162_);
lean_ctor_set(v_reuseFailAlloc_2191_, 2, v_a_2165_);
lean_ctor_set(v_reuseFailAlloc_2191_, 3, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2176_; lean_object* v___x_2178_; 
lean_inc_ref(v___x_2175_);
v___x_2176_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2142_, v_lctx_2167_, v___x_2175_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2176_);
v___x_2178_ = v___x_2170_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2176_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_nextIdx_2168_);
v___x_2178_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = lean_st_ref_put(v_a_2128_, v___x_2178_);
v___x_2180_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2148_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2189_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2183_ = v___x_2180_;
v_isShared_2184_ = v_isSharedCheck_2189_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2189_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2185_; lean_object* v___x_2187_; 
v___x_2185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2175_);
lean_ctor_set(v___x_2185_, 1, v_a_2181_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v___x_2185_);
v___x_2187_ = v___x_2183_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
else
{
lean_dec_ref(v___x_2175_);
return v___x_2180_;
}
}
}
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec(v_binderName_2162_);
lean_dec(v_fvarId_2161_);
lean_dec_ref(v_code_2148_);
lean_del_object(v___x_2135_);
lean_dec(v_discr_2132_);
v_a_2193_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2164_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2164_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec_ref(v_code_2148_);
lean_dec_ref(v_params_2147_);
lean_del_object(v___x_2135_);
lean_dec(v_discr_2132_);
v_a_2201_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2159_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2159_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
}
else
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
lean_dec(v___x_2145_);
lean_del_object(v___x_2135_);
lean_dec(v_discr_2132_);
v___x_2209_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__6, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__6_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__6);
v___x_2210_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2209_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
return v___x_2210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(size_t v_sz_2214_, size_t v_i_2215_, lean_object* v_bs_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
uint8_t v___x_2223_; 
v___x_2223_ = lean_usize_dec_lt(v_i_2215_, v_sz_2214_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2224_, 0, v_bs_2216_);
return v___x_2224_;
}
else
{
lean_object* v_v_2225_; lean_object* v___x_2226_; lean_object* v_bs_x27_2227_; lean_object* v_a_2229_; 
v_v_2225_ = lean_array_uget(v_bs_2216_, v_i_2215_);
v___x_2226_ = lean_unsigned_to_nat(0u);
v_bs_x27_2227_ = lean_array_uset(v_bs_2216_, v_i_2215_, v___x_2226_);
if (lean_obj_tag(v_v_2225_) == 0)
{
lean_object* v_params_2234_; lean_object* v_code_2235_; size_t v_sz_2236_; size_t v___x_2237_; lean_object* v___x_2238_; 
v_params_2234_ = lean_ctor_get(v_v_2225_, 1);
v_code_2235_ = lean_ctor_get(v_v_2225_, 2);
v_sz_2236_ = lean_array_size(v_params_2234_);
v___x_2237_ = ((size_t)0ULL);
lean_inc_ref(v_params_2234_);
v___x_2238_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_2236_, v___x_2237_, v_params_2234_, v___y_2217_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2240_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2238_, 1);
lean_inc_ref(v_code_2235_);
v___x_2240_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2235_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; uint8_t v___x_2242_; lean_object* v___x_2243_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
lean_dec_ref_known(v___x_2240_, 1);
v___x_2242_ = 0;
v___x_2243_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v___x_2242_, v_v_2225_, v_a_2239_, v_a_2241_);
v_a_2229_ = v___x_2243_;
goto v___jp_2228_;
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_dec(v_a_2239_);
lean_dec_ref_known(v_v_2225_, 3);
lean_dec_ref(v_bs_x27_2227_);
v_a_2244_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2240_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2240_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
else
{
lean_dec_ref_known(v_v_2225_, 3);
lean_dec_ref(v_bs_x27_2227_);
return v___x_2238_;
}
}
else
{
lean_object* v_code_2252_; lean_object* v___x_2253_; 
v_code_2252_ = lean_ctor_get(v_v_2225_, 0);
lean_inc_ref(v_code_2252_);
v___x_2253_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2252_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v___x_2255_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2254_);
lean_dec_ref_known(v___x_2253_, 1);
v___x_2255_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_2225_, v_a_2254_);
v_a_2229_ = v___x_2255_;
goto v___jp_2228_;
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec_ref_known(v_v_2225_, 1);
lean_dec_ref(v_bs_x27_2227_);
v_a_2256_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2253_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2253_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
v___jp_2228_:
{
size_t v___x_2230_; size_t v___x_2231_; lean_object* v___x_2232_; 
v___x_2230_ = ((size_t)1ULL);
v___x_2231_ = lean_usize_add(v_i_2215_, v___x_2230_);
v___x_2232_ = lean_array_uset(v_bs_x27_2227_, v_i_2215_, v_a_2229_);
v_i_2215_ = v___x_2231_;
v_bs_2216_ = v___x_2232_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2265_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2266_ = lean_unsigned_to_nat(2u);
v___x_2267_ = lean_unsigned_to_nat(365u);
v___x_2268_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0));
v___x_2269_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2270_ = l_mkPanicMessageWithDecl(v___x_2269_, v___x_2268_, v___x_2267_, v___x_2266_, v___x_2265_);
return v___x_2270_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2275_ = lean_box(0);
v___x_2276_ = lean_unsigned_to_nat(2u);
v___x_2277_ = lean_mk_empty_array_with_capacity(v___x_2276_);
v___x_2278_ = lean_array_push(v___x_2277_, v___x_2275_);
return v___x_2278_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2279_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_2280_ = lean_unsigned_to_nat(34u);
v___x_2281_ = lean_unsigned_to_nat(366u);
v___x_2282_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0));
v___x_2283_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2284_ = l_mkPanicMessageWithDecl(v___x_2283_, v___x_2282_, v___x_2281_, v___x_2280_, v___x_2279_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg(lean_object* v_c_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_discr_2292_; lean_object* v_alts_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2362_; 
v_discr_2292_ = lean_ctor_get(v_c_2285_, 2);
v_alts_2293_ = lean_ctor_get(v_c_2285_, 3);
v_isSharedCheck_2362_ = !lean_is_exclusive(v_c_2285_);
if (v_isSharedCheck_2362_ == 0)
{
lean_object* v_unused_2363_; lean_object* v_unused_2364_; 
v_unused_2363_ = lean_ctor_get(v_c_2285_, 1);
lean_dec(v_unused_2363_);
v_unused_2364_ = lean_ctor_get(v_c_2285_, 0);
lean_dec(v_unused_2364_);
v___x_2295_ = v_c_2285_;
v_isShared_2296_ = v_isSharedCheck_2362_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_alts_2293_);
lean_inc(v_discr_2292_);
lean_dec(v_c_2285_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2362_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; 
v___x_2297_ = lean_array_get_size(v_alts_2293_);
v___x_2298_ = lean_unsigned_to_nat(1u);
v___x_2299_ = lean_nat_dec_eq(v___x_2297_, v___x_2298_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_del_object(v___x_2295_);
lean_dec_ref(v_alts_2293_);
lean_dec(v_discr_2292_);
v___x_2300_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1);
v___x_2301_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2300_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
return v___x_2301_;
}
else
{
uint8_t v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2302_ = 0;
v___x_2303_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2304_ = lean_unsigned_to_nat(0u);
v___x_2305_ = lean_array_get(v___x_2303_, v_alts_2293_, v___x_2304_);
lean_dec_ref(v_alts_2293_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_params_2306_; lean_object* v_code_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2358_; 
v_params_2306_ = lean_ctor_get(v___x_2305_, 1);
v_code_2307_ = lean_ctor_get(v___x_2305_, 2);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2358_ == 0)
{
lean_object* v_unused_2359_; 
v_unused_2359_ = lean_ctor_get(v___x_2305_, 0);
lean_dec(v_unused_2359_);
v___x_2309_ = v___x_2305_;
v_isShared_2310_ = v_isSharedCheck_2358_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_code_2307_);
lean_inc(v_params_2306_);
lean_dec(v___x_2305_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2358_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2302_, v_params_2306_, v_a_2288_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v_fvarId_2315_; lean_object* v_binderName_2316_; lean_object* v_lctx_2317_; lean_object* v_nextIdx_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2349_; 
lean_dec_ref_known(v___x_2311_, 1);
v___x_2312_ = lean_st_ref_take(v_a_2288_);
v___x_2313_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2314_ = lean_array_get(v___x_2313_, v_params_2306_, v___x_2304_);
lean_dec_ref(v_params_2306_);
v_fvarId_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_fvarId_2315_);
v_binderName_2316_ = lean_ctor_get(v___x_2314_, 1);
lean_inc(v_binderName_2316_);
lean_dec(v___x_2314_);
v_lctx_2317_ = lean_ctor_get(v___x_2312_, 0);
v_nextIdx_2318_ = lean_ctor_get(v___x_2312_, 1);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2320_ = v___x_2312_;
v_isShared_2321_ = v_isSharedCheck_2349_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_nextIdx_2318_);
lean_inc(v_lctx_2317_);
lean_dec(v___x_2312_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2349_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2328_; 
v___x_2322_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__4));
v___x_2323_ = lean_box(0);
v___x_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2324_, 0, v_discr_2292_);
v___x_2325_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5);
v___x_2326_ = lean_array_push(v___x_2325_, v___x_2324_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set_tag(v___x_2309_, 3);
lean_ctor_set(v___x_2309_, 2, v___x_2326_);
lean_ctor_set(v___x_2309_, 1, v___x_2323_);
lean_ctor_set(v___x_2309_, 0, v___x_2322_);
v___x_2328_ = v___x_2309_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2322_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v___x_2323_);
lean_ctor_set(v_reuseFailAlloc_2348_, 2, v___x_2326_);
v___x_2328_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2329_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 3, v___x_2328_);
lean_ctor_set(v___x_2295_, 2, v___x_2329_);
lean_ctor_set(v___x_2295_, 1, v_binderName_2316_);
lean_ctor_set(v___x_2295_, 0, v_fvarId_2315_);
v___x_2331_ = v___x_2295_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_fvarId_2315_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_binderName_2316_);
lean_ctor_set(v_reuseFailAlloc_2347_, 2, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2347_, 3, v___x_2328_);
v___x_2331_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2332_; lean_object* v___x_2334_; 
lean_inc_ref(v___x_2331_);
v___x_2332_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2302_, v_lctx_2317_, v___x_2331_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v___x_2332_);
v___x_2334_ = v___x_2320_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2332_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v_nextIdx_2318_);
v___x_2334_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = lean_st_ref_put(v_a_2288_, v___x_2334_);
v___x_2336_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2307_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2345_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2345_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2345_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2341_; lean_object* v___x_2343_; 
v___x_2341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2331_);
lean_ctor_set(v___x_2341_, 1, v_a_2337_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2341_);
v___x_2343_ = v___x_2339_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2341_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
else
{
lean_dec_ref(v___x_2331_);
return v___x_2336_;
}
}
}
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_del_object(v___x_2309_);
lean_dec_ref(v_code_2307_);
lean_dec_ref(v_params_2306_);
lean_del_object(v___x_2295_);
lean_dec(v_discr_2292_);
v_a_2350_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2311_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2311_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
}
else
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
lean_dec(v___x_2305_);
lean_del_object(v___x_2295_);
lean_dec(v_discr_2292_);
v___x_2360_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5);
v___x_2361_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2360_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
return v___x_2361_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2366_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2367_ = lean_unsigned_to_nat(2u);
v___x_2368_ = lean_unsigned_to_nat(345u);
v___x_2369_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0));
v___x_2370_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2371_ = l_mkPanicMessageWithDecl(v___x_2370_, v___x_2369_, v___x_2368_, v___x_2367_, v___x_2366_);
return v___x_2371_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8(void){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2378_ = lean_box(0);
v___x_2379_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__7));
v___x_2380_ = l_Lean_Expr_const___override(v___x_2379_, v___x_2378_);
return v___x_2380_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9(void){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2381_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_2382_ = lean_unsigned_to_nat(34u);
v___x_2383_ = lean_unsigned_to_nat(346u);
v___x_2384_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0));
v___x_2385_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2386_ = l_mkPanicMessageWithDecl(v___x_2385_, v___x_2384_, v___x_2383_, v___x_2382_, v___x_2381_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg(lean_object* v_c_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v_discr_2394_; lean_object* v_alts_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; uint8_t v___x_2398_; 
v_discr_2394_ = lean_ctor_get(v_c_2387_, 2);
v_alts_2395_ = lean_ctor_get(v_c_2387_, 3);
v___x_2396_ = lean_array_get_size(v_alts_2395_);
v___x_2397_ = lean_unsigned_to_nat(1u);
v___x_2398_ = lean_nat_dec_eq(v___x_2396_, v___x_2397_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1);
v___x_2400_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2399_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
return v___x_2400_;
}
else
{
uint8_t v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2401_ = 0;
v___x_2402_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2403_ = lean_unsigned_to_nat(0u);
v___x_2404_ = lean_array_get(v___x_2402_, v_alts_2395_, v___x_2403_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_params_2405_; lean_object* v_code_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2503_; 
v_params_2405_ = lean_ctor_get(v___x_2404_, 1);
v_code_2406_ = lean_ctor_get(v___x_2404_, 2);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2503_ == 0)
{
lean_object* v_unused_2504_; 
v_unused_2504_ = lean_ctor_get(v___x_2404_, 0);
lean_dec(v_unused_2504_);
v___x_2408_ = v___x_2404_;
v_isShared_2409_ = v_isSharedCheck_2503_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_code_2406_);
lean_inc(v_params_2405_);
lean_dec(v___x_2404_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2503_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2410_; 
v___x_2410_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2401_, v_params_2405_, v_a_2390_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
lean_dec_ref_known(v___x_2410_, 1);
v___x_2411_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3));
v___x_2412_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2411_, v_a_2390_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2421_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2413_);
lean_dec_ref_known(v___x_2412_, 1);
v___x_2414_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
lean_inc(v_discr_2394_);
v___x_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2415_, 0, v_discr_2394_);
v___x_2416_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5));
v___x_2417_ = lean_box(0);
v___x_2418_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5);
v___x_2419_ = lean_array_push(v___x_2418_, v___x_2415_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set_tag(v___x_2408_, 3);
lean_ctor_set(v___x_2408_, 2, v___x_2419_);
lean_ctor_set(v___x_2408_, 1, v___x_2417_);
lean_ctor_set(v___x_2408_, 0, v___x_2416_);
v___x_2421_ = v___x_2408_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2416_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v___x_2417_);
lean_ctor_set(v_reuseFailAlloc_2486_, 2, v___x_2419_);
v___x_2421_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2423_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2401_, v_a_2413_, v___x_2422_, v___x_2421_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; lean_object* v___x_2427_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2424_);
lean_dec_ref_known(v___x_2423_, 1);
v___x_2425_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8);
v___x_2426_ = 0;
v___x_2427_ = l_Lean_Compiler_LCNF_mkAuxParam(v___x_2401_, v___x_2425_, v___x_2426_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v___x_2429_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_a_2428_);
lean_dec_ref_known(v___x_2427_, 1);
v___x_2429_ = l_Lean_mkArrow(v___x_2425_, v___x_2422_, v_a_2391_, v_a_2392_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v_fvarId_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v_fvarId_2434_; lean_object* v_binderName_2435_; lean_object* v_lctx_2436_; lean_object* v_nextIdx_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2461_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2429_, 1);
v_fvarId_2431_ = lean_ctor_get(v_a_2424_, 0);
v___x_2432_ = lean_st_ref_take(v_a_2390_);
v___x_2433_ = lean_array_get(v___x_2414_, v_params_2405_, v___x_2403_);
lean_dec_ref(v_params_2405_);
v_fvarId_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_fvarId_2434_);
v_binderName_2435_ = lean_ctor_get(v___x_2433_, 1);
lean_inc(v_binderName_2435_);
lean_dec(v___x_2433_);
v_lctx_2436_ = lean_ctor_get(v___x_2432_, 0);
v_nextIdx_2437_ = lean_ctor_get(v___x_2432_, 1);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2439_ = v___x_2432_;
v_isShared_2440_ = v_isSharedCheck_2461_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_nextIdx_2437_);
lean_inc(v_lctx_2436_);
lean_dec(v___x_2432_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2461_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2448_; 
lean_inc(v_fvarId_2431_);
v___x_2441_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2441_, 0, v_fvarId_2431_);
v___x_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2442_, 0, v_a_2424_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = lean_mk_empty_array_with_capacity(v___x_2397_);
v___x_2444_ = lean_array_push(v___x_2443_, v_a_2428_);
v___x_2445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2445_, 0, v_fvarId_2434_);
lean_ctor_set(v___x_2445_, 1, v_binderName_2435_);
lean_ctor_set(v___x_2445_, 2, v___x_2444_);
lean_ctor_set(v___x_2445_, 3, v_a_2430_);
lean_ctor_set(v___x_2445_, 4, v___x_2442_);
lean_inc_ref(v___x_2445_);
v___x_2446_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_2401_, v_lctx_2436_, v___x_2445_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2446_);
v___x_2448_ = v___x_2439_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v_nextIdx_2437_);
v___x_2448_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = lean_st_ref_put(v_a_2390_, v___x_2448_);
v___x_2450_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2406_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2459_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2459_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2459_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2455_; lean_object* v___x_2457_; 
v___x_2455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2445_);
lean_ctor_set(v___x_2455_, 1, v_a_2451_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2455_);
v___x_2457_ = v___x_2453_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2455_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
else
{
lean_dec_ref_known(v___x_2445_, 5);
return v___x_2450_;
}
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec(v_a_2428_);
lean_dec(v_a_2424_);
lean_dec_ref(v_code_2406_);
lean_dec_ref(v_params_2405_);
v_a_2462_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2429_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2429_);
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
lean_dec(v_a_2424_);
lean_dec_ref(v_code_2406_);
lean_dec_ref(v_params_2405_);
v_a_2470_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2427_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2427_);
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
lean_dec_ref(v_code_2406_);
lean_dec_ref(v_params_2405_);
v_a_2478_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2423_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2423_);
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
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_del_object(v___x_2408_);
lean_dec_ref(v_code_2406_);
lean_dec_ref(v_params_2405_);
v_a_2487_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2412_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2412_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_del_object(v___x_2408_);
lean_dec_ref(v_code_2406_);
lean_dec_ref(v_params_2405_);
v_a_2495_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2410_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2410_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
else
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_dec(v___x_2404_);
v___x_2505_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9);
v___x_2506_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2505_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
return v___x_2506_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2508_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2509_ = lean_unsigned_to_nat(2u);
v___x_2510_ = lean_unsigned_to_nat(334u);
v___x_2511_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0));
v___x_2512_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2513_ = l_mkPanicMessageWithDecl(v___x_2512_, v___x_2511_, v___x_2510_, v___x_2509_, v___x_2508_);
return v___x_2513_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2518_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_2519_ = lean_unsigned_to_nat(34u);
v___x_2520_ = lean_unsigned_to_nat(335u);
v___x_2521_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0));
v___x_2522_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2523_ = l_mkPanicMessageWithDecl(v___x_2522_, v___x_2521_, v___x_2520_, v___x_2519_, v___x_2518_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(lean_object* v_c_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_){
_start:
{
lean_object* v_discr_2531_; lean_object* v_alts_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2601_; 
v_discr_2531_ = lean_ctor_get(v_c_2524_, 2);
v_alts_2532_ = lean_ctor_get(v_c_2524_, 3);
v_isSharedCheck_2601_ = !lean_is_exclusive(v_c_2524_);
if (v_isSharedCheck_2601_ == 0)
{
lean_object* v_unused_2602_; lean_object* v_unused_2603_; 
v_unused_2602_ = lean_ctor_get(v_c_2524_, 1);
lean_dec(v_unused_2602_);
v_unused_2603_ = lean_ctor_get(v_c_2524_, 0);
lean_dec(v_unused_2603_);
v___x_2534_ = v_c_2524_;
v_isShared_2535_ = v_isSharedCheck_2601_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_alts_2532_);
lean_inc(v_discr_2531_);
lean_dec(v_c_2524_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2601_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2536_ = lean_array_get_size(v_alts_2532_);
v___x_2537_ = lean_unsigned_to_nat(1u);
v___x_2538_ = lean_nat_dec_eq(v___x_2536_, v___x_2537_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
lean_del_object(v___x_2534_);
lean_dec_ref(v_alts_2532_);
lean_dec(v_discr_2531_);
v___x_2539_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1);
v___x_2540_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2539_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
return v___x_2540_;
}
else
{
uint8_t v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2541_ = 0;
v___x_2542_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2543_ = lean_unsigned_to_nat(0u);
v___x_2544_ = lean_array_get(v___x_2542_, v_alts_2532_, v___x_2543_);
lean_dec_ref(v_alts_2532_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_params_2545_; lean_object* v_code_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2597_; 
v_params_2545_ = lean_ctor_get(v___x_2544_, 1);
v_code_2546_ = lean_ctor_get(v___x_2544_, 2);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2597_ == 0)
{
lean_object* v_unused_2598_; 
v_unused_2598_ = lean_ctor_get(v___x_2544_, 0);
lean_dec(v_unused_2598_);
v___x_2548_ = v___x_2544_;
v_isShared_2549_ = v_isSharedCheck_2597_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_code_2546_);
lean_inc(v_params_2545_);
lean_dec(v___x_2544_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2597_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2550_; 
v___x_2550_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2541_, v_params_2545_, v_a_2527_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v_fvarId_2554_; lean_object* v_binderName_2555_; lean_object* v_lctx_2556_; lean_object* v_nextIdx_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2588_; 
lean_dec_ref_known(v___x_2550_, 1);
v___x_2551_ = lean_st_ref_take(v_a_2527_);
v___x_2552_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2553_ = lean_array_get(v___x_2552_, v_params_2545_, v___x_2543_);
lean_dec_ref(v_params_2545_);
v_fvarId_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_fvarId_2554_);
v_binderName_2555_ = lean_ctor_get(v___x_2553_, 1);
lean_inc(v_binderName_2555_);
lean_dec(v___x_2553_);
v_lctx_2556_ = lean_ctor_get(v___x_2551_, 0);
v_nextIdx_2557_ = lean_ctor_get(v___x_2551_, 1);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2559_ = v___x_2551_;
v_isShared_2560_ = v_isSharedCheck_2588_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_nextIdx_2557_);
lean_inc(v_lctx_2556_);
lean_dec(v___x_2551_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2588_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2567_; 
v___x_2561_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__4));
v___x_2562_ = lean_box(0);
v___x_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2563_, 0, v_discr_2531_);
v___x_2564_ = lean_mk_empty_array_with_capacity(v___x_2537_);
v___x_2565_ = lean_array_push(v___x_2564_, v___x_2563_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set_tag(v___x_2548_, 3);
lean_ctor_set(v___x_2548_, 2, v___x_2565_);
lean_ctor_set(v___x_2548_, 1, v___x_2562_);
lean_ctor_set(v___x_2548_, 0, v___x_2561_);
v___x_2567_ = v___x_2548_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2561_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v___x_2562_);
lean_ctor_set(v_reuseFailAlloc_2587_, 2, v___x_2565_);
v___x_2567_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
lean_object* v___x_2568_; lean_object* v___x_2570_; 
v___x_2568_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 3, v___x_2567_);
lean_ctor_set(v___x_2534_, 2, v___x_2568_);
lean_ctor_set(v___x_2534_, 1, v_binderName_2555_);
lean_ctor_set(v___x_2534_, 0, v_fvarId_2554_);
v___x_2570_ = v___x_2534_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_fvarId_2554_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_binderName_2555_);
lean_ctor_set(v_reuseFailAlloc_2586_, 2, v___x_2568_);
lean_ctor_set(v_reuseFailAlloc_2586_, 3, v___x_2567_);
v___x_2570_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
lean_object* v___x_2571_; lean_object* v___x_2573_; 
lean_inc_ref(v___x_2570_);
v___x_2571_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2541_, v_lctx_2556_, v___x_2570_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2571_);
v___x_2573_ = v___x_2559_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2571_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_nextIdx_2557_);
v___x_2573_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2574_ = lean_st_ref_put(v_a_2527_, v___x_2573_);
v___x_2575_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2546_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2584_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2578_ = v___x_2575_;
v_isShared_2579_ = v_isSharedCheck_2584_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2575_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2584_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2580_; lean_object* v___x_2582_; 
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2570_);
lean_ctor_set(v___x_2580_, 1, v_a_2576_);
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 0, v___x_2580_);
v___x_2582_ = v___x_2578_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
else
{
lean_dec_ref(v___x_2570_);
return v___x_2575_;
}
}
}
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_del_object(v___x_2548_);
lean_dec_ref(v_code_2546_);
lean_dec_ref(v_params_2545_);
lean_del_object(v___x_2534_);
lean_dec(v_discr_2531_);
v_a_2589_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2550_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2550_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
else
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
lean_dec(v___x_2544_);
lean_del_object(v___x_2534_);
lean_dec(v_discr_2531_);
v___x_2599_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5);
v___x_2600_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2599_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
return v___x_2600_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2605_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2606_ = lean_unsigned_to_nat(2u);
v___x_2607_ = lean_unsigned_to_nat(323u);
v___x_2608_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0));
v___x_2609_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2610_ = l_mkPanicMessageWithDecl(v___x_2609_, v___x_2608_, v___x_2607_, v___x_2606_, v___x_2605_);
return v___x_2610_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2614_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_2615_ = lean_unsigned_to_nat(34u);
v___x_2616_ = lean_unsigned_to_nat(324u);
v___x_2617_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0));
v___x_2618_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2619_ = l_mkPanicMessageWithDecl(v___x_2618_, v___x_2617_, v___x_2616_, v___x_2615_, v___x_2614_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg(lean_object* v_c_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_){
_start:
{
lean_object* v_discr_2627_; lean_object* v_alts_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2697_; 
v_discr_2627_ = lean_ctor_get(v_c_2620_, 2);
v_alts_2628_ = lean_ctor_get(v_c_2620_, 3);
v_isSharedCheck_2697_ = !lean_is_exclusive(v_c_2620_);
if (v_isSharedCheck_2697_ == 0)
{
lean_object* v_unused_2698_; lean_object* v_unused_2699_; 
v_unused_2698_ = lean_ctor_get(v_c_2620_, 1);
lean_dec(v_unused_2698_);
v_unused_2699_ = lean_ctor_get(v_c_2620_, 0);
lean_dec(v_unused_2699_);
v___x_2630_ = v_c_2620_;
v_isShared_2631_ = v_isSharedCheck_2697_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_alts_2628_);
lean_inc(v_discr_2627_);
lean_dec(v_c_2620_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2697_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; 
v___x_2632_ = lean_array_get_size(v_alts_2628_);
v___x_2633_ = lean_unsigned_to_nat(1u);
v___x_2634_ = lean_nat_dec_eq(v___x_2632_, v___x_2633_);
if (v___x_2634_ == 0)
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
lean_del_object(v___x_2630_);
lean_dec_ref(v_alts_2628_);
lean_dec(v_discr_2627_);
v___x_2635_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1);
v___x_2636_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2635_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_);
return v___x_2636_;
}
else
{
uint8_t v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2637_ = 0;
v___x_2638_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2639_ = lean_unsigned_to_nat(0u);
v___x_2640_ = lean_array_get(v___x_2638_, v_alts_2628_, v___x_2639_);
lean_dec_ref(v_alts_2628_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_params_2641_; lean_object* v_code_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2693_; 
v_params_2641_ = lean_ctor_get(v___x_2640_, 1);
v_code_2642_ = lean_ctor_get(v___x_2640_, 2);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2693_ == 0)
{
lean_object* v_unused_2694_; 
v_unused_2694_ = lean_ctor_get(v___x_2640_, 0);
lean_dec(v_unused_2694_);
v___x_2644_ = v___x_2640_;
v_isShared_2645_ = v_isSharedCheck_2693_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_code_2642_);
lean_inc(v_params_2641_);
lean_dec(v___x_2640_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2693_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2637_, v_params_2641_, v_a_2623_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v_fvarId_2650_; lean_object* v_binderName_2651_; lean_object* v_lctx_2652_; lean_object* v_nextIdx_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2684_; 
lean_dec_ref_known(v___x_2646_, 1);
v___x_2647_ = lean_st_ref_take(v_a_2623_);
v___x_2648_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2649_ = lean_array_get(v___x_2648_, v_params_2641_, v___x_2639_);
lean_dec_ref(v_params_2641_);
v_fvarId_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_fvarId_2650_);
v_binderName_2651_ = lean_ctor_get(v___x_2649_, 1);
lean_inc(v_binderName_2651_);
lean_dec(v___x_2649_);
v_lctx_2652_ = lean_ctor_get(v___x_2647_, 0);
v_nextIdx_2653_ = lean_ctor_get(v___x_2647_, 1);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2655_ = v___x_2647_;
v_isShared_2656_ = v_isSharedCheck_2684_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_nextIdx_2653_);
lean_inc(v_lctx_2652_);
lean_dec(v___x_2647_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2684_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2663_; 
v___x_2657_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__3));
v___x_2658_ = lean_box(0);
v___x_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2659_, 0, v_discr_2627_);
v___x_2660_ = lean_mk_empty_array_with_capacity(v___x_2633_);
v___x_2661_ = lean_array_push(v___x_2660_, v___x_2659_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set_tag(v___x_2644_, 3);
lean_ctor_set(v___x_2644_, 2, v___x_2661_);
lean_ctor_set(v___x_2644_, 1, v___x_2658_);
lean_ctor_set(v___x_2644_, 0, v___x_2657_);
v___x_2663_ = v___x_2644_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2683_, 2, v___x_2661_);
v___x_2663_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
lean_object* v___x_2664_; lean_object* v___x_2666_; 
v___x_2664_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 3, v___x_2663_);
lean_ctor_set(v___x_2630_, 2, v___x_2664_);
lean_ctor_set(v___x_2630_, 1, v_binderName_2651_);
lean_ctor_set(v___x_2630_, 0, v_fvarId_2650_);
v___x_2666_ = v___x_2630_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_fvarId_2650_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_binderName_2651_);
lean_ctor_set(v_reuseFailAlloc_2682_, 2, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2682_, 3, v___x_2663_);
v___x_2666_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v___x_2667_; lean_object* v___x_2669_; 
lean_inc_ref(v___x_2666_);
v___x_2667_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2637_, v_lctx_2652_, v___x_2666_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v___x_2667_);
v___x_2669_ = v___x_2655_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2667_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v_nextIdx_2653_);
v___x_2669_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2670_ = lean_st_ref_put(v_a_2623_, v___x_2669_);
v___x_2671_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2642_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2680_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2674_ = v___x_2671_;
v_isShared_2675_ = v_isSharedCheck_2680_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2680_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2676_; lean_object* v___x_2678_; 
v___x_2676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2666_);
lean_ctor_set(v___x_2676_, 1, v_a_2672_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2676_);
v___x_2678_ = v___x_2674_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2676_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
else
{
lean_dec_ref(v___x_2666_);
return v___x_2671_;
}
}
}
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_del_object(v___x_2644_);
lean_dec_ref(v_code_2642_);
lean_dec_ref(v_params_2641_);
lean_del_object(v___x_2630_);
lean_dec(v_discr_2627_);
v_a_2685_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2646_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2646_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
}
else
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
lean_dec(v___x_2640_);
lean_del_object(v___x_2630_);
lean_dec(v_discr_2627_);
v___x_2695_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4);
v___x_2696_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2695_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_);
return v___x_2696_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2701_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2702_ = lean_unsigned_to_nat(2u);
v___x_2703_ = lean_unsigned_to_nat(312u);
v___x_2704_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0));
v___x_2705_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2706_ = l_mkPanicMessageWithDecl(v___x_2705_, v___x_2704_, v___x_2703_, v___x_2702_, v___x_2701_);
return v___x_2706_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2711_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_2712_ = lean_unsigned_to_nat(34u);
v___x_2713_ = lean_unsigned_to_nat(313u);
v___x_2714_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0));
v___x_2715_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2716_ = l_mkPanicMessageWithDecl(v___x_2715_, v___x_2714_, v___x_2713_, v___x_2712_, v___x_2711_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg(lean_object* v_c_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v_discr_2724_; lean_object* v_alts_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2794_; 
v_discr_2724_ = lean_ctor_get(v_c_2717_, 2);
v_alts_2725_ = lean_ctor_get(v_c_2717_, 3);
v_isSharedCheck_2794_ = !lean_is_exclusive(v_c_2717_);
if (v_isSharedCheck_2794_ == 0)
{
lean_object* v_unused_2795_; lean_object* v_unused_2796_; 
v_unused_2795_ = lean_ctor_get(v_c_2717_, 1);
lean_dec(v_unused_2795_);
v_unused_2796_ = lean_ctor_get(v_c_2717_, 0);
lean_dec(v_unused_2796_);
v___x_2727_ = v_c_2717_;
v_isShared_2728_ = v_isSharedCheck_2794_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_alts_2725_);
lean_inc(v_discr_2724_);
lean_dec(v_c_2717_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2794_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; uint8_t v___x_2731_; 
v___x_2729_ = lean_array_get_size(v_alts_2725_);
v___x_2730_ = lean_unsigned_to_nat(1u);
v___x_2731_ = lean_nat_dec_eq(v___x_2729_, v___x_2730_);
if (v___x_2731_ == 0)
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
lean_del_object(v___x_2727_);
lean_dec_ref(v_alts_2725_);
lean_dec(v_discr_2724_);
v___x_2732_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1);
v___x_2733_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2732_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_);
return v___x_2733_;
}
else
{
uint8_t v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2734_ = 0;
v___x_2735_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2736_ = lean_unsigned_to_nat(0u);
v___x_2737_ = lean_array_get(v___x_2735_, v_alts_2725_, v___x_2736_);
lean_dec_ref(v_alts_2725_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_params_2738_; lean_object* v_code_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2790_; 
v_params_2738_ = lean_ctor_get(v___x_2737_, 1);
v_code_2739_ = lean_ctor_get(v___x_2737_, 2);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2790_ == 0)
{
lean_object* v_unused_2791_; 
v_unused_2791_ = lean_ctor_get(v___x_2737_, 0);
lean_dec(v_unused_2791_);
v___x_2741_ = v___x_2737_;
v_isShared_2742_ = v_isSharedCheck_2790_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_code_2739_);
lean_inc(v_params_2738_);
lean_dec(v___x_2737_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2790_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2743_; 
v___x_2743_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2734_, v_params_2738_, v_a_2720_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v_fvarId_2747_; lean_object* v_binderName_2748_; lean_object* v_lctx_2749_; lean_object* v_nextIdx_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2781_; 
lean_dec_ref_known(v___x_2743_, 1);
v___x_2744_ = lean_st_ref_take(v_a_2720_);
v___x_2745_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2746_ = lean_array_get(v___x_2745_, v_params_2738_, v___x_2736_);
lean_dec_ref(v_params_2738_);
v_fvarId_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_fvarId_2747_);
v_binderName_2748_ = lean_ctor_get(v___x_2746_, 1);
lean_inc(v_binderName_2748_);
lean_dec(v___x_2746_);
v_lctx_2749_ = lean_ctor_get(v___x_2744_, 0);
v_nextIdx_2750_ = lean_ctor_get(v___x_2744_, 1);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2752_ = v___x_2744_;
v_isShared_2753_ = v_isSharedCheck_2781_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_nextIdx_2750_);
lean_inc(v_lctx_2749_);
lean_dec(v___x_2744_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2781_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2760_; 
v___x_2754_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__4));
v___x_2755_ = lean_box(0);
v___x_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2756_, 0, v_discr_2724_);
v___x_2757_ = lean_mk_empty_array_with_capacity(v___x_2730_);
v___x_2758_ = lean_array_push(v___x_2757_, v___x_2756_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set_tag(v___x_2741_, 3);
lean_ctor_set(v___x_2741_, 2, v___x_2758_);
lean_ctor_set(v___x_2741_, 1, v___x_2755_);
lean_ctor_set(v___x_2741_, 0, v___x_2754_);
v___x_2760_ = v___x_2741_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2754_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v___x_2755_);
lean_ctor_set(v_reuseFailAlloc_2780_, 2, v___x_2758_);
v___x_2760_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
lean_object* v___x_2761_; lean_object* v___x_2763_; 
v___x_2761_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 3, v___x_2760_);
lean_ctor_set(v___x_2727_, 2, v___x_2761_);
lean_ctor_set(v___x_2727_, 1, v_binderName_2748_);
lean_ctor_set(v___x_2727_, 0, v_fvarId_2747_);
v___x_2763_ = v___x_2727_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_fvarId_2747_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_binderName_2748_);
lean_ctor_set(v_reuseFailAlloc_2779_, 2, v___x_2761_);
lean_ctor_set(v_reuseFailAlloc_2779_, 3, v___x_2760_);
v___x_2763_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_object* v___x_2764_; lean_object* v___x_2766_; 
lean_inc_ref(v___x_2763_);
v___x_2764_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2734_, v_lctx_2749_, v___x_2763_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v___x_2764_);
v___x_2766_ = v___x_2752_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2764_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_nextIdx_2750_);
v___x_2766_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = lean_st_ref_put(v_a_2720_, v___x_2766_);
v___x_2768_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2739_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2777_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2771_ = v___x_2768_;
v_isShared_2772_ = v_isSharedCheck_2777_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2768_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2777_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2773_; lean_object* v___x_2775_; 
v___x_2773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2763_);
lean_ctor_set(v___x_2773_, 1, v_a_2769_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v___x_2773_);
v___x_2775_ = v___x_2771_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2773_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
else
{
lean_dec_ref(v___x_2763_);
return v___x_2768_;
}
}
}
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_del_object(v___x_2741_);
lean_dec_ref(v_code_2739_);
lean_dec_ref(v_params_2738_);
lean_del_object(v___x_2727_);
lean_dec(v_discr_2724_);
v_a_2782_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2743_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2743_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
else
{
lean_object* v___x_2792_; lean_object* v___x_2793_; 
lean_dec(v___x_2737_);
lean_del_object(v___x_2727_);
lean_dec(v_discr_2724_);
v___x_2792_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5);
v___x_2793_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2792_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_);
return v___x_2793_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2798_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2799_ = lean_unsigned_to_nat(2u);
v___x_2800_ = lean_unsigned_to_nat(301u);
v___x_2801_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0));
v___x_2802_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2803_ = l_mkPanicMessageWithDecl(v___x_2802_, v___x_2801_, v___x_2800_, v___x_2799_, v___x_2798_);
return v___x_2803_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2808_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_2809_ = lean_unsigned_to_nat(34u);
v___x_2810_ = lean_unsigned_to_nat(302u);
v___x_2811_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0));
v___x_2812_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2813_ = l_mkPanicMessageWithDecl(v___x_2812_, v___x_2811_, v___x_2810_, v___x_2809_, v___x_2808_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(lean_object* v_c_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v_discr_2821_; lean_object* v_alts_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2891_; 
v_discr_2821_ = lean_ctor_get(v_c_2814_, 2);
v_alts_2822_ = lean_ctor_get(v_c_2814_, 3);
v_isSharedCheck_2891_ = !lean_is_exclusive(v_c_2814_);
if (v_isSharedCheck_2891_ == 0)
{
lean_object* v_unused_2892_; lean_object* v_unused_2893_; 
v_unused_2892_ = lean_ctor_get(v_c_2814_, 1);
lean_dec(v_unused_2892_);
v_unused_2893_ = lean_ctor_get(v_c_2814_, 0);
lean_dec(v_unused_2893_);
v___x_2824_ = v_c_2814_;
v_isShared_2825_ = v_isSharedCheck_2891_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_alts_2822_);
lean_inc(v_discr_2821_);
lean_dec(v_c_2814_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2891_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v___x_2826_ = lean_array_get_size(v_alts_2822_);
v___x_2827_ = lean_unsigned_to_nat(1u);
v___x_2828_ = lean_nat_dec_eq(v___x_2826_, v___x_2827_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
lean_del_object(v___x_2824_);
lean_dec_ref(v_alts_2822_);
lean_dec(v_discr_2821_);
v___x_2829_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1);
v___x_2830_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2829_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_);
return v___x_2830_;
}
else
{
uint8_t v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2831_ = 0;
v___x_2832_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2833_ = lean_unsigned_to_nat(0u);
v___x_2834_ = lean_array_get(v___x_2832_, v_alts_2822_, v___x_2833_);
lean_dec_ref(v_alts_2822_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_params_2835_; lean_object* v_code_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2887_; 
v_params_2835_ = lean_ctor_get(v___x_2834_, 1);
v_code_2836_ = lean_ctor_get(v___x_2834_, 2);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2887_ == 0)
{
lean_object* v_unused_2888_; 
v_unused_2888_ = lean_ctor_get(v___x_2834_, 0);
lean_dec(v_unused_2888_);
v___x_2838_ = v___x_2834_;
v_isShared_2839_ = v_isSharedCheck_2887_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_code_2836_);
lean_inc(v_params_2835_);
lean_dec(v___x_2834_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2887_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2840_; 
v___x_2840_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2831_, v_params_2835_, v_a_2817_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v_fvarId_2844_; lean_object* v_binderName_2845_; lean_object* v_lctx_2846_; lean_object* v_nextIdx_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2878_; 
lean_dec_ref_known(v___x_2840_, 1);
v___x_2841_ = lean_st_ref_take(v_a_2817_);
v___x_2842_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2843_ = lean_array_get(v___x_2842_, v_params_2835_, v___x_2833_);
lean_dec_ref(v_params_2835_);
v_fvarId_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_fvarId_2844_);
v_binderName_2845_ = lean_ctor_get(v___x_2843_, 1);
lean_inc(v_binderName_2845_);
lean_dec(v___x_2843_);
v_lctx_2846_ = lean_ctor_get(v___x_2841_, 0);
v_nextIdx_2847_ = lean_ctor_get(v___x_2841_, 1);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2849_ = v___x_2841_;
v_isShared_2850_ = v_isSharedCheck_2878_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_nextIdx_2847_);
lean_inc(v_lctx_2846_);
lean_dec(v___x_2841_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2878_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2857_; 
v___x_2851_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__3));
v___x_2852_ = lean_box(0);
v___x_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2853_, 0, v_discr_2821_);
v___x_2854_ = lean_mk_empty_array_with_capacity(v___x_2827_);
v___x_2855_ = lean_array_push(v___x_2854_, v___x_2853_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set_tag(v___x_2838_, 3);
lean_ctor_set(v___x_2838_, 2, v___x_2855_);
lean_ctor_set(v___x_2838_, 1, v___x_2852_);
lean_ctor_set(v___x_2838_, 0, v___x_2851_);
v___x_2857_ = v___x_2838_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2851_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v___x_2852_);
lean_ctor_set(v_reuseFailAlloc_2877_, 2, v___x_2855_);
v___x_2857_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
lean_object* v___x_2858_; lean_object* v___x_2860_; 
v___x_2858_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 3, v___x_2857_);
lean_ctor_set(v___x_2824_, 2, v___x_2858_);
lean_ctor_set(v___x_2824_, 1, v_binderName_2845_);
lean_ctor_set(v___x_2824_, 0, v_fvarId_2844_);
v___x_2860_ = v___x_2824_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_fvarId_2844_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_binderName_2845_);
lean_ctor_set(v_reuseFailAlloc_2876_, 2, v___x_2858_);
lean_ctor_set(v_reuseFailAlloc_2876_, 3, v___x_2857_);
v___x_2860_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
lean_object* v___x_2861_; lean_object* v___x_2863_; 
lean_inc_ref(v___x_2860_);
v___x_2861_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2831_, v_lctx_2846_, v___x_2860_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v___x_2861_);
v___x_2863_ = v___x_2849_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2861_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v_nextIdx_2847_);
v___x_2863_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2864_ = lean_st_ref_put(v_a_2817_, v___x_2863_);
v___x_2865_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2836_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2874_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2868_ = v___x_2865_;
v_isShared_2869_ = v_isSharedCheck_2874_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2865_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2874_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; lean_object* v___x_2872_; 
v___x_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2860_);
lean_ctor_set(v___x_2870_, 1, v_a_2866_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v___x_2870_);
v___x_2872_ = v___x_2868_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2870_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
else
{
lean_dec_ref(v___x_2860_);
return v___x_2865_;
}
}
}
}
}
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_del_object(v___x_2838_);
lean_dec_ref(v_code_2836_);
lean_dec_ref(v_params_2835_);
lean_del_object(v___x_2824_);
lean_dec(v_discr_2821_);
v_a_2879_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2840_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2840_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
}
else
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
lean_dec(v___x_2834_);
lean_del_object(v___x_2824_);
lean_dec(v_discr_2821_);
v___x_2889_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4);
v___x_2890_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2889_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_);
return v___x_2890_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2895_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2896_ = lean_unsigned_to_nat(2u);
v___x_2897_ = lean_unsigned_to_nat(289u);
v___x_2898_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0));
v___x_2899_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2900_ = l_mkPanicMessageWithDecl(v___x_2899_, v___x_2898_, v___x_2897_, v___x_2896_, v___x_2895_);
return v___x_2900_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2904_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_2905_ = lean_unsigned_to_nat(34u);
v___x_2906_ = lean_unsigned_to_nat(290u);
v___x_2907_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0));
v___x_2908_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2909_ = l_mkPanicMessageWithDecl(v___x_2908_, v___x_2907_, v___x_2906_, v___x_2905_, v___x_2904_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(lean_object* v_c_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_){
_start:
{
lean_object* v_discr_2917_; lean_object* v_alts_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2987_; 
v_discr_2917_ = lean_ctor_get(v_c_2910_, 2);
v_alts_2918_ = lean_ctor_get(v_c_2910_, 3);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_c_2910_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; lean_object* v_unused_2989_; 
v_unused_2988_ = lean_ctor_get(v_c_2910_, 1);
lean_dec(v_unused_2988_);
v_unused_2989_ = lean_ctor_get(v_c_2910_, 0);
lean_dec(v_unused_2989_);
v___x_2920_ = v_c_2910_;
v_isShared_2921_ = v_isSharedCheck_2987_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_alts_2918_);
lean_inc(v_discr_2917_);
lean_dec(v_c_2910_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2987_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; uint8_t v___x_2924_; 
v___x_2922_ = lean_array_get_size(v_alts_2918_);
v___x_2923_ = lean_unsigned_to_nat(1u);
v___x_2924_ = lean_nat_dec_eq(v___x_2922_, v___x_2923_);
if (v___x_2924_ == 0)
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
lean_del_object(v___x_2920_);
lean_dec_ref(v_alts_2918_);
lean_dec(v_discr_2917_);
v___x_2925_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1);
v___x_2926_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2925_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_);
return v___x_2926_;
}
else
{
uint8_t v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2927_ = 0;
v___x_2928_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2929_ = lean_unsigned_to_nat(0u);
v___x_2930_ = lean_array_get(v___x_2928_, v_alts_2918_, v___x_2929_);
lean_dec_ref(v_alts_2918_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_params_2931_; lean_object* v_code_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2983_; 
v_params_2931_ = lean_ctor_get(v___x_2930_, 1);
v_code_2932_ = lean_ctor_get(v___x_2930_, 2);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2983_ == 0)
{
lean_object* v_unused_2984_; 
v_unused_2984_ = lean_ctor_get(v___x_2930_, 0);
lean_dec(v_unused_2984_);
v___x_2934_ = v___x_2930_;
v_isShared_2935_ = v_isSharedCheck_2983_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_code_2932_);
lean_inc(v_params_2931_);
lean_dec(v___x_2930_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2983_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2927_, v_params_2931_, v_a_2913_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v_fvarId_2940_; lean_object* v_binderName_2941_; lean_object* v_lctx_2942_; lean_object* v_nextIdx_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2974_; 
lean_dec_ref_known(v___x_2936_, 1);
v___x_2937_ = lean_st_ref_take(v_a_2913_);
v___x_2938_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2939_ = lean_array_get(v___x_2938_, v_params_2931_, v___x_2929_);
lean_dec_ref(v_params_2931_);
v_fvarId_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_fvarId_2940_);
v_binderName_2941_ = lean_ctor_get(v___x_2939_, 1);
lean_inc(v_binderName_2941_);
lean_dec(v___x_2939_);
v_lctx_2942_ = lean_ctor_get(v___x_2937_, 0);
v_nextIdx_2943_ = lean_ctor_get(v___x_2937_, 1);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2945_ = v___x_2937_;
v_isShared_2946_ = v_isSharedCheck_2974_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_nextIdx_2943_);
lean_inc(v_lctx_2942_);
lean_dec(v___x_2937_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2974_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2953_; 
v___x_2947_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__4));
v___x_2948_ = lean_box(0);
v___x_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2949_, 0, v_discr_2917_);
v___x_2950_ = lean_mk_empty_array_with_capacity(v___x_2923_);
v___x_2951_ = lean_array_push(v___x_2950_, v___x_2949_);
if (v_isShared_2935_ == 0)
{
lean_ctor_set_tag(v___x_2934_, 3);
lean_ctor_set(v___x_2934_, 2, v___x_2951_);
lean_ctor_set(v___x_2934_, 1, v___x_2948_);
lean_ctor_set(v___x_2934_, 0, v___x_2947_);
v___x_2953_ = v___x_2934_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2947_);
lean_ctor_set(v_reuseFailAlloc_2973_, 1, v___x_2948_);
lean_ctor_set(v_reuseFailAlloc_2973_, 2, v___x_2951_);
v___x_2953_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
lean_object* v___x_2954_; lean_object* v___x_2956_; 
v___x_2954_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 3, v___x_2953_);
lean_ctor_set(v___x_2920_, 2, v___x_2954_);
lean_ctor_set(v___x_2920_, 1, v_binderName_2941_);
lean_ctor_set(v___x_2920_, 0, v_fvarId_2940_);
v___x_2956_ = v___x_2920_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_fvarId_2940_);
lean_ctor_set(v_reuseFailAlloc_2972_, 1, v_binderName_2941_);
lean_ctor_set(v_reuseFailAlloc_2972_, 2, v___x_2954_);
lean_ctor_set(v_reuseFailAlloc_2972_, 3, v___x_2953_);
v___x_2956_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
lean_object* v___x_2957_; lean_object* v___x_2959_; 
lean_inc_ref(v___x_2956_);
v___x_2957_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2927_, v_lctx_2942_, v___x_2956_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 0, v___x_2957_);
v___x_2959_ = v___x_2945_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2957_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v_nextIdx_2943_);
v___x_2959_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2960_ = lean_st_ref_put(v_a_2913_, v___x_2959_);
v___x_2961_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2932_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2970_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2964_ = v___x_2961_;
v_isShared_2965_ = v_isSharedCheck_2970_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2961_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2970_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2966_; lean_object* v___x_2968_; 
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2956_);
lean_ctor_set(v___x_2966_, 1, v_a_2962_);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 0, v___x_2966_);
v___x_2968_ = v___x_2964_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v___x_2966_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
else
{
lean_dec_ref(v___x_2956_);
return v___x_2961_;
}
}
}
}
}
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_del_object(v___x_2934_);
lean_dec_ref(v_code_2932_);
lean_dec_ref(v_params_2931_);
lean_del_object(v___x_2920_);
lean_dec(v_discr_2917_);
v_a_2975_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2936_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2936_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
}
else
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
lean_dec(v___x_2930_);
lean_del_object(v___x_2920_);
lean_dec(v_discr_2917_);
v___x_2985_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5);
v___x_2986_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2985_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_);
return v___x_2986_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2991_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2992_ = lean_unsigned_to_nat(2u);
v___x_2993_ = lean_unsigned_to_nat(277u);
v___x_2994_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0));
v___x_2995_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2996_ = l_mkPanicMessageWithDecl(v___x_2995_, v___x_2994_, v___x_2993_, v___x_2992_, v___x_2991_);
return v___x_2996_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3001_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_3002_ = lean_unsigned_to_nat(34u);
v___x_3003_ = lean_unsigned_to_nat(278u);
v___x_3004_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0));
v___x_3005_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_3006_ = l_mkPanicMessageWithDecl(v___x_3005_, v___x_3004_, v___x_3003_, v___x_3002_, v___x_3001_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg(lean_object* v_c_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_){
_start:
{
lean_object* v_discr_3014_; lean_object* v_alts_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3084_; 
v_discr_3014_ = lean_ctor_get(v_c_3007_, 2);
v_alts_3015_ = lean_ctor_get(v_c_3007_, 3);
v_isSharedCheck_3084_ = !lean_is_exclusive(v_c_3007_);
if (v_isSharedCheck_3084_ == 0)
{
lean_object* v_unused_3085_; lean_object* v_unused_3086_; 
v_unused_3085_ = lean_ctor_get(v_c_3007_, 1);
lean_dec(v_unused_3085_);
v_unused_3086_ = lean_ctor_get(v_c_3007_, 0);
lean_dec(v_unused_3086_);
v___x_3017_ = v_c_3007_;
v_isShared_3018_ = v_isSharedCheck_3084_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_alts_3015_);
lean_inc(v_discr_3014_);
lean_dec(v_c_3007_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3084_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; 
v___x_3019_ = lean_array_get_size(v_alts_3015_);
v___x_3020_ = lean_unsigned_to_nat(1u);
v___x_3021_ = lean_nat_dec_eq(v___x_3019_, v___x_3020_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
lean_del_object(v___x_3017_);
lean_dec_ref(v_alts_3015_);
lean_dec(v_discr_3014_);
v___x_3022_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1);
v___x_3023_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3022_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
return v___x_3023_;
}
else
{
uint8_t v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3024_ = 0;
v___x_3025_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_3026_ = lean_unsigned_to_nat(0u);
v___x_3027_ = lean_array_get(v___x_3025_, v_alts_3015_, v___x_3026_);
lean_dec_ref(v_alts_3015_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_params_3028_; lean_object* v_code_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3080_; 
v_params_3028_ = lean_ctor_get(v___x_3027_, 1);
v_code_3029_ = lean_ctor_get(v___x_3027_, 2);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3080_ == 0)
{
lean_object* v_unused_3081_; 
v_unused_3081_ = lean_ctor_get(v___x_3027_, 0);
lean_dec(v_unused_3081_);
v___x_3031_ = v___x_3027_;
v_isShared_3032_ = v_isSharedCheck_3080_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_code_3029_);
lean_inc(v_params_3028_);
lean_dec(v___x_3027_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3080_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3033_; 
v___x_3033_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3024_, v_params_3028_, v_a_3010_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v_fvarId_3037_; lean_object* v_binderName_3038_; lean_object* v_lctx_3039_; lean_object* v_nextIdx_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3071_; 
lean_dec_ref_known(v___x_3033_, 1);
v___x_3034_ = lean_st_ref_take(v_a_3010_);
v___x_3035_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_3036_ = lean_array_get(v___x_3035_, v_params_3028_, v___x_3026_);
lean_dec_ref(v_params_3028_);
v_fvarId_3037_ = lean_ctor_get(v___x_3036_, 0);
lean_inc(v_fvarId_3037_);
v_binderName_3038_ = lean_ctor_get(v___x_3036_, 1);
lean_inc(v_binderName_3038_);
lean_dec(v___x_3036_);
v_lctx_3039_ = lean_ctor_get(v___x_3034_, 0);
v_nextIdx_3040_ = lean_ctor_get(v___x_3034_, 1);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3042_ = v___x_3034_;
v_isShared_3043_ = v_isSharedCheck_3071_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_nextIdx_3040_);
lean_inc(v_lctx_3039_);
lean_dec(v___x_3034_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3071_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3050_; 
v___x_3044_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__4));
v___x_3045_ = lean_box(0);
v___x_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3046_, 0, v_discr_3014_);
v___x_3047_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5);
v___x_3048_ = lean_array_push(v___x_3047_, v___x_3046_);
if (v_isShared_3032_ == 0)
{
lean_ctor_set_tag(v___x_3031_, 3);
lean_ctor_set(v___x_3031_, 2, v___x_3048_);
lean_ctor_set(v___x_3031_, 1, v___x_3045_);
lean_ctor_set(v___x_3031_, 0, v___x_3044_);
v___x_3050_ = v___x_3031_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3044_);
lean_ctor_set(v_reuseFailAlloc_3070_, 1, v___x_3045_);
lean_ctor_set(v_reuseFailAlloc_3070_, 2, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3051_; lean_object* v___x_3053_; 
v___x_3051_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 3, v___x_3050_);
lean_ctor_set(v___x_3017_, 2, v___x_3051_);
lean_ctor_set(v___x_3017_, 1, v_binderName_3038_);
lean_ctor_set(v___x_3017_, 0, v_fvarId_3037_);
v___x_3053_ = v___x_3017_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_fvarId_3037_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v_binderName_3038_);
lean_ctor_set(v_reuseFailAlloc_3069_, 2, v___x_3051_);
lean_ctor_set(v_reuseFailAlloc_3069_, 3, v___x_3050_);
v___x_3053_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
lean_object* v___x_3054_; lean_object* v___x_3056_; 
lean_inc_ref(v___x_3053_);
v___x_3054_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3024_, v_lctx_3039_, v___x_3053_);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 0, v___x_3054_);
v___x_3056_ = v___x_3042_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3054_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v_nextIdx_3040_);
v___x_3056_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = lean_st_ref_put(v_a_3010_, v___x_3056_);
v___x_3058_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3029_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3067_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3061_ = v___x_3058_;
v_isShared_3062_ = v_isSharedCheck_3067_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3058_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3067_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3063_; lean_object* v___x_3065_; 
v___x_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3053_);
lean_ctor_set(v___x_3063_, 1, v_a_3059_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 0, v___x_3063_);
v___x_3065_ = v___x_3061_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3063_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
else
{
lean_dec_ref(v___x_3053_);
return v___x_3058_;
}
}
}
}
}
}
else
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
lean_del_object(v___x_3031_);
lean_dec_ref(v_code_3029_);
lean_dec_ref(v_params_3028_);
lean_del_object(v___x_3017_);
lean_dec(v_discr_3014_);
v_a_3072_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_3033_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3033_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3075_ == 0)
{
v___x_3077_ = v___x_3074_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3072_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
}
else
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
lean_dec(v___x_3027_);
lean_del_object(v___x_3017_);
lean_dec(v_discr_3014_);
v___x_3082_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_3083_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3082_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
return v___x_3083_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2(void){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3088_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_3089_ = lean_unsigned_to_nat(2u);
v___x_3090_ = lean_unsigned_to_nat(266u);
v___x_3091_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0));
v___x_3092_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_3093_ = l_mkPanicMessageWithDecl(v___x_3092_, v___x_3091_, v___x_3090_, v___x_3089_, v___x_3088_);
return v___x_3093_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3095_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_3096_ = lean_unsigned_to_nat(34u);
v___x_3097_ = lean_unsigned_to_nat(267u);
v___x_3098_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0));
v___x_3099_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_3100_ = l_mkPanicMessageWithDecl(v___x_3099_, v___x_3098_, v___x_3097_, v___x_3096_, v___x_3095_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg(lean_object* v_c_3101_, lean_object* v_uintName_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_){
_start:
{
lean_object* v_discr_3109_; lean_object* v_alts_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3180_; 
v_discr_3109_ = lean_ctor_get(v_c_3101_, 2);
v_alts_3110_ = lean_ctor_get(v_c_3101_, 3);
v_isSharedCheck_3180_ = !lean_is_exclusive(v_c_3101_);
if (v_isSharedCheck_3180_ == 0)
{
lean_object* v_unused_3181_; lean_object* v_unused_3182_; 
v_unused_3181_ = lean_ctor_get(v_c_3101_, 1);
lean_dec(v_unused_3181_);
v_unused_3182_ = lean_ctor_get(v_c_3101_, 0);
lean_dec(v_unused_3182_);
v___x_3112_ = v_c_3101_;
v_isShared_3113_ = v_isSharedCheck_3180_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_alts_3110_);
lean_inc(v_discr_3109_);
lean_dec(v_c_3101_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3180_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; uint8_t v___x_3116_; 
v___x_3114_ = lean_array_get_size(v_alts_3110_);
v___x_3115_ = lean_unsigned_to_nat(1u);
v___x_3116_ = lean_nat_dec_eq(v___x_3114_, v___x_3115_);
if (v___x_3116_ == 0)
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
lean_del_object(v___x_3112_);
lean_dec_ref(v_alts_3110_);
lean_dec(v_discr_3109_);
lean_dec(v_uintName_3102_);
v___x_3117_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2);
v___x_3118_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3117_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
return v___x_3118_;
}
else
{
uint8_t v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3119_ = 0;
v___x_3120_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_3121_ = lean_unsigned_to_nat(0u);
v___x_3122_ = lean_array_get(v___x_3120_, v_alts_3110_, v___x_3121_);
lean_dec_ref(v_alts_3110_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_params_3123_; lean_object* v_code_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3176_; 
v_params_3123_ = lean_ctor_get(v___x_3122_, 1);
v_code_3124_ = lean_ctor_get(v___x_3122_, 2);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3176_ == 0)
{
lean_object* v_unused_3177_; 
v_unused_3177_ = lean_ctor_get(v___x_3122_, 0);
lean_dec(v_unused_3177_);
v___x_3126_ = v___x_3122_;
v_isShared_3127_ = v_isSharedCheck_3176_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_code_3124_);
lean_inc(v_params_3123_);
lean_dec(v___x_3122_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3176_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3128_; 
v___x_3128_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3119_, v_params_3123_, v_a_3105_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v_fvarId_3132_; lean_object* v_binderName_3133_; lean_object* v_lctx_3134_; lean_object* v_nextIdx_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3167_; 
lean_dec_ref_known(v___x_3128_, 1);
v___x_3129_ = lean_st_ref_take(v_a_3105_);
v___x_3130_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_3131_ = lean_array_get(v___x_3130_, v_params_3123_, v___x_3121_);
lean_dec_ref(v_params_3123_);
v_fvarId_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_fvarId_3132_);
v_binderName_3133_ = lean_ctor_get(v___x_3131_, 1);
lean_inc(v_binderName_3133_);
lean_dec(v___x_3131_);
v_lctx_3134_ = lean_ctor_get(v___x_3129_, 0);
v_nextIdx_3135_ = lean_ctor_get(v___x_3129_, 1);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3137_ = v___x_3129_;
v_isShared_3138_ = v_isSharedCheck_3167_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_nextIdx_3135_);
lean_inc(v_lctx_3134_);
lean_dec(v___x_3129_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3167_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3146_; 
v___x_3139_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3));
v___x_3140_ = l_Lean_Name_str___override(v_uintName_3102_, v___x_3139_);
v___x_3141_ = lean_box(0);
v___x_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3142_, 0, v_discr_3109_);
v___x_3143_ = lean_mk_empty_array_with_capacity(v___x_3115_);
v___x_3144_ = lean_array_push(v___x_3143_, v___x_3142_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set_tag(v___x_3126_, 3);
lean_ctor_set(v___x_3126_, 2, v___x_3144_);
lean_ctor_set(v___x_3126_, 1, v___x_3141_);
lean_ctor_set(v___x_3126_, 0, v___x_3140_);
v___x_3146_ = v___x_3126_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3140_);
lean_ctor_set(v_reuseFailAlloc_3166_, 1, v___x_3141_);
lean_ctor_set(v_reuseFailAlloc_3166_, 2, v___x_3144_);
v___x_3146_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
lean_object* v___x_3147_; lean_object* v___x_3149_; 
v___x_3147_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 3, v___x_3146_);
lean_ctor_set(v___x_3112_, 2, v___x_3147_);
lean_ctor_set(v___x_3112_, 1, v_binderName_3133_);
lean_ctor_set(v___x_3112_, 0, v_fvarId_3132_);
v___x_3149_ = v___x_3112_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_fvarId_3132_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v_binderName_3133_);
lean_ctor_set(v_reuseFailAlloc_3165_, 2, v___x_3147_);
lean_ctor_set(v_reuseFailAlloc_3165_, 3, v___x_3146_);
v___x_3149_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
lean_object* v___x_3150_; lean_object* v___x_3152_; 
lean_inc_ref(v___x_3149_);
v___x_3150_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3119_, v_lctx_3134_, v___x_3149_);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 0, v___x_3150_);
v___x_3152_ = v___x_3137_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3150_);
lean_ctor_set(v_reuseFailAlloc_3164_, 1, v_nextIdx_3135_);
v___x_3152_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = lean_st_ref_put(v_a_3105_, v___x_3152_);
v___x_3154_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3124_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3163_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3157_ = v___x_3154_;
v_isShared_3158_ = v_isSharedCheck_3163_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3154_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3163_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3159_; lean_object* v___x_3161_; 
v___x_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3149_);
lean_ctor_set(v___x_3159_, 1, v_a_3155_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 0, v___x_3159_);
v___x_3161_ = v___x_3157_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v___x_3159_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
else
{
lean_dec_ref(v___x_3149_);
return v___x_3154_;
}
}
}
}
}
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_del_object(v___x_3126_);
lean_dec_ref(v_code_3124_);
lean_dec_ref(v_params_3123_);
lean_del_object(v___x_3112_);
lean_dec(v_discr_3109_);
lean_dec(v_uintName_3102_);
v_a_3168_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3128_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3128_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
}
else
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
lean_dec(v___x_3122_);
lean_del_object(v___x_3112_);
lean_dec(v_discr_3109_);
lean_dec(v_uintName_3102_);
v___x_3178_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4);
v___x_3179_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3178_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
return v___x_3179_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3186_ = lean_box(0);
v___x_3187_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
v___x_3188_ = l_Lean_mkConst(v___x_3187_, v___x_3186_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18(lean_object* v___x_3199_, size_t v_sz_3200_, size_t v_i_3201_, lean_object* v_bs_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
uint8_t v___x_3209_; 
v___x_3209_ = lean_usize_dec_lt(v_i_3201_, v_sz_3200_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; 
lean_dec_ref(v___x_3199_);
v___x_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3210_, 0, v_bs_3202_);
return v___x_3210_;
}
else
{
lean_object* v_v_3211_; lean_object* v___x_3212_; lean_object* v_bs_x27_3213_; lean_object* v_a_3215_; 
v_v_3211_ = lean_array_uget(v_bs_3202_, v_i_3201_);
v___x_3212_ = lean_unsigned_to_nat(0u);
v_bs_x27_3213_ = lean_array_uset(v_bs_3202_, v_i_3201_, v___x_3212_);
if (lean_obj_tag(v_v_3211_) == 0)
{
lean_object* v_ctorName_3220_; lean_object* v_params_3221_; lean_object* v_code_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3300_; 
v_ctorName_3220_ = lean_ctor_get(v_v_3211_, 0);
v_params_3221_ = lean_ctor_get(v_v_3211_, 1);
v_code_3222_ = lean_ctor_get(v_v_3211_, 2);
v_isSharedCheck_3300_ = !lean_is_exclusive(v_v_3211_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3224_ = v_v_3211_;
v_isShared_3225_ = v_isSharedCheck_3300_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_code_3222_);
lean_inc(v_params_3221_);
lean_inc(v_ctorName_3220_);
lean_dec(v_v_3211_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3300_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
uint8_t v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = 0;
v___x_3227_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3226_, v_params_3221_, v___y_3205_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v___x_3228_; uint8_t v___x_3229_; 
lean_dec_ref_known(v___x_3227_, 1);
v___x_3228_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__23));
v___x_3229_ = lean_name_eq(v_ctorName_3220_, v___x_3228_);
lean_dec(v_ctorName_3220_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3230_; 
lean_dec_ref(v_params_3221_);
v___x_3230_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3222_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3235_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___x_3230_, 1);
v___x_3232_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__36));
v___x_3233_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24___closed__0));
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 2, v_a_3231_);
lean_ctor_set(v___x_3224_, 1, v___x_3233_);
lean_ctor_set(v___x_3224_, 0, v___x_3232_);
v___x_3235_ = v___x_3224_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3232_);
lean_ctor_set(v_reuseFailAlloc_3236_, 1, v___x_3233_);
lean_ctor_set(v_reuseFailAlloc_3236_, 2, v_a_3231_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
v_a_3215_ = v___x_3235_;
goto v___jp_3214_;
}
}
else
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
lean_del_object(v___x_3224_);
lean_dec_ref(v_bs_x27_3213_);
lean_dec_ref(v___x_3199_);
v_a_3237_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3239_ = v___x_3230_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3230_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
if (v_isShared_3240_ == 0)
{
v___x_3242_ = v___x_3239_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3237_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
else
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v_fvarId_3247_; lean_object* v_binderName_3248_; lean_object* v_type_3249_; lean_object* v___x_3250_; 
v___x_3245_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_3246_ = lean_array_get(v___x_3245_, v_params_3221_, v___x_3212_);
lean_dec_ref(v_params_3221_);
v_fvarId_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_fvarId_3247_);
v_binderName_3248_ = lean_ctor_get(v___x_3246_, 1);
lean_inc(v_binderName_3248_);
v_type_3249_ = lean_ctor_get(v___x_3246_, 2);
lean_inc_ref(v_type_3249_);
lean_dec(v___x_3246_);
v___x_3250_ = l_Lean_Compiler_LCNF_toMonoType(v_type_3249_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; lean_object* v___x_3252_; lean_object* v_lctx_3253_; lean_object* v_nextIdx_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3283_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
lean_dec_ref_known(v___x_3250_, 1);
v___x_3252_ = lean_st_ref_take(v___y_3205_);
v_lctx_3253_ = lean_ctor_get(v___x_3252_, 0);
v_nextIdx_3254_ = lean_ctor_get(v___x_3252_, 1);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3256_ = v___x_3252_;
v_isShared_3257_ = v_isSharedCheck_3283_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_nextIdx_3254_);
lean_inc(v_lctx_3253_);
lean_dec(v___x_3252_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3283_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3264_; 
v___x_3258_ = lean_box(0);
v___x_3259_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18___closed__1));
lean_inc_ref(v___x_3199_);
v___x_3260_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3259_);
lean_ctor_set(v___x_3260_, 1, v___x_3258_);
lean_ctor_set(v___x_3260_, 2, v___x_3199_);
v___x_3261_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3261_, 0, v_fvarId_3247_);
lean_ctor_set(v___x_3261_, 1, v_binderName_3248_);
lean_ctor_set(v___x_3261_, 2, v_a_3251_);
lean_ctor_set(v___x_3261_, 3, v___x_3260_);
lean_inc_ref(v___x_3261_);
v___x_3262_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3226_, v_lctx_3253_, v___x_3261_);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 0, v___x_3262_);
v___x_3264_ = v___x_3256_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3262_);
lean_ctor_set(v_reuseFailAlloc_3282_, 1, v_nextIdx_3254_);
v___x_3264_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3265_ = lean_st_ref_put(v___y_3205_, v___x_3264_);
v___x_3266_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3222_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3272_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3267_);
lean_dec_ref_known(v___x_3266_, 1);
v___x_3268_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__39));
v___x_3269_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24___closed__0));
v___x_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3261_);
lean_ctor_set(v___x_3270_, 1, v_a_3267_);
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 2, v___x_3270_);
lean_ctor_set(v___x_3224_, 1, v___x_3269_);
lean_ctor_set(v___x_3224_, 0, v___x_3268_);
v___x_3272_ = v___x_3224_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3268_);
lean_ctor_set(v_reuseFailAlloc_3273_, 1, v___x_3269_);
lean_ctor_set(v_reuseFailAlloc_3273_, 2, v___x_3270_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
v_a_3215_ = v___x_3272_;
goto v___jp_3214_;
}
}
else
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
lean_dec_ref_known(v___x_3261_, 4);
lean_del_object(v___x_3224_);
lean_dec_ref(v_bs_x27_3213_);
lean_dec_ref(v___x_3199_);
v_a_3274_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___x_3266_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3266_);
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
}
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
lean_dec(v_binderName_3248_);
lean_dec(v_fvarId_3247_);
lean_del_object(v___x_3224_);
lean_dec_ref(v_code_3222_);
lean_dec_ref(v_bs_x27_3213_);
lean_dec_ref(v___x_3199_);
v_a_3284_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3250_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3250_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
}
else
{
lean_object* v_a_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3299_; 
lean_del_object(v___x_3224_);
lean_dec_ref(v_code_3222_);
lean_dec_ref(v_params_3221_);
lean_dec(v_ctorName_3220_);
lean_dec_ref(v_bs_x27_3213_);
lean_dec_ref(v___x_3199_);
v_a_3292_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3294_ = v___x_3227_;
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_a_3292_);
lean_dec(v___x_3227_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3297_; 
if (v_isShared_3295_ == 0)
{
v___x_3297_ = v___x_3294_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_a_3292_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
}
}
else
{
lean_object* v_code_3301_; lean_object* v___x_3302_; 
v_code_3301_ = lean_ctor_get(v_v_3211_, 0);
lean_inc_ref(v_code_3301_);
v___x_3302_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3301_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_a_3303_; lean_object* v___x_3304_; 
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_a_3303_);
lean_dec_ref_known(v___x_3302_, 1);
v___x_3304_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_3211_, v_a_3303_);
v_a_3215_ = v___x_3304_;
goto v___jp_3214_;
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
lean_dec_ref_known(v_v_3211_, 1);
lean_dec_ref(v_bs_x27_3213_);
lean_dec_ref(v___x_3199_);
v_a_3305_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3302_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3302_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3310_; 
if (v_isShared_3308_ == 0)
{
v___x_3310_ = v___x_3307_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
v___jp_3214_:
{
size_t v___x_3216_; size_t v___x_3217_; lean_object* v___x_3218_; 
v___x_3216_ = ((size_t)1ULL);
v___x_3217_ = lean_usize_add(v_i_3201_, v___x_3216_);
v___x_3218_ = lean_array_uset(v_bs_x27_3213_, v_i_3201_, v_a_3215_);
v_i_3201_ = v___x_3217_;
v_bs_3202_ = v___x_3218_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNOptionToMono___redArg(lean_object* v_c_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_){
_start:
{
lean_object* v_resultType_3320_; lean_object* v_discr_3321_; lean_object* v_alts_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3381_; 
v_resultType_3320_ = lean_ctor_get(v_c_3313_, 1);
v_discr_3321_ = lean_ctor_get(v_c_3313_, 2);
v_alts_3322_ = lean_ctor_get(v_c_3313_, 3);
v_isSharedCheck_3381_ = !lean_is_exclusive(v_c_3313_);
if (v_isSharedCheck_3381_ == 0)
{
lean_object* v_unused_3382_; 
v_unused_3382_ = lean_ctor_get(v_c_3313_, 0);
lean_dec(v_unused_3382_);
v___x_3324_ = v_c_3313_;
v_isShared_3325_ = v_isSharedCheck_3381_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_alts_3322_);
lean_inc(v_discr_3321_);
lean_inc(v_resultType_3320_);
lean_dec(v_c_3313_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3381_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3326_; 
v___x_3326_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3320_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; uint8_t v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v___x_3326_, 1);
v___x_3328_ = 0;
v___x_3329_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__1));
v___x_3330_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
v___x_3331_ = lean_box(0);
v___x_3332_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2, &l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2);
v___x_3333_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__4));
v___x_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3334_, 0, v_discr_3321_);
v___x_3335_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5);
v___x_3336_ = lean_array_push(v___x_3335_, v___x_3334_);
lean_inc_ref(v___x_3336_);
v___x_3337_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3333_);
lean_ctor_set(v___x_3337_, 1, v___x_3331_);
lean_ctor_set(v___x_3337_, 2, v___x_3336_);
v___x_3338_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3328_, v___x_3329_, v___x_3332_, v___x_3337_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; size_t v_sz_3340_; size_t v___x_3341_; lean_object* v___x_3342_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3339_);
lean_dec_ref_known(v___x_3338_, 1);
v_sz_3340_ = lean_array_size(v_alts_3322_);
v___x_3341_ = ((size_t)0ULL);
v___x_3342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18(v___x_3336_, v_sz_3340_, v___x_3341_, v_alts_3322_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3356_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3345_ = v___x_3342_;
v_isShared_3346_ = v_isSharedCheck_3356_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3342_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3356_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v_fvarId_3347_; lean_object* v___x_3349_; 
v_fvarId_3347_ = lean_ctor_get(v_a_3339_, 0);
lean_inc(v_fvarId_3347_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 3, v_a_3343_);
lean_ctor_set(v___x_3324_, 2, v_fvarId_3347_);
lean_ctor_set(v___x_3324_, 1, v_a_3327_);
lean_ctor_set(v___x_3324_, 0, v___x_3330_);
v___x_3349_ = v___x_3324_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3330_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v_a_3327_);
lean_ctor_set(v_reuseFailAlloc_3355_, 2, v_fvarId_3347_);
lean_ctor_set(v_reuseFailAlloc_3355_, 3, v_a_3343_);
v___x_3349_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3353_; 
v___x_3350_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
v___x_3351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3351_, 0, v_a_3339_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 0, v___x_3351_);
v___x_3353_ = v___x_3345_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3351_);
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
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
lean_dec(v_a_3339_);
lean_dec(v_a_3327_);
lean_del_object(v___x_3324_);
v_a_3357_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___x_3342_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3342_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
else
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_dec_ref(v___x_3336_);
lean_dec(v_a_3327_);
lean_del_object(v___x_3324_);
lean_dec_ref(v_alts_3322_);
v_a_3365_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3338_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3338_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
lean_del_object(v___x_3324_);
lean_dec_ref(v_alts_3322_);
lean_dec(v_discr_3321_);
v_a_3373_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3326_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3326_);
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
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3383_ = lean_box(0);
v___x_3384_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0));
v___x_3385_ = l_Lean_mkConst(v___x_3384_, v___x_3383_);
return v___x_3385_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6(void){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3392_ = lean_box(0);
v___x_3393_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3));
v___x_3394_ = l_Lean_mkConst(v___x_3393_, v___x_3392_);
return v___x_3394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20(lean_object* v___x_3424_, size_t v_sz_3425_, size_t v_i_3426_, lean_object* v_bs_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
uint8_t v___x_3434_; 
v___x_3434_ = lean_usize_dec_lt(v_i_3426_, v_sz_3425_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3435_; 
lean_dec(v___x_3424_);
v___x_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3435_, 0, v_bs_3427_);
return v___x_3435_;
}
else
{
lean_object* v_v_3436_; lean_object* v___x_3437_; lean_object* v_bs_x27_3438_; lean_object* v_a_3440_; 
v_v_3436_ = lean_array_uget(v_bs_3427_, v_i_3426_);
v___x_3437_ = lean_unsigned_to_nat(0u);
v_bs_x27_3438_ = lean_array_uset(v_bs_3427_, v_i_3426_, v___x_3437_);
if (lean_obj_tag(v_v_3436_) == 0)
{
lean_object* v_ctorName_3445_; lean_object* v_params_3446_; lean_object* v_code_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3574_; 
v_ctorName_3445_ = lean_ctor_get(v_v_3436_, 0);
v_params_3446_ = lean_ctor_get(v_v_3436_, 1);
v_code_3447_ = lean_ctor_get(v_v_3436_, 2);
v_isSharedCheck_3574_ = !lean_is_exclusive(v_v_3436_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3449_ = v_v_3436_;
v_isShared_3450_ = v_isSharedCheck_3574_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_code_3447_);
lean_inc(v_params_3446_);
lean_inc(v_ctorName_3445_);
lean_dec(v_v_3436_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3574_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
uint8_t v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3451_ = 0;
v___x_3452_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_3453_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3451_, v_params_3446_, v___y_3430_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; uint8_t v___x_3458_; 
lean_dec_ref_known(v___x_3453_, 1);
v___x_3454_ = lean_box(0);
v___x_3455_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3456_ = lean_array_get(v___x_3452_, v_params_3446_, v___x_3437_);
lean_dec_ref(v_params_3446_);
v___x_3457_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__1));
v___x_3458_ = lean_name_eq(v_ctorName_3445_, v___x_3457_);
lean_dec(v_ctorName_3445_);
if (v___x_3458_ == 0)
{
lean_object* v___x_3459_; lean_object* v_fvarId_3460_; lean_object* v_binderName_3461_; lean_object* v_lctx_3462_; lean_object* v_nextIdx_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3494_; 
v___x_3459_ = lean_st_ref_take(v___y_3430_);
v_fvarId_3460_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_fvarId_3460_);
v_binderName_3461_ = lean_ctor_get(v___x_3456_, 1);
lean_inc(v_binderName_3461_);
lean_dec(v___x_3456_);
v_lctx_3462_ = lean_ctor_get(v___x_3459_, 0);
v_nextIdx_3463_ = lean_ctor_get(v___x_3459_, 1);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3465_ = v___x_3459_;
v_isShared_3466_ = v_isSharedCheck_3494_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_nextIdx_3463_);
lean_inc(v_lctx_3462_);
lean_dec(v___x_3459_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3494_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3475_; 
v___x_3467_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__3));
v___x_3468_ = lean_unsigned_to_nat(1u);
v___x_3469_ = lean_mk_empty_array_with_capacity(v___x_3468_);
lean_inc(v___x_3424_);
v___x_3470_ = lean_array_push(v___x_3469_, v___x_3424_);
v___x_3471_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3467_);
lean_ctor_set(v___x_3471_, 1, v___x_3454_);
lean_ctor_set(v___x_3471_, 2, v___x_3470_);
v___x_3472_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3472_, 0, v_fvarId_3460_);
lean_ctor_set(v___x_3472_, 1, v_binderName_3461_);
lean_ctor_set(v___x_3472_, 2, v___x_3455_);
lean_ctor_set(v___x_3472_, 3, v___x_3471_);
lean_inc_ref(v___x_3472_);
v___x_3473_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3451_, v_lctx_3462_, v___x_3472_);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 0, v___x_3473_);
v___x_3475_ = v___x_3465_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3473_);
lean_ctor_set(v_reuseFailAlloc_3493_, 1, v_nextIdx_3463_);
v___x_3475_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3476_ = lean_st_ref_put(v___y_3430_, v___x_3475_);
v___x_3477_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3447_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3483_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref_known(v___x_3477_, 1);
v___x_3479_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__36));
v___x_3480_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24___closed__0));
v___x_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3472_);
lean_ctor_set(v___x_3481_, 1, v_a_3478_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 2, v___x_3481_);
lean_ctor_set(v___x_3449_, 1, v___x_3480_);
lean_ctor_set(v___x_3449_, 0, v___x_3479_);
v___x_3483_ = v___x_3449_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3479_);
lean_ctor_set(v_reuseFailAlloc_3484_, 1, v___x_3480_);
lean_ctor_set(v_reuseFailAlloc_3484_, 2, v___x_3481_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
v_a_3440_ = v___x_3483_;
goto v___jp_3439_;
}
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
lean_dec_ref_known(v___x_3472_, 4);
lean_del_object(v___x_3449_);
lean_dec_ref(v_bs_x27_3438_);
lean_dec(v___x_3424_);
v_a_3485_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3477_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3477_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
}
}
else
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__5));
v___x_3496_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__3));
v___x_3497_ = lean_unsigned_to_nat(1u);
v___x_3498_ = lean_mk_empty_array_with_capacity(v___x_3497_);
lean_inc(v___x_3424_);
v___x_3499_ = lean_array_push(v___x_3498_, v___x_3424_);
v___x_3500_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3496_);
lean_ctor_set(v___x_3500_, 1, v___x_3454_);
lean_ctor_set(v___x_3500_, 2, v___x_3499_);
v___x_3501_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3451_, v___x_3495_, v___x_3455_, v___x_3500_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v___x_3503_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__1));
v___x_3504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__3));
v___x_3505_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3451_, v___x_3503_, v___x_3455_, v___x_3504_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; lean_object* v_fvarId_3507_; lean_object* v_fvarId_3508_; lean_object* v___x_3509_; lean_object* v_fvarId_3510_; lean_object* v_binderName_3511_; lean_object* v_lctx_3512_; lean_object* v_nextIdx_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3549_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3506_);
lean_dec_ref_known(v___x_3505_, 1);
v_fvarId_3507_ = lean_ctor_get(v_a_3502_, 0);
v_fvarId_3508_ = lean_ctor_get(v_a_3506_, 0);
v___x_3509_ = lean_st_ref_take(v___y_3430_);
v_fvarId_3510_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_fvarId_3510_);
v_binderName_3511_ = lean_ctor_get(v___x_3456_, 1);
lean_inc(v_binderName_3511_);
lean_dec(v___x_3456_);
v_lctx_3512_ = lean_ctor_get(v___x_3509_, 0);
v_nextIdx_3513_ = lean_ctor_get(v___x_3509_, 1);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3515_ = v___x_3509_;
v_isShared_3516_ = v_isSharedCheck_3549_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_nextIdx_3513_);
lean_inc(v_lctx_3512_);
lean_dec(v___x_3509_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3549_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3528_; 
v___x_3517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__5));
lean_inc(v_fvarId_3507_);
v___x_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3518_, 0, v_fvarId_3507_);
lean_inc(v_fvarId_3508_);
v___x_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3519_, 0, v_fvarId_3508_);
v___x_3520_ = lean_unsigned_to_nat(2u);
v___x_3521_ = lean_mk_empty_array_with_capacity(v___x_3520_);
v___x_3522_ = lean_array_push(v___x_3521_, v___x_3518_);
v___x_3523_ = lean_array_push(v___x_3522_, v___x_3519_);
v___x_3524_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3517_);
lean_ctor_set(v___x_3524_, 1, v___x_3454_);
lean_ctor_set(v___x_3524_, 2, v___x_3523_);
v___x_3525_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3525_, 0, v_fvarId_3510_);
lean_ctor_set(v___x_3525_, 1, v_binderName_3511_);
lean_ctor_set(v___x_3525_, 2, v___x_3455_);
lean_ctor_set(v___x_3525_, 3, v___x_3524_);
lean_inc_ref(v___x_3525_);
v___x_3526_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3451_, v_lctx_3512_, v___x_3525_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v___x_3526_);
v___x_3528_ = v___x_3515_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3526_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_nextIdx_3513_);
v___x_3528_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3529_ = lean_st_ref_put(v___y_3430_, v___x_3528_);
v___x_3530_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3447_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3538_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3530_, 1);
v___x_3532_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__39));
v___x_3533_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24___closed__0));
v___x_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3525_);
lean_ctor_set(v___x_3534_, 1, v_a_3531_);
v___x_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3535_, 0, v_a_3506_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v___x_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3536_, 0, v_a_3502_);
lean_ctor_set(v___x_3536_, 1, v___x_3535_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 2, v___x_3536_);
lean_ctor_set(v___x_3449_, 1, v___x_3533_);
lean_ctor_set(v___x_3449_, 0, v___x_3532_);
v___x_3538_ = v___x_3449_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3532_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v___x_3533_);
lean_ctor_set(v_reuseFailAlloc_3539_, 2, v___x_3536_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
v_a_3440_ = v___x_3538_;
goto v___jp_3439_;
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec_ref_known(v___x_3525_, 4);
lean_dec(v_a_3506_);
lean_dec(v_a_3502_);
lean_del_object(v___x_3449_);
lean_dec_ref(v_bs_x27_3438_);
lean_dec(v___x_3424_);
v_a_3540_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3530_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3530_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
}
}
else
{
lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3557_; 
lean_dec(v_a_3502_);
lean_dec(v___x_3456_);
lean_del_object(v___x_3449_);
lean_dec_ref(v_code_3447_);
lean_dec_ref(v_bs_x27_3438_);
lean_dec(v___x_3424_);
v_a_3550_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3552_ = v___x_3505_;
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3505_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3555_; 
if (v_isShared_3553_ == 0)
{
v___x_3555_ = v___x_3552_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_a_3550_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
lean_dec(v___x_3456_);
lean_del_object(v___x_3449_);
lean_dec_ref(v_code_3447_);
lean_dec_ref(v_bs_x27_3438_);
lean_dec(v___x_3424_);
v_a_3558_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3560_ = v___x_3501_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3501_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3558_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
}
else
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
lean_del_object(v___x_3449_);
lean_dec_ref(v_code_3447_);
lean_dec_ref(v_params_3446_);
lean_dec(v_ctorName_3445_);
lean_dec_ref(v_bs_x27_3438_);
lean_dec(v___x_3424_);
v_a_3566_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3568_ = v___x_3453_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3453_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
if (v_isShared_3569_ == 0)
{
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3566_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
}
else
{
lean_object* v_code_3575_; lean_object* v___x_3576_; 
v_code_3575_ = lean_ctor_get(v_v_3436_, 0);
lean_inc_ref(v_code_3575_);
v___x_3576_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3575_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v_a_3577_; lean_object* v___x_3578_; 
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc(v_a_3577_);
lean_dec_ref_known(v___x_3576_, 1);
v___x_3578_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_3436_, v_a_3577_);
v_a_3440_ = v___x_3578_;
goto v___jp_3439_;
}
else
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
lean_dec_ref_known(v_v_3436_, 1);
lean_dec_ref(v_bs_x27_3438_);
lean_dec(v___x_3424_);
v_a_3579_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3581_ = v___x_3576_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3576_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3579_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
v___jp_3439_:
{
size_t v___x_3441_; size_t v___x_3442_; lean_object* v___x_3443_; 
v___x_3441_ = ((size_t)1ULL);
v___x_3442_ = lean_usize_add(v_i_3426_, v___x_3441_);
v___x_3443_ = lean_array_uset(v_bs_x27_3438_, v_i_3426_, v_a_3440_);
v_i_3426_ = v___x_3442_;
v_bs_3427_ = v___x_3443_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg(lean_object* v_c_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_){
_start:
{
lean_object* v_resultType_3594_; lean_object* v_discr_3595_; lean_object* v_alts_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3693_; 
v_resultType_3594_ = lean_ctor_get(v_c_3587_, 1);
v_discr_3595_ = lean_ctor_get(v_c_3587_, 2);
v_alts_3596_ = lean_ctor_get(v_c_3587_, 3);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_c_3587_);
if (v_isSharedCheck_3693_ == 0)
{
lean_object* v_unused_3694_; 
v_unused_3694_ = lean_ctor_get(v_c_3587_, 0);
lean_dec(v_unused_3694_);
v___x_3598_ = v_c_3587_;
v_isShared_3599_ = v_isSharedCheck_3693_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_alts_3596_);
lean_inc(v_discr_3595_);
lean_inc(v_resultType_3594_);
lean_dec(v_c_3587_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3693_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3600_; 
v___x_3600_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3594_, v_a_3591_, v_a_3592_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; uint8_t v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref_known(v___x_3600_, 1);
v___x_3602_ = 0;
v___x_3603_ = lean_box(0);
v___x_3604_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3605_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__1));
v___x_3606_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__33));
v___x_3607_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3602_, v___x_3605_, v___x_3604_, v___x_3606_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v_fvarId_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_a_3608_);
lean_dec_ref_known(v___x_3607_, 1);
v_fvarId_3609_ = lean_ctor_get(v_a_3608_, 0);
v___x_3610_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__5));
v___x_3611_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6, &l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6);
v___x_3612_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__8));
lean_inc(v_fvarId_3609_);
v___x_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3613_, 0, v_fvarId_3609_);
v___x_3614_ = lean_unsigned_to_nat(1u);
v___x_3615_ = lean_mk_empty_array_with_capacity(v___x_3614_);
v___x_3616_ = lean_array_push(v___x_3615_, v___x_3613_);
v___x_3617_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3612_);
lean_ctor_set(v___x_3617_, 1, v___x_3603_);
lean_ctor_set(v___x_3617_, 2, v___x_3616_);
v___x_3618_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3602_, v___x_3610_, v___x_3611_, v___x_3617_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v_fvarId_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v___x_3618_, 1);
v_fvarId_3620_ = lean_ctor_get(v_a_3619_, 0);
v___x_3621_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__10));
v___x_3622_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
v___x_3623_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2, &l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2);
v___x_3624_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12));
v___x_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3625_, 0, v_discr_3595_);
lean_inc(v_fvarId_3620_);
v___x_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3626_, 0, v_fvarId_3620_);
v___x_3627_ = lean_unsigned_to_nat(2u);
v___x_3628_ = lean_mk_empty_array_with_capacity(v___x_3627_);
lean_inc_ref(v___x_3625_);
v___x_3629_ = lean_array_push(v___x_3628_, v___x_3625_);
v___x_3630_ = lean_array_push(v___x_3629_, v___x_3626_);
v___x_3631_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3624_);
lean_ctor_set(v___x_3631_, 1, v___x_3603_);
lean_ctor_set(v___x_3631_, 2, v___x_3630_);
v___x_3632_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3602_, v___x_3621_, v___x_3623_, v___x_3631_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; size_t v_sz_3634_; size_t v___x_3635_; lean_object* v___x_3636_; 
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_a_3633_);
lean_dec_ref_known(v___x_3632_, 1);
v_sz_3634_ = lean_array_size(v_alts_3596_);
v___x_3635_ = ((size_t)0ULL);
v___x_3636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20(v___x_3625_, v_sz_3634_, v___x_3635_, v_alts_3596_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3652_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3639_ = v___x_3636_;
v_isShared_3640_ = v_isSharedCheck_3652_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3636_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3652_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v_fvarId_3641_; lean_object* v___x_3643_; 
v_fvarId_3641_ = lean_ctor_get(v_a_3633_, 0);
lean_inc(v_fvarId_3641_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 3, v_a_3637_);
lean_ctor_set(v___x_3598_, 2, v_fvarId_3641_);
lean_ctor_set(v___x_3598_, 1, v_a_3601_);
lean_ctor_set(v___x_3598_, 0, v___x_3622_);
v___x_3643_ = v___x_3598_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3622_);
lean_ctor_set(v_reuseFailAlloc_3651_, 1, v_a_3601_);
lean_ctor_set(v_reuseFailAlloc_3651_, 2, v_fvarId_3641_);
lean_ctor_set(v_reuseFailAlloc_3651_, 3, v_a_3637_);
v___x_3643_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3649_; 
v___x_3644_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
v___x_3645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3645_, 0, v_a_3633_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
v___x_3646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3646_, 0, v_a_3619_);
lean_ctor_set(v___x_3646_, 1, v___x_3645_);
v___x_3647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3647_, 0, v_a_3608_);
lean_ctor_set(v___x_3647_, 1, v___x_3646_);
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 0, v___x_3647_);
v___x_3649_ = v___x_3639_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3647_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
else
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3660_; 
lean_dec(v_a_3633_);
lean_dec(v_a_3619_);
lean_dec(v_a_3608_);
lean_dec(v_a_3601_);
lean_del_object(v___x_3598_);
v_a_3653_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3655_ = v___x_3636_;
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3636_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3658_; 
if (v_isShared_3656_ == 0)
{
v___x_3658_ = v___x_3655_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_a_3653_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
}
else
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
lean_dec_ref_known(v___x_3625_, 1);
lean_dec(v_a_3619_);
lean_dec(v_a_3608_);
lean_dec(v_a_3601_);
lean_del_object(v___x_3598_);
lean_dec_ref(v_alts_3596_);
v_a_3661_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___x_3632_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3632_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3666_; 
if (v_isShared_3664_ == 0)
{
v___x_3666_ = v___x_3663_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3661_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
else
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3676_; 
lean_dec(v_a_3608_);
lean_dec(v_a_3601_);
lean_del_object(v___x_3598_);
lean_dec_ref(v_alts_3596_);
lean_dec(v_discr_3595_);
v_a_3669_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3671_ = v___x_3618_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3618_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3674_; 
if (v_isShared_3672_ == 0)
{
v___x_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3669_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
lean_dec(v_a_3601_);
lean_del_object(v___x_3598_);
lean_dec_ref(v_alts_3596_);
lean_dec(v_discr_3595_);
v_a_3677_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3607_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3607_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
else
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
lean_del_object(v___x_3598_);
lean_dec_ref(v_alts_3596_);
lean_dec(v_discr_3595_);
v_a_3685_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3687_ = v___x_3600_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3600_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22(lean_object* v___x_3704_, size_t v_sz_3705_, size_t v_i_3706_, lean_object* v_bs_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
uint8_t v___x_3714_; 
v___x_3714_ = lean_usize_dec_lt(v_i_3706_, v_sz_3705_);
if (v___x_3714_ == 0)
{
lean_object* v___x_3715_; 
lean_dec(v___x_3704_);
v___x_3715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3715_, 0, v_bs_3707_);
return v___x_3715_;
}
else
{
lean_object* v_v_3716_; lean_object* v___x_3717_; lean_object* v_bs_x27_3718_; lean_object* v_a_3720_; 
v_v_3716_ = lean_array_uget(v_bs_3707_, v_i_3706_);
v___x_3717_ = lean_unsigned_to_nat(0u);
v_bs_x27_3718_ = lean_array_uset(v_bs_3707_, v_i_3706_, v___x_3717_);
if (lean_obj_tag(v_v_3716_) == 0)
{
lean_object* v_ctorName_3725_; lean_object* v_params_3726_; lean_object* v_code_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3814_; 
v_ctorName_3725_ = lean_ctor_get(v_v_3716_, 0);
v_params_3726_ = lean_ctor_get(v_v_3716_, 1);
v_code_3727_ = lean_ctor_get(v_v_3716_, 2);
v_isSharedCheck_3814_ = !lean_is_exclusive(v_v_3716_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3729_ = v_v_3716_;
v_isShared_3730_ = v_isSharedCheck_3814_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_code_3727_);
lean_inc(v_params_3726_);
lean_inc(v_ctorName_3725_);
lean_dec(v_v_3716_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3814_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
uint8_t v___x_3731_; lean_object* v___x_3732_; 
v___x_3731_ = 0;
v___x_3732_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3731_, v_params_3726_, v___y_3710_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v___x_3733_; uint8_t v___x_3734_; 
lean_dec_ref_known(v___x_3732_, 1);
v___x_3733_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__18));
v___x_3734_ = lean_name_eq(v_ctorName_3725_, v___x_3733_);
lean_dec(v_ctorName_3725_);
if (v___x_3734_ == 0)
{
lean_object* v___x_3735_; 
lean_dec_ref(v_params_3726_);
v___x_3735_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3727_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3740_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3736_);
lean_dec_ref_known(v___x_3735_, 1);
v___x_3737_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__39));
v___x_3738_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24___closed__0));
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 2, v_a_3736_);
lean_ctor_set(v___x_3729_, 1, v___x_3738_);
lean_ctor_set(v___x_3729_, 0, v___x_3737_);
v___x_3740_ = v___x_3729_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3741_, 1, v___x_3738_);
lean_ctor_set(v_reuseFailAlloc_3741_, 2, v_a_3736_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
v_a_3720_ = v___x_3740_;
goto v___jp_3719_;
}
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
lean_del_object(v___x_3729_);
lean_dec_ref(v_bs_x27_3718_);
lean_dec(v___x_3704_);
v_a_3742_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3735_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3735_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
else
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3750_ = lean_box(0);
v___x_3751_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3752_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_3753_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__1));
v___x_3754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__3));
v___x_3755_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3731_, v___x_3753_, v___x_3751_, v___x_3754_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3756_; lean_object* v_fvarId_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v_fvarId_3760_; lean_object* v_binderName_3761_; lean_object* v_lctx_3762_; lean_object* v_nextIdx_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3797_; 
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_a_3756_);
lean_dec_ref_known(v___x_3755_, 1);
v_fvarId_3757_ = lean_ctor_get(v_a_3756_, 0);
v___x_3758_ = lean_st_ref_take(v___y_3710_);
v___x_3759_ = lean_array_get(v___x_3752_, v_params_3726_, v___x_3717_);
lean_dec_ref(v_params_3726_);
v_fvarId_3760_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_fvarId_3760_);
v_binderName_3761_ = lean_ctor_get(v___x_3759_, 1);
lean_inc(v_binderName_3761_);
lean_dec(v___x_3759_);
v_lctx_3762_ = lean_ctor_get(v___x_3758_, 0);
v_nextIdx_3763_ = lean_ctor_get(v___x_3758_, 1);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3765_ = v___x_3758_;
v_isShared_3766_ = v_isSharedCheck_3797_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_nextIdx_3763_);
lean_inc(v_lctx_3762_);
lean_dec(v___x_3758_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3797_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3777_; 
v___x_3767_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__5));
lean_inc(v_fvarId_3757_);
v___x_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3768_, 0, v_fvarId_3757_);
v___x_3769_ = lean_unsigned_to_nat(2u);
v___x_3770_ = lean_mk_empty_array_with_capacity(v___x_3769_);
lean_inc(v___x_3704_);
v___x_3771_ = lean_array_push(v___x_3770_, v___x_3704_);
v___x_3772_ = lean_array_push(v___x_3771_, v___x_3768_);
v___x_3773_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3767_);
lean_ctor_set(v___x_3773_, 1, v___x_3750_);
lean_ctor_set(v___x_3773_, 2, v___x_3772_);
v___x_3774_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3774_, 0, v_fvarId_3760_);
lean_ctor_set(v___x_3774_, 1, v_binderName_3761_);
lean_ctor_set(v___x_3774_, 2, v___x_3751_);
lean_ctor_set(v___x_3774_, 3, v___x_3773_);
lean_inc_ref(v___x_3774_);
v___x_3775_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3731_, v_lctx_3762_, v___x_3774_);
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 0, v___x_3775_);
v___x_3777_ = v___x_3765_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3775_);
lean_ctor_set(v_reuseFailAlloc_3796_, 1, v_nextIdx_3763_);
v___x_3777_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3778_ = lean_st_ref_put(v___y_3710_, v___x_3777_);
v___x_3779_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3727_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3786_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3780_);
lean_dec_ref_known(v___x_3779_, 1);
v___x_3781_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__36));
v___x_3782_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24___closed__0));
v___x_3783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3774_);
lean_ctor_set(v___x_3783_, 1, v_a_3780_);
v___x_3784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3784_, 0, v_a_3756_);
lean_ctor_set(v___x_3784_, 1, v___x_3783_);
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 2, v___x_3784_);
lean_ctor_set(v___x_3729_, 1, v___x_3782_);
lean_ctor_set(v___x_3729_, 0, v___x_3781_);
v___x_3786_ = v___x_3729_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v___x_3781_);
lean_ctor_set(v_reuseFailAlloc_3787_, 1, v___x_3782_);
lean_ctor_set(v_reuseFailAlloc_3787_, 2, v___x_3784_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
v_a_3720_ = v___x_3786_;
goto v___jp_3719_;
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_dec_ref_known(v___x_3774_, 4);
lean_dec(v_a_3756_);
lean_del_object(v___x_3729_);
lean_dec_ref(v_bs_x27_3718_);
lean_dec(v___x_3704_);
v_a_3788_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3779_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3779_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
}
}
else
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
lean_del_object(v___x_3729_);
lean_dec_ref(v_code_3727_);
lean_dec_ref(v_params_3726_);
lean_dec_ref(v_bs_x27_3718_);
lean_dec(v___x_3704_);
v_a_3798_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3755_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3755_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_del_object(v___x_3729_);
lean_dec_ref(v_code_3727_);
lean_dec_ref(v_params_3726_);
lean_dec(v_ctorName_3725_);
lean_dec_ref(v_bs_x27_3718_);
lean_dec(v___x_3704_);
v_a_3806_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3732_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3732_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
else
{
lean_object* v_code_3815_; lean_object* v___x_3816_; 
v_code_3815_ = lean_ctor_get(v_v_3716_, 0);
lean_inc_ref(v_code_3815_);
v___x_3816_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3815_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v_a_3817_; lean_object* v___x_3818_; 
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_a_3817_);
lean_dec_ref_known(v___x_3816_, 1);
v___x_3818_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_3716_, v_a_3817_);
v_a_3720_ = v___x_3818_;
goto v___jp_3719_;
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
lean_dec_ref_known(v_v_3716_, 1);
lean_dec_ref(v_bs_x27_3718_);
lean_dec(v___x_3704_);
v_a_3819_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3821_ = v___x_3816_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3816_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3819_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
v___jp_3719_:
{
size_t v___x_3721_; size_t v___x_3722_; lean_object* v___x_3723_; 
v___x_3721_ = ((size_t)1ULL);
v___x_3722_ = lean_usize_add(v_i_3706_, v___x_3721_);
v___x_3723_ = lean_array_uset(v_bs_x27_3718_, v_i_3706_, v_a_3720_);
v_i_3706_ = v___x_3722_;
v_bs_3707_ = v___x_3723_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg(lean_object* v_c_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_){
_start:
{
lean_object* v_resultType_3834_; lean_object* v_discr_3835_; lean_object* v_alts_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3913_; 
v_resultType_3834_ = lean_ctor_get(v_c_3827_, 1);
v_discr_3835_ = lean_ctor_get(v_c_3827_, 2);
v_alts_3836_ = lean_ctor_get(v_c_3827_, 3);
v_isSharedCheck_3913_ = !lean_is_exclusive(v_c_3827_);
if (v_isSharedCheck_3913_ == 0)
{
lean_object* v_unused_3914_; 
v_unused_3914_ = lean_ctor_get(v_c_3827_, 0);
lean_dec(v_unused_3914_);
v___x_3838_ = v_c_3827_;
v_isShared_3839_ = v_isSharedCheck_3913_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_alts_3836_);
lean_inc(v_discr_3835_);
lean_inc(v_resultType_3834_);
lean_dec(v_c_3827_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3913_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3840_; 
v___x_3840_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3834_, v_a_3831_, v_a_3832_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; uint8_t v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
lean_inc(v_a_3841_);
lean_dec_ref_known(v___x_3840_, 1);
v___x_3842_ = 0;
v___x_3843_ = lean_box(0);
v___x_3844_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3845_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__2));
v___x_3846_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__33));
v___x_3847_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3842_, v___x_3845_, v___x_3844_, v___x_3846_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v_a_3848_; lean_object* v_fvarId_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_a_3848_);
lean_dec_ref_known(v___x_3847_, 1);
v_fvarId_3849_ = lean_ctor_get(v_a_3848_, 0);
v___x_3850_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__4));
v___x_3851_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
v___x_3852_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2, &l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2);
v___x_3853_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6));
v___x_3854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3854_, 0, v_discr_3835_);
lean_inc(v_fvarId_3849_);
v___x_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3855_, 0, v_fvarId_3849_);
v___x_3856_ = lean_unsigned_to_nat(2u);
v___x_3857_ = lean_mk_empty_array_with_capacity(v___x_3856_);
lean_inc_ref(v___x_3854_);
v___x_3858_ = lean_array_push(v___x_3857_, v___x_3854_);
v___x_3859_ = lean_array_push(v___x_3858_, v___x_3855_);
v___x_3860_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3853_);
lean_ctor_set(v___x_3860_, 1, v___x_3843_);
lean_ctor_set(v___x_3860_, 2, v___x_3859_);
v___x_3861_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3842_, v___x_3850_, v___x_3852_, v___x_3860_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v_a_3862_; size_t v_sz_3863_; size_t v___x_3864_; lean_object* v___x_3865_; 
v_a_3862_ = lean_ctor_get(v___x_3861_, 0);
lean_inc(v_a_3862_);
lean_dec_ref_known(v___x_3861_, 1);
v_sz_3863_ = lean_array_size(v_alts_3836_);
v___x_3864_ = ((size_t)0ULL);
v___x_3865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22(v___x_3854_, v_sz_3863_, v___x_3864_, v_alts_3836_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_);
if (lean_obj_tag(v___x_3865_) == 0)
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3880_; 
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3868_ = v___x_3865_;
v_isShared_3869_ = v_isSharedCheck_3880_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3865_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3880_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v_fvarId_3870_; lean_object* v___x_3872_; 
v_fvarId_3870_ = lean_ctor_get(v_a_3862_, 0);
lean_inc(v_fvarId_3870_);
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 3, v_a_3866_);
lean_ctor_set(v___x_3838_, 2, v_fvarId_3870_);
lean_ctor_set(v___x_3838_, 1, v_a_3841_);
lean_ctor_set(v___x_3838_, 0, v___x_3851_);
v___x_3872_ = v___x_3838_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3851_);
lean_ctor_set(v_reuseFailAlloc_3879_, 1, v_a_3841_);
lean_ctor_set(v_reuseFailAlloc_3879_, 2, v_fvarId_3870_);
lean_ctor_set(v_reuseFailAlloc_3879_, 3, v_a_3866_);
v___x_3872_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3877_; 
v___x_3873_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3872_);
v___x_3874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3874_, 0, v_a_3862_);
lean_ctor_set(v___x_3874_, 1, v___x_3873_);
v___x_3875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3875_, 0, v_a_3848_);
lean_ctor_set(v___x_3875_, 1, v___x_3874_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 0, v___x_3875_);
v___x_3877_ = v___x_3868_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3875_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
else
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3888_; 
lean_dec(v_a_3862_);
lean_dec(v_a_3848_);
lean_dec(v_a_3841_);
lean_del_object(v___x_3838_);
v_a_3881_ = lean_ctor_get(v___x_3865_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3883_ = v___x_3865_;
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3865_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3886_; 
if (v_isShared_3884_ == 0)
{
v___x_3886_ = v___x_3883_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3881_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
else
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
lean_dec_ref_known(v___x_3854_, 1);
lean_dec(v_a_3848_);
lean_dec(v_a_3841_);
lean_del_object(v___x_3838_);
lean_dec_ref(v_alts_3836_);
v_a_3889_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3861_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3861_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
else
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
lean_dec(v_a_3841_);
lean_del_object(v___x_3838_);
lean_dec_ref(v_alts_3836_);
lean_dec(v_discr_3835_);
v_a_3897_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3899_ = v___x_3847_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3847_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
}
}
else
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3912_; 
lean_del_object(v___x_3838_);
lean_dec_ref(v_alts_3836_);
lean_dec(v_discr_3835_);
v_a_3905_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3907_ = v___x_3840_;
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3840_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3905_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono(lean_object* v_code_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_){
_start:
{
lean_object* v___y_3929_; lean_object* v___y_3930_; uint8_t v___y_3931_; lean_object* v___y_3936_; lean_object* v___y_3937_; uint8_t v___y_3938_; lean_object* v_decl_3943_; lean_object* v_k_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3990_; lean_object* v___y_3991_; uint8_t v___y_3992_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; 
switch(lean_obj_tag(v_code_3921_))
{
case 0:
{
lean_object* v_decl_4004_; lean_object* v_k_4005_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v_value_4030_; 
v_decl_4004_ = lean_ctor_get(v_code_3921_, 0);
v_k_4005_ = lean_ctor_get(v_code_3921_, 1);
v_value_4030_ = lean_ctor_get(v_decl_4004_, 3);
lean_inc(v_value_4030_);
if (lean_obj_tag(v_value_4030_) == 3)
{
lean_object* v_declName_4031_; 
v_declName_4031_ = lean_ctor_get(v_value_4030_, 0);
lean_inc(v_declName_4031_);
if (lean_obj_tag(v_declName_4031_) == 1)
{
lean_object* v_pre_4032_; 
v_pre_4032_ = lean_ctor_get(v_declName_4031_, 0);
lean_inc(v_pre_4032_);
if (lean_obj_tag(v_pre_4032_) == 1)
{
lean_object* v_pre_4033_; 
v_pre_4033_ = lean_ctor_get(v_pre_4032_, 0);
if (lean_obj_tag(v_pre_4033_) == 0)
{
lean_object* v_type_4034_; lean_object* v_args_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4105_; 
v_type_4034_ = lean_ctor_get(v_decl_4004_, 2);
v_args_4035_ = lean_ctor_get(v_value_4030_, 2);
v_isSharedCheck_4105_ = !lean_is_exclusive(v_value_4030_);
if (v_isSharedCheck_4105_ == 0)
{
lean_object* v_unused_4106_; lean_object* v_unused_4107_; 
v_unused_4106_ = lean_ctor_get(v_value_4030_, 1);
lean_dec(v_unused_4106_);
v_unused_4107_ = lean_ctor_get(v_value_4030_, 0);
lean_dec(v_unused_4107_);
v___x_4037_ = v_value_4030_;
v_isShared_4038_ = v_isSharedCheck_4105_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_args_4035_);
lean_dec(v_value_4030_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4105_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v_str_4039_; lean_object* v_str_4040_; lean_object* v___x_4041_; uint8_t v___x_4042_; 
v_str_4039_ = lean_ctor_get(v_declName_4031_, 1);
lean_inc_ref(v_str_4039_);
lean_dec_ref_known(v_declName_4031_, 2);
v_str_4040_ = lean_ctor_get(v_pre_4032_, 1);
lean_inc_ref(v_str_4040_);
lean_dec_ref_known(v_pre_4032_, 2);
v___x_4041_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__14));
v___x_4042_ = lean_string_dec_eq(v_str_4040_, v___x_4041_);
lean_dec_ref(v_str_4040_);
if (v___x_4042_ == 0)
{
lean_dec_ref(v_str_4039_);
lean_del_object(v___x_4037_);
lean_dec_ref(v_args_4035_);
v___y_4007_ = v_a_3922_;
v___y_4008_ = v_a_3923_;
v___y_4009_ = v_a_3924_;
v___y_4010_ = v_a_3925_;
v___y_4011_ = v_a_3926_;
goto v___jp_4006_;
}
else
{
lean_object* v___x_4043_; uint8_t v___x_4044_; 
v___x_4043_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__17));
v___x_4044_ = lean_string_dec_eq(v_str_4039_, v___x_4043_);
lean_dec_ref(v_str_4039_);
if (v___x_4044_ == 0)
{
lean_del_object(v___x_4037_);
lean_dec_ref(v_args_4035_);
v___y_4007_ = v_a_3922_;
v___y_4008_ = v_a_3923_;
v___y_4009_ = v_a_3924_;
v___y_4010_ = v_a_3925_;
v___y_4011_ = v_a_3926_;
goto v___jp_4006_;
}
else
{
lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4102_; 
lean_inc_ref(v_type_4034_);
lean_inc_ref(v_k_4005_);
lean_inc_ref(v_decl_4004_);
v_isSharedCheck_4102_ = !lean_is_exclusive(v_code_3921_);
if (v_isSharedCheck_4102_ == 0)
{
lean_object* v_unused_4103_; lean_object* v_unused_4104_; 
v_unused_4103_ = lean_ctor_get(v_code_3921_, 1);
lean_dec(v_unused_4103_);
v_unused_4104_ = lean_ctor_get(v_code_3921_, 0);
lean_dec(v_unused_4104_);
v___x_4046_ = v_code_3921_;
v_isShared_4047_ = v_isSharedCheck_4102_;
goto v_resetjp_4045_;
}
else
{
lean_dec(v_code_3921_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4102_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; uint8_t v___x_4050_; 
v___x_4048_ = lean_array_get_size(v_args_4035_);
v___x_4049_ = lean_unsigned_to_nat(1u);
v___x_4050_ = lean_nat_dec_eq(v___x_4048_, v___x_4049_);
if (v___x_4050_ == 0)
{
lean_object* v___x_4051_; lean_object* v___x_4052_; 
lean_del_object(v___x_4046_);
lean_del_object(v___x_4037_);
lean_dec_ref(v_args_4035_);
lean_dec_ref(v_type_4034_);
lean_dec_ref(v_k_4005_);
lean_dec_ref(v_decl_4004_);
v___x_4051_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__5, &l_Lean_Compiler_LCNF_Code_toMono___closed__5_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__5);
v___x_4052_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_4051_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_4052_;
}
else
{
uint8_t v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4053_ = 0;
v___x_4054_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__3));
v___x_4055_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3));
v___x_4056_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_4053_, v___x_4054_, v___x_4055_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_object* v_a_4057_; lean_object* v_fvarId_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4069_; 
v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
lean_inc(v_a_4057_);
lean_dec_ref_known(v___x_4056_, 1);
v_fvarId_4058_ = lean_ctor_get(v_a_4057_, 0);
v___x_4059_ = lean_unsigned_to_nat(0u);
v___x_4060_ = lean_array_fget(v_args_4035_, v___x_4059_);
lean_dec_ref(v_args_4035_);
v___x_4061_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__7));
v___x_4062_ = lean_box(0);
lean_inc(v_fvarId_4058_);
v___x_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4063_, 0, v_fvarId_4058_);
v___x_4064_ = lean_unsigned_to_nat(2u);
v___x_4065_ = lean_mk_empty_array_with_capacity(v___x_4064_);
v___x_4066_ = lean_array_push(v___x_4065_, v___x_4060_);
v___x_4067_ = lean_array_push(v___x_4066_, v___x_4063_);
if (v_isShared_4038_ == 0)
{
lean_ctor_set(v___x_4037_, 2, v___x_4067_);
lean_ctor_set(v___x_4037_, 1, v___x_4062_);
lean_ctor_set(v___x_4037_, 0, v___x_4061_);
v___x_4069_ = v___x_4037_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_4061_);
lean_ctor_set(v_reuseFailAlloc_4093_, 1, v___x_4062_);
lean_ctor_set(v_reuseFailAlloc_4093_, 2, v___x_4067_);
v___x_4069_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
lean_object* v___x_4070_; 
v___x_4070_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_4053_, v_decl_4004_, v_type_4034_, v___x_4069_, v_a_3924_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_object* v_a_4071_; lean_object* v___x_4072_; 
v_a_4071_ = lean_ctor_get(v___x_4070_, 0);
lean_inc(v_a_4071_);
lean_dec_ref_known(v___x_4070_, 1);
v___x_4072_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_4005_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4084_; 
v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4084_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4084_ == 0)
{
v___x_4075_ = v___x_4072_;
v_isShared_4076_ = v_isSharedCheck_4084_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4072_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4084_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4047_ == 0)
{
lean_ctor_set(v___x_4046_, 1, v_a_4073_);
lean_ctor_set(v___x_4046_, 0, v_a_4071_);
v___x_4078_ = v___x_4046_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_a_4071_);
lean_ctor_set(v_reuseFailAlloc_4083_, 1, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
lean_object* v___x_4079_; lean_object* v___x_4081_; 
v___x_4079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4079_, 0, v_a_4057_);
lean_ctor_set(v___x_4079_, 1, v___x_4078_);
if (v_isShared_4076_ == 0)
{
lean_ctor_set(v___x_4075_, 0, v___x_4079_);
v___x_4081_ = v___x_4075_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v___x_4079_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
}
else
{
lean_dec(v_a_4071_);
lean_dec(v_a_4057_);
lean_del_object(v___x_4046_);
return v___x_4072_;
}
}
else
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4092_; 
lean_dec(v_a_4057_);
lean_del_object(v___x_4046_);
lean_dec_ref(v_k_4005_);
v_a_4085_ = lean_ctor_get(v___x_4070_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4087_ = v___x_4070_;
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_4070_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4090_; 
if (v_isShared_4088_ == 0)
{
v___x_4090_ = v___x_4087_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_a_4085_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
}
else
{
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4101_; 
lean_del_object(v___x_4046_);
lean_del_object(v___x_4037_);
lean_dec_ref(v_args_4035_);
lean_dec_ref(v_type_4034_);
lean_dec_ref(v_k_4005_);
lean_dec_ref(v_decl_4004_);
v_a_4094_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4096_ = v___x_4056_;
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v___x_4056_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4099_; 
if (v_isShared_4097_ == 0)
{
v___x_4099_ = v___x_4096_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_a_4094_);
v___x_4099_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
return v___x_4099_;
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
lean_dec_ref_known(v_pre_4032_, 2);
lean_dec_ref_known(v_declName_4031_, 2);
lean_dec_ref_known(v_value_4030_, 3);
v___y_4007_ = v_a_3922_;
v___y_4008_ = v_a_3923_;
v___y_4009_ = v_a_3924_;
v___y_4010_ = v_a_3925_;
v___y_4011_ = v_a_3926_;
goto v___jp_4006_;
}
}
else
{
lean_dec(v_pre_4032_);
lean_dec_ref_known(v_declName_4031_, 2);
lean_dec_ref_known(v_value_4030_, 3);
v___y_4007_ = v_a_3922_;
v___y_4008_ = v_a_3923_;
v___y_4009_ = v_a_3924_;
v___y_4010_ = v_a_3925_;
v___y_4011_ = v_a_3926_;
goto v___jp_4006_;
}
}
else
{
lean_dec_ref_known(v_value_4030_, 3);
lean_dec(v_declName_4031_);
v___y_4007_ = v_a_3922_;
v___y_4008_ = v_a_3923_;
v___y_4009_ = v_a_3924_;
v___y_4010_ = v_a_3925_;
v___y_4011_ = v_a_3926_;
goto v___jp_4006_;
}
}
else
{
lean_dec(v_value_4030_);
v___y_4007_ = v_a_3922_;
v___y_4008_ = v_a_3923_;
v___y_4009_ = v_a_3924_;
v___y_4010_ = v_a_3925_;
v___y_4011_ = v_a_3926_;
goto v___jp_4006_;
}
v___jp_4006_:
{
lean_object* v___x_4012_; 
lean_inc_ref(v_decl_4004_);
v___x_4012_ = l_Lean_Compiler_LCNF_LetDecl_toMono(v_decl_4004_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_object* v_a_4013_; lean_object* v___x_4014_; 
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
lean_inc(v_a_4013_);
lean_dec_ref_known(v___x_4012_, 1);
lean_inc_ref(v_k_4005_);
v___x_4014_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_4005_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v_a_4015_; size_t v___x_4016_; size_t v___x_4017_; uint8_t v___x_4018_; 
v_a_4015_ = lean_ctor_get(v___x_4014_, 0);
lean_inc(v_a_4015_);
lean_dec_ref_known(v___x_4014_, 1);
v___x_4016_ = lean_ptr_addr(v_k_4005_);
v___x_4017_ = lean_ptr_addr(v_a_4015_);
v___x_4018_ = lean_usize_dec_eq(v___x_4016_, v___x_4017_);
if (v___x_4018_ == 0)
{
v___y_3990_ = v_a_4015_;
v___y_3991_ = v_a_4013_;
v___y_3992_ = v___x_4018_;
goto v___jp_3989_;
}
else
{
size_t v___x_4019_; size_t v___x_4020_; uint8_t v___x_4021_; 
v___x_4019_ = lean_ptr_addr(v_decl_4004_);
v___x_4020_ = lean_ptr_addr(v_a_4013_);
v___x_4021_ = lean_usize_dec_eq(v___x_4019_, v___x_4020_);
v___y_3990_ = v_a_4015_;
v___y_3991_ = v_a_4013_;
v___y_3992_ = v___x_4021_;
goto v___jp_3989_;
}
}
else
{
lean_dec(v_a_4013_);
lean_dec_ref_known(v_code_3921_, 2);
return v___x_4014_;
}
}
else
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4029_; 
lean_dec_ref_known(v_code_3921_, 2);
v_a_4022_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4024_ = v___x_4012_;
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_4012_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4027_; 
if (v_isShared_4025_ == 0)
{
v___x_4027_ = v___x_4024_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_a_4022_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_4108_; lean_object* v_args_4109_; size_t v_sz_4110_; size_t v___x_4111_; lean_object* v___x_4112_; 
v_fvarId_4108_ = lean_ctor_get(v_code_3921_, 0);
v_args_4109_ = lean_ctor_get(v_code_3921_, 1);
v_sz_4110_ = lean_array_size(v_args_4109_);
v___x_4111_ = ((size_t)0ULL);
lean_inc_ref(v_args_4109_);
v___x_4112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_4110_, v___x_4111_, v_args_4109_, v_a_3922_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4138_; 
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4115_ = v___x_4112_;
v_isShared_4116_ = v_isSharedCheck_4138_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_4112_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4138_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
uint8_t v___y_4118_; uint8_t v___x_4134_; 
v___x_4134_ = l_Lean_instBEqFVarId_beq(v_fvarId_4108_, v_fvarId_4108_);
if (v___x_4134_ == 0)
{
v___y_4118_ = v___x_4134_;
goto v___jp_4117_;
}
else
{
size_t v___x_4135_; size_t v___x_4136_; uint8_t v___x_4137_; 
v___x_4135_ = lean_ptr_addr(v_args_4109_);
v___x_4136_ = lean_ptr_addr(v_a_4113_);
v___x_4137_ = lean_usize_dec_eq(v___x_4135_, v___x_4136_);
v___y_4118_ = v___x_4137_;
goto v___jp_4117_;
}
v___jp_4117_:
{
if (v___y_4118_ == 0)
{
lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4128_; 
lean_inc(v_fvarId_4108_);
v_isSharedCheck_4128_ = !lean_is_exclusive(v_code_3921_);
if (v_isSharedCheck_4128_ == 0)
{
lean_object* v_unused_4129_; lean_object* v_unused_4130_; 
v_unused_4129_ = lean_ctor_get(v_code_3921_, 1);
lean_dec(v_unused_4129_);
v_unused_4130_ = lean_ctor_get(v_code_3921_, 0);
lean_dec(v_unused_4130_);
v___x_4120_ = v_code_3921_;
v_isShared_4121_ = v_isSharedCheck_4128_;
goto v_resetjp_4119_;
}
else
{
lean_dec(v_code_3921_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4128_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 1, v_a_4113_);
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_fvarId_4108_);
lean_ctor_set(v_reuseFailAlloc_4127_, 1, v_a_4113_);
v___x_4123_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
lean_object* v___x_4125_; 
if (v_isShared_4116_ == 0)
{
lean_ctor_set(v___x_4115_, 0, v___x_4123_);
v___x_4125_ = v___x_4115_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4123_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
else
{
lean_object* v___x_4132_; 
lean_dec(v_a_4113_);
if (v_isShared_4116_ == 0)
{
lean_ctor_set(v___x_4115_, 0, v_code_3921_);
v___x_4132_ = v___x_4115_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_code_3921_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
}
}
else
{
lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4146_; 
lean_dec_ref_known(v_code_3921_, 2);
v_a_4139_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4141_ = v___x_4112_;
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v___x_4112_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4144_; 
if (v_isShared_4142_ == 0)
{
v___x_4144_ = v___x_4141_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_a_4139_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
}
case 4:
{
lean_object* v_cases_4147_; lean_object* v___x_4148_; lean_object* v_typeName_4149_; lean_object* v_resultType_4150_; lean_object* v_discr_4151_; lean_object* v_alts_4152_; uint8_t v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4187_; lean_object* v___y_4188_; uint8_t v___y_4189_; lean_object* v_env_4287_; lean_object* v___x_4288_; uint8_t v___x_4289_; 
v_cases_4147_ = lean_ctor_get(v_code_3921_, 0);
v___x_4148_ = lean_st_ref_get(v_a_3926_);
v_typeName_4149_ = lean_ctor_get(v_cases_4147_, 0);
v_resultType_4150_ = lean_ctor_get(v_cases_4147_, 1);
v_discr_4151_ = lean_ctor_get(v_cases_4147_, 2);
v_alts_4152_ = lean_ctor_get(v_cases_4147_, 3);
v_env_4287_ = lean_ctor_get(v___x_4148_, 0);
lean_inc_ref(v_env_4287_);
lean_dec(v___x_4148_);
v___x_4288_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__25));
v___x_4289_ = lean_name_eq(v_typeName_4149_, v___x_4288_);
if (v___x_4289_ == 0)
{
lean_dec_ref(v_env_4287_);
goto v___jp_4192_;
}
else
{
lean_object* v___x_4290_; uint8_t v___x_4291_; 
v___x_4290_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__27));
v___x_4291_ = l_Lean_Environment_contains(v_env_4287_, v___x_4290_, v___x_4289_);
if (v___x_4291_ == 0)
{
lean_object* v___x_4292_; 
lean_inc_ref(v_cases_4147_);
lean_dec_ref_known(v_code_3921_, 1);
v___x_4292_ = l_Lean_Compiler_LCNF_decToMono___redArg(v_cases_4147_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_4292_;
}
else
{
goto v___jp_4192_;
}
}
v___jp_4153_:
{
size_t v_sz_4157_; size_t v___x_4158_; lean_object* v___x_4159_; 
v_sz_4157_ = lean_array_size(v_alts_4152_);
v___x_4158_ = ((size_t)0ULL);
v___x_4159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(v___y_4156_, v___y_4154_, v_sz_4157_, v___x_4158_, v_alts_4152_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4171_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4162_ = v___x_4159_;
v_isShared_4163_ = v_isSharedCheck_4171_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___x_4159_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4171_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4169_; 
v___x_4164_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4));
v___x_4165_ = l_Lean_Name_append(v_typeName_4149_, v___x_4164_);
v___x_4166_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4165_);
lean_ctor_set(v___x_4166_, 1, v___y_4155_);
lean_ctor_set(v___x_4166_, 2, v_discr_4151_);
lean_ctor_set(v___x_4166_, 3, v_a_4160_);
v___x_4167_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4166_);
if (v_isShared_4163_ == 0)
{
lean_ctor_set(v___x_4162_, 0, v___x_4167_);
v___x_4169_ = v___x_4162_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v___x_4167_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
else
{
lean_object* v_a_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4179_; 
lean_dec_ref(v___y_4155_);
lean_dec(v_discr_4151_);
lean_dec(v_typeName_4149_);
v_a_4172_ = lean_ctor_get(v___x_4159_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4174_ = v___x_4159_;
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_a_4172_);
lean_dec(v___x_4159_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4177_; 
if (v_isShared_4175_ == 0)
{
v___x_4177_ = v___x_4174_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_a_4172_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
}
v___jp_4180_:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
v___x_4183_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4183_, 0, v_typeName_4149_);
lean_ctor_set(v___x_4183_, 1, v___y_4182_);
lean_ctor_set(v___x_4183_, 2, v_discr_4151_);
lean_ctor_set(v___x_4183_, 3, v___y_4181_);
v___x_4184_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4183_);
v___x_4185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
return v___x_4185_;
}
v___jp_4186_:
{
if (v___y_4189_ == 0)
{
lean_inc(v_discr_4151_);
lean_inc(v_typeName_4149_);
lean_dec_ref_known(v_code_3921_, 1);
v___y_4181_ = v___y_4187_;
v___y_4182_ = v___y_4188_;
goto v___jp_4180_;
}
else
{
uint8_t v___x_4190_; 
v___x_4190_ = l_Lean_instBEqFVarId_beq(v_discr_4151_, v_discr_4151_);
if (v___x_4190_ == 0)
{
lean_inc(v_discr_4151_);
lean_inc(v_typeName_4149_);
lean_dec_ref_known(v_code_3921_, 1);
v___y_4181_ = v___y_4187_;
v___y_4182_ = v___y_4188_;
goto v___jp_4180_;
}
else
{
lean_object* v___x_4191_; 
lean_dec_ref(v___y_4188_);
lean_dec_ref(v___y_4187_);
v___x_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4191_, 0, v_code_3921_);
return v___x_4191_;
}
}
}
v___jp_4192_:
{
lean_object* v___x_4193_; uint8_t v___x_4194_; 
v___x_4193_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0));
v___x_4194_ = lean_name_eq(v_typeName_4149_, v___x_4193_);
if (v___x_4194_ == 0)
{
lean_object* v___x_4195_; uint8_t v___x_4196_; 
v___x_4195_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3));
v___x_4196_ = lean_name_eq(v_typeName_4149_, v___x_4195_);
if (v___x_4196_ == 0)
{
lean_object* v___x_4197_; uint8_t v___x_4198_; 
v___x_4197_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__8));
v___x_4198_ = lean_name_eq(v_typeName_4149_, v___x_4197_);
if (v___x_4198_ == 0)
{
lean_object* v___x_4199_; uint8_t v___x_4200_; 
v___x_4199_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__10));
v___x_4200_ = lean_name_eq(v_typeName_4149_, v___x_4199_);
if (v___x_4200_ == 0)
{
lean_object* v___x_4201_; uint8_t v___x_4202_; 
v___x_4201_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__12));
v___x_4202_ = lean_name_eq(v_typeName_4149_, v___x_4201_);
if (v___x_4202_ == 0)
{
lean_object* v___x_4203_; uint8_t v___x_4204_; 
v___x_4203_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__14));
v___x_4204_ = lean_name_eq(v_typeName_4149_, v___x_4203_);
if (v___x_4204_ == 0)
{
lean_object* v___x_4205_; uint8_t v___x_4206_; 
v___x_4205_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__16));
v___x_4206_ = lean_name_eq(v_typeName_4149_, v___x_4205_);
if (v___x_4206_ == 0)
{
lean_object* v___x_4207_; uint8_t v___x_4208_; 
v___x_4207_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__17));
v___x_4208_ = lean_name_eq(v_typeName_4149_, v___x_4207_);
if (v___x_4208_ == 0)
{
lean_object* v___x_4209_; uint8_t v___x_4210_; 
v___x_4209_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__18));
v___x_4210_ = lean_name_eq(v_typeName_4149_, v___x_4209_);
if (v___x_4210_ == 0)
{
lean_object* v___x_4211_; uint8_t v___x_4212_; 
v___x_4211_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__19));
v___x_4212_ = lean_name_eq(v_typeName_4149_, v___x_4211_);
if (v___x_4212_ == 0)
{
lean_object* v___x_4213_; uint8_t v___x_4214_; 
v___x_4213_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__20));
v___x_4214_ = lean_name_eq(v_typeName_4149_, v___x_4213_);
if (v___x_4214_ == 0)
{
lean_object* v___x_4215_; uint8_t v___x_4216_; 
v___x_4215_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__21));
v___x_4216_ = lean_name_eq(v_typeName_4149_, v___x_4215_);
if (v___x_4216_ == 0)
{
lean_object* v___x_4217_; uint8_t v___x_4218_; 
v___x_4217_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__22));
v___x_4218_ = lean_name_eq(v_typeName_4149_, v___x_4217_);
if (v___x_4218_ == 0)
{
lean_object* v___x_4219_; uint8_t v___x_4220_; 
v___x_4219_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__23));
v___x_4220_ = lean_name_eq(v_typeName_4149_, v___x_4219_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4221_; uint8_t v___x_4222_; 
v___x_4221_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__24));
v___x_4222_ = lean_name_eq(v_typeName_4149_, v___x_4221_);
if (v___x_4222_ == 0)
{
lean_object* v___x_4223_; 
lean_inc(v_typeName_4149_);
v___x_4223_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_typeName_4149_, v_a_3925_, v_a_3926_);
if (lean_obj_tag(v___x_4223_) == 0)
{
lean_object* v_a_4224_; 
v_a_4224_ = lean_ctor_get(v___x_4223_, 0);
lean_inc(v_a_4224_);
lean_dec_ref_known(v___x_4223_, 1);
if (lean_obj_tag(v_a_4224_) == 1)
{
lean_object* v_val_4225_; lean_object* v___x_4226_; 
lean_inc_ref(v_cases_4147_);
lean_dec_ref_known(v_code_3921_, 1);
v_val_4225_ = lean_ctor_get(v_a_4224_, 0);
lean_inc(v_val_4225_);
lean_dec_ref_known(v_a_4224_, 1);
v___x_4226_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_val_4225_, v_cases_4147_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
lean_dec(v_val_4225_);
return v___x_4226_;
}
else
{
lean_object* v___x_4227_; 
lean_dec(v_a_4224_);
lean_inc_ref(v_resultType_4150_);
v___x_4227_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_4150_, v_a_3925_, v_a_3926_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_a_4228_; lean_object* v___x_4229_; lean_object* v_env_4230_; lean_object* v___x_4231_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4228_);
lean_dec_ref_known(v___x_4227_, 1);
v___x_4229_ = lean_st_ref_get(v_a_3926_);
v_env_4230_ = lean_ctor_get(v___x_4229_, 0);
lean_inc_ref_n(v_env_4230_, 2);
lean_dec(v___x_4229_);
lean_inc(v_typeName_4149_);
v___x_4231_ = l_Lean_Environment_find_x3f(v_env_4230_, v_typeName_4149_, v___x_4222_);
if (lean_obj_tag(v___x_4231_) == 1)
{
lean_object* v_val_4232_; 
v_val_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_val_4232_);
lean_dec_ref_known(v___x_4231_, 1);
if (lean_obj_tag(v_val_4232_) == 5)
{
lean_object* v_val_4233_; lean_object* v_toConstantVal_4234_; lean_object* v_name_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; 
v_val_4233_ = lean_ctor_get(v_val_4232_, 0);
lean_inc_ref(v_val_4233_);
lean_dec_ref_known(v_val_4232_, 1);
v_toConstantVal_4234_ = lean_ctor_get(v_val_4233_, 0);
lean_inc_ref(v_toConstantVal_4234_);
lean_dec_ref(v_val_4233_);
v_name_4235_ = lean_ctor_get(v_toConstantVal_4234_, 0);
lean_inc(v_name_4235_);
lean_dec_ref(v_toConstantVal_4234_);
v___x_4236_ = l_Lean_mkCasesOnName(v_name_4235_);
lean_inc_ref(v_env_4230_);
v___x_4237_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_4230_, v___x_4236_);
if (lean_obj_tag(v___x_4237_) == 0)
{
if (v___x_4222_ == 0)
{
size_t v_sz_4238_; size_t v___x_4239_; lean_object* v___x_4240_; 
lean_dec_ref(v_env_4230_);
v_sz_4238_ = lean_array_size(v_alts_4152_);
v___x_4239_ = ((size_t)0ULL);
lean_inc_ref(v_alts_4152_);
v___x_4240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v_sz_4238_, v___x_4239_, v_alts_4152_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v_a_4241_; size_t v___x_4242_; size_t v___x_4243_; uint8_t v___x_4244_; 
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
lean_inc(v_a_4241_);
lean_dec_ref_known(v___x_4240_, 1);
v___x_4242_ = lean_ptr_addr(v_alts_4152_);
v___x_4243_ = lean_ptr_addr(v_a_4241_);
v___x_4244_ = lean_usize_dec_eq(v___x_4242_, v___x_4243_);
if (v___x_4244_ == 0)
{
v___y_4187_ = v_a_4241_;
v___y_4188_ = v_a_4228_;
v___y_4189_ = v___x_4244_;
goto v___jp_4186_;
}
else
{
size_t v___x_4245_; size_t v___x_4246_; uint8_t v___x_4247_; 
v___x_4245_ = lean_ptr_addr(v_resultType_4150_);
v___x_4246_ = lean_ptr_addr(v_a_4228_);
v___x_4247_ = lean_usize_dec_eq(v___x_4245_, v___x_4246_);
v___y_4187_ = v_a_4241_;
v___y_4188_ = v_a_4228_;
v___y_4189_ = v___x_4247_;
goto v___jp_4186_;
}
}
else
{
lean_object* v_a_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4255_; 
lean_dec(v_a_4228_);
lean_dec_ref_known(v_code_3921_, 1);
v_a_4248_ = lean_ctor_get(v___x_4240_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4250_ = v___x_4240_;
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_a_4248_);
lean_dec(v___x_4240_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4253_; 
if (v_isShared_4251_ == 0)
{
v___x_4253_ = v___x_4250_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_a_4248_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
}
else
{
lean_inc_ref(v_alts_4152_);
lean_inc(v_discr_4151_);
lean_inc(v_typeName_4149_);
lean_dec_ref_known(v_code_3921_, 1);
v___y_4154_ = v___x_4222_;
v___y_4155_ = v_a_4228_;
v___y_4156_ = v_env_4230_;
goto v___jp_4153_;
}
}
else
{
lean_inc_ref(v_alts_4152_);
lean_inc(v_discr_4151_);
lean_inc(v_typeName_4149_);
lean_dec_ref_known(v___x_4237_, 1);
lean_dec_ref_known(v_code_3921_, 1);
v___y_4154_ = v___x_4222_;
v___y_4155_ = v_a_4228_;
v___y_4156_ = v_env_4230_;
goto v___jp_4153_;
}
}
else
{
lean_dec(v_val_4232_);
lean_dec_ref(v_env_4230_);
lean_dec(v_a_4228_);
lean_dec_ref_known(v_code_3921_, 1);
v___y_3997_ = v_a_3922_;
v___y_3998_ = v_a_3923_;
v___y_3999_ = v_a_3924_;
v___y_4000_ = v_a_3925_;
v___y_4001_ = v_a_3926_;
goto v___jp_3996_;
}
}
else
{
lean_dec(v___x_4231_);
lean_dec_ref(v_env_4230_);
lean_dec(v_a_4228_);
lean_dec_ref_known(v_code_3921_, 1);
v___y_3997_ = v_a_3922_;
v___y_3998_ = v_a_3923_;
v___y_3999_ = v_a_3924_;
v___y_4000_ = v_a_3925_;
v___y_4001_ = v_a_3926_;
goto v___jp_3996_;
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
lean_dec_ref_known(v_code_3921_, 1);
v_a_4256_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4227_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4227_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
}
else
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4271_; 
lean_dec_ref_known(v_code_3921_, 1);
v_a_4264_ = lean_ctor_get(v___x_4223_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4223_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4266_ = v___x_4223_;
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4223_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
if (v_isShared_4267_ == 0)
{
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4264_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
}
else
{
lean_object* v___x_4272_; 
lean_inc_ref(v_cases_4147_);
lean_dec_ref_known(v_code_3921_, 1);
v___x_4272_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_cases_4147_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_4272_;
}
}
else
{
lean_object* v___x_4273_; 
lean_inc_ref(v_cases_4147_);
lean_dec_ref_known(v_code_3921_, 1);
v___x_4273_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_cases_4147_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
lean_dec_ref(v_cases_4147_);
return v___x_4273_;
}
}
else
{
lean_object* v___x_4274_; 
lean_inc_ref(v_cases_4147_);
lean_dec_ref_known(v_code_3921_, 1);
v___x_4274_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_cases_4147_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_4274_;
}
}
else
{
lean_object* v___x_4275_; 
lean_inc_ref(v_cases_4147_);
lean_dec_ref_known(v_code_3921_, 1);
v___x_4275_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_cases_4147_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_4275_;
}
}
else
{
lean_object* v___x_4276_; 
lean_inc_ref(v_cases_4147_);
lean_dec_ref_known(v_code_3921_, 1);
v___x_4276_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_cases_4147_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_4276_;
}
}
else
{
lean_object* v___x_4277_; 
lean_inc_ref(v_cases_4147_);
lean_dec_ref_known(v_code_3921_, 1);
v___x_4277_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_cases_4147_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_4277_;
}
}
else
{
lean_object* v___x_4278_; 
lean_inc_ref(v_cases_4147_);
lean_dec_ref_known(v_code_3921_, 1);
v___x_4278_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_cases_4147_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_4278_;
}
}
else
{
lean_object* v___x_4279_; 
lean_inc_ref(v_cases_4147_);
lean_dec_ref_known(v_code_3921_, 1);
v___x_4279_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_cases_4147_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_4279_;
}
}
else
{
lean_object* v___x_4280_; 
lean_inc_ref(v_cases_4147_);
lean_dec_ref_known(v_code_3921_, 1);
v___x_4280_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_4147_, v___x_4205_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_4280_;
}
}
else
{
lean_object* v___x_4281_; 
lean_inc_ref(v_cases_4147_);
lean_dec_ref_known(v_code_3921_, 1);
v___x_4281_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_4147_, v___x_4203_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_4281_;
}
}
else
{
lean_object* v___x_4282_; 
lean_inc_ref(v_cases_4147_);
lean_dec_ref_known(v_code_3921_, 1);
v___x_4282_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_4147_, v___x_4201_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_4282_;
}
}
else
{
lean_object* v___x_4283_; 
lean_inc_ref(v_cases_4147_);
lean_dec_ref_known(v_code_3921_, 1);
v___x_4283_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_4147_, v___x_4199_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_4283_;
}
}
else
{
lean_object* v___x_4284_; 
lean_inc_ref(v_cases_4147_);
lean_dec_ref_known(v_code_3921_, 1);
v___x_4284_ = l_Lean_Compiler_LCNF_casesNOptionToMono___redArg(v_cases_4147_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_4284_;
}
}
else
{
lean_object* v___x_4285_; 
lean_inc_ref(v_cases_4147_);
lean_dec_ref_known(v_code_3921_, 1);
v___x_4285_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_cases_4147_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_4285_;
}
}
else
{
lean_object* v___x_4286_; 
lean_inc_ref(v_cases_4147_);
lean_dec_ref_known(v_code_3921_, 1);
v___x_4286_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_cases_4147_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_4286_;
}
}
}
case 5:
{
lean_object* v___x_4293_; 
v___x_4293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4293_, 0, v_code_3921_);
return v___x_4293_;
}
case 6:
{
lean_object* v_type_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4318_; 
v_type_4294_ = lean_ctor_get(v_code_3921_, 0);
v_isSharedCheck_4318_ = !lean_is_exclusive(v_code_3921_);
if (v_isSharedCheck_4318_ == 0)
{
v___x_4296_ = v_code_3921_;
v_isShared_4297_ = v_isSharedCheck_4318_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_type_4294_);
lean_dec(v_code_3921_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4318_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4298_; 
v___x_4298_ = l_Lean_Compiler_LCNF_toMonoType(v_type_4294_, v_a_3925_, v_a_3926_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4309_; 
v_a_4299_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4301_ = v___x_4298_;
v_isShared_4302_ = v_isSharedCheck_4309_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4298_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4309_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
if (v_isShared_4297_ == 0)
{
lean_ctor_set(v___x_4296_, 0, v_a_4299_);
v___x_4304_ = v___x_4296_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4299_);
v___x_4304_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
lean_object* v___x_4306_; 
if (v_isShared_4302_ == 0)
{
lean_ctor_set(v___x_4301_, 0, v___x_4304_);
v___x_4306_ = v___x_4301_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v___x_4304_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
lean_del_object(v___x_4296_);
v_a_4310_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4312_ = v___x_4298_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4298_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4310_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
}
}
}
default: 
{
lean_object* v_decl_4319_; lean_object* v_k_4320_; 
v_decl_4319_ = lean_ctor_get(v_code_3921_, 0);
v_k_4320_ = lean_ctor_get(v_code_3921_, 1);
lean_inc_ref(v_k_4320_);
lean_inc_ref(v_decl_4319_);
v_decl_3943_ = v_decl_4319_;
v_k_3944_ = v_k_4320_;
v___y_3945_ = v_a_3922_;
v___y_3946_ = v_a_3923_;
v___y_3947_ = v_a_3924_;
v___y_3948_ = v_a_3925_;
v___y_3949_ = v_a_3926_;
goto v___jp_3942_;
}
}
v___jp_3928_:
{
if (v___y_3931_ == 0)
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
lean_dec_ref(v_code_3921_);
v___x_3932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3932_, 0, v___y_3930_);
lean_ctor_set(v___x_3932_, 1, v___y_3929_);
v___x_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3932_);
return v___x_3933_;
}
else
{
lean_object* v___x_3934_; 
lean_dec_ref(v___y_3930_);
lean_dec_ref(v___y_3929_);
v___x_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3934_, 0, v_code_3921_);
return v___x_3934_;
}
}
v___jp_3935_:
{
if (v___y_3938_ == 0)
{
lean_object* v___x_3939_; lean_object* v___x_3940_; 
lean_dec_ref(v_code_3921_);
v___x_3939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3939_, 0, v___y_3937_);
lean_ctor_set(v___x_3939_, 1, v___y_3936_);
v___x_3940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3939_);
return v___x_3940_;
}
else
{
lean_object* v___x_3941_; 
lean_dec_ref(v___y_3937_);
lean_dec_ref(v___y_3936_);
v___x_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3941_, 0, v_code_3921_);
return v___x_3941_;
}
}
v___jp_3942_:
{
lean_object* v___x_3950_; 
v___x_3950_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_3943_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v_a_3951_; lean_object* v___x_3952_; 
v_a_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_a_3951_);
lean_dec_ref_known(v___x_3950_, 1);
v___x_3952_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
if (lean_obj_tag(v___x_3952_) == 0)
{
switch(lean_obj_tag(v_code_3921_))
{
case 1:
{
lean_object* v_a_3953_; lean_object* v_decl_3954_; lean_object* v_k_3955_; size_t v___x_3956_; size_t v___x_3957_; uint8_t v___x_3958_; 
v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
lean_inc(v_a_3953_);
lean_dec_ref_known(v___x_3952_, 1);
v_decl_3954_ = lean_ctor_get(v_code_3921_, 0);
v_k_3955_ = lean_ctor_get(v_code_3921_, 1);
v___x_3956_ = lean_ptr_addr(v_k_3955_);
v___x_3957_ = lean_ptr_addr(v_a_3953_);
v___x_3958_ = lean_usize_dec_eq(v___x_3956_, v___x_3957_);
if (v___x_3958_ == 0)
{
v___y_3929_ = v_a_3953_;
v___y_3930_ = v_a_3951_;
v___y_3931_ = v___x_3958_;
goto v___jp_3928_;
}
else
{
size_t v___x_3959_; size_t v___x_3960_; uint8_t v___x_3961_; 
v___x_3959_ = lean_ptr_addr(v_decl_3954_);
v___x_3960_ = lean_ptr_addr(v_a_3951_);
v___x_3961_ = lean_usize_dec_eq(v___x_3959_, v___x_3960_);
v___y_3929_ = v_a_3953_;
v___y_3930_ = v_a_3951_;
v___y_3931_ = v___x_3961_;
goto v___jp_3928_;
}
}
case 2:
{
lean_object* v_a_3962_; lean_object* v_decl_3963_; lean_object* v_k_3964_; size_t v___x_3965_; size_t v___x_3966_; uint8_t v___x_3967_; 
v_a_3962_ = lean_ctor_get(v___x_3952_, 0);
lean_inc(v_a_3962_);
lean_dec_ref_known(v___x_3952_, 1);
v_decl_3963_ = lean_ctor_get(v_code_3921_, 0);
v_k_3964_ = lean_ctor_get(v_code_3921_, 1);
v___x_3965_ = lean_ptr_addr(v_k_3964_);
v___x_3966_ = lean_ptr_addr(v_a_3962_);
v___x_3967_ = lean_usize_dec_eq(v___x_3965_, v___x_3966_);
if (v___x_3967_ == 0)
{
v___y_3936_ = v_a_3962_;
v___y_3937_ = v_a_3951_;
v___y_3938_ = v___x_3967_;
goto v___jp_3935_;
}
else
{
size_t v___x_3968_; size_t v___x_3969_; uint8_t v___x_3970_; 
v___x_3968_ = lean_ptr_addr(v_decl_3963_);
v___x_3969_ = lean_ptr_addr(v_a_3951_);
v___x_3970_ = lean_usize_dec_eq(v___x_3968_, v___x_3969_);
v___y_3936_ = v_a_3962_;
v___y_3937_ = v_a_3951_;
v___y_3938_ = v___x_3970_;
goto v___jp_3935_;
}
}
default: 
{
lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3979_; 
lean_dec(v_a_3951_);
lean_dec_ref(v_code_3921_);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3979_ == 0)
{
lean_object* v_unused_3980_; 
v_unused_3980_ = lean_ctor_get(v___x_3952_, 0);
lean_dec(v_unused_3980_);
v___x_3972_ = v___x_3952_;
v_isShared_3973_ = v_isSharedCheck_3979_;
goto v_resetjp_3971_;
}
else
{
lean_dec(v___x_3952_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3979_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3977_; 
v___x_3974_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__2, &l_Lean_Compiler_LCNF_Code_toMono___closed__2_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__2);
v___x_3975_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__2(v___x_3974_);
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 0, v___x_3975_);
v___x_3977_ = v___x_3972_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v___x_3975_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
}
else
{
lean_dec(v_a_3951_);
lean_dec_ref(v_code_3921_);
return v___x_3952_;
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
lean_dec_ref(v_k_3944_);
lean_dec_ref(v_code_3921_);
v_a_3981_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3950_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3950_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
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
v___jp_3989_:
{
if (v___y_3992_ == 0)
{
lean_object* v___x_3993_; lean_object* v___x_3994_; 
lean_dec_ref(v_code_3921_);
v___x_3993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3993_, 0, v___y_3991_);
lean_ctor_set(v___x_3993_, 1, v___y_3990_);
v___x_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3993_);
return v___x_3994_;
}
else
{
lean_object* v___x_3995_; 
lean_dec_ref(v___y_3991_);
lean_dec_ref(v___y_3990_);
v___x_3995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3995_, 0, v_code_3921_);
return v___x_3995_;
}
}
v___jp_3996_:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4002_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__4, &l_Lean_Compiler_LCNF_Code_toMono___closed__4_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__4);
v___x_4003_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_4002_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_);
return v___x_4003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24(size_t v_sz_4321_, size_t v_i_4322_, lean_object* v_bs_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
uint8_t v___x_4330_; 
v___x_4330_ = lean_usize_dec_lt(v_i_4322_, v_sz_4321_);
if (v___x_4330_ == 0)
{
lean_object* v___x_4331_; 
v___x_4331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4331_, 0, v_bs_4323_);
return v___x_4331_;
}
else
{
lean_object* v_v_4332_; lean_object* v___x_4333_; lean_object* v_bs_x27_4334_; lean_object* v_a_4336_; 
v_v_4332_ = lean_array_uget(v_bs_4323_, v_i_4322_);
v___x_4333_ = lean_unsigned_to_nat(0u);
v_bs_x27_4334_ = lean_array_uset(v_bs_4323_, v_i_4322_, v___x_4333_);
if (lean_obj_tag(v_v_4332_) == 0)
{
lean_object* v_ctorName_4341_; lean_object* v_params_4342_; lean_object* v_code_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4377_; 
v_ctorName_4341_ = lean_ctor_get(v_v_4332_, 0);
v_params_4342_ = lean_ctor_get(v_v_4332_, 1);
v_code_4343_ = lean_ctor_get(v_v_4332_, 2);
v_isSharedCheck_4377_ = !lean_is_exclusive(v_v_4332_);
if (v_isSharedCheck_4377_ == 0)
{
v___x_4345_ = v_v_4332_;
v_isShared_4346_ = v_isSharedCheck_4377_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_code_4343_);
lean_inc(v_params_4342_);
lean_inc(v_ctorName_4341_);
lean_dec(v_v_4332_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4377_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
uint8_t v___x_4347_; lean_object* v___x_4348_; 
v___x_4347_ = 0;
v___x_4348_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_4347_, v_params_4342_, v___y_4326_);
lean_dec_ref(v_params_4342_);
if (lean_obj_tag(v___x_4348_) == 0)
{
lean_object* v___y_4350_; lean_object* v___x_4365_; uint8_t v___x_4366_; 
lean_dec_ref_known(v___x_4348_, 1);
v___x_4365_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__4));
v___x_4366_ = lean_name_eq(v_ctorName_4341_, v___x_4365_);
lean_dec(v_ctorName_4341_);
if (v___x_4366_ == 0)
{
lean_object* v___x_4367_; 
v___x_4367_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__36));
v___y_4350_ = v___x_4367_;
goto v___jp_4349_;
}
else
{
lean_object* v___x_4368_; 
v___x_4368_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__39));
v___y_4350_ = v___x_4368_;
goto v___jp_4349_;
}
v___jp_4349_:
{
lean_object* v___x_4351_; 
v___x_4351_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_4343_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_object* v_a_4352_; lean_object* v___x_4353_; lean_object* v___x_4355_; 
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
lean_inc(v_a_4352_);
lean_dec_ref_known(v___x_4351_, 1);
v___x_4353_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24___closed__0));
lean_inc(v___y_4350_);
if (v_isShared_4346_ == 0)
{
lean_ctor_set(v___x_4345_, 2, v_a_4352_);
lean_ctor_set(v___x_4345_, 1, v___x_4353_);
lean_ctor_set(v___x_4345_, 0, v___y_4350_);
v___x_4355_ = v___x_4345_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v___y_4350_);
lean_ctor_set(v_reuseFailAlloc_4356_, 1, v___x_4353_);
lean_ctor_set(v_reuseFailAlloc_4356_, 2, v_a_4352_);
v___x_4355_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
v_a_4336_ = v___x_4355_;
goto v___jp_4335_;
}
}
else
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
lean_del_object(v___x_4345_);
lean_dec_ref(v_bs_x27_4334_);
v_a_4357_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4359_ = v___x_4351_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4351_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
}
}
else
{
lean_object* v_a_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4376_; 
lean_del_object(v___x_4345_);
lean_dec_ref(v_code_4343_);
lean_dec(v_ctorName_4341_);
lean_dec_ref(v_bs_x27_4334_);
v_a_4369_ = lean_ctor_get(v___x_4348_, 0);
v_isSharedCheck_4376_ = !lean_is_exclusive(v___x_4348_);
if (v_isSharedCheck_4376_ == 0)
{
v___x_4371_ = v___x_4348_;
v_isShared_4372_ = v_isSharedCheck_4376_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_a_4369_);
lean_dec(v___x_4348_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4376_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v___x_4374_; 
if (v_isShared_4372_ == 0)
{
v___x_4374_ = v___x_4371_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v_a_4369_);
v___x_4374_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
return v___x_4374_;
}
}
}
}
}
else
{
lean_object* v_code_4378_; lean_object* v___x_4379_; 
v_code_4378_ = lean_ctor_get(v_v_4332_, 0);
lean_inc_ref(v_code_4378_);
v___x_4379_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_4378_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v_a_4380_; lean_object* v___x_4381_; 
v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
lean_inc(v_a_4380_);
lean_dec_ref_known(v___x_4379_, 1);
v___x_4381_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_4332_, v_a_4380_);
v_a_4336_ = v___x_4381_;
goto v___jp_4335_;
}
else
{
lean_object* v_a_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4389_; 
lean_dec_ref_known(v_v_4332_, 1);
lean_dec_ref(v_bs_x27_4334_);
v_a_4382_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4384_ = v___x_4379_;
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_a_4382_);
lean_dec(v___x_4379_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4387_; 
if (v_isShared_4385_ == 0)
{
v___x_4387_ = v___x_4384_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_a_4382_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
return v___x_4387_;
}
}
}
}
v___jp_4335_:
{
size_t v___x_4337_; size_t v___x_4338_; lean_object* v___x_4339_; 
v___x_4337_ = ((size_t)1ULL);
v___x_4338_ = lean_usize_add(v_i_4322_, v___x_4337_);
v___x_4339_ = lean_array_uset(v_bs_x27_4334_, v_i_4322_, v_a_4336_);
v_i_4322_ = v___x_4338_;
v_bs_4323_ = v___x_4339_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___redArg(lean_object* v_c_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_){
_start:
{
lean_object* v_resultType_4397_; lean_object* v_discr_4398_; lean_object* v_alts_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4437_; 
v_resultType_4397_ = lean_ctor_get(v_c_4390_, 1);
v_discr_4398_ = lean_ctor_get(v_c_4390_, 2);
v_alts_4399_ = lean_ctor_get(v_c_4390_, 3);
v_isSharedCheck_4437_ = !lean_is_exclusive(v_c_4390_);
if (v_isSharedCheck_4437_ == 0)
{
lean_object* v_unused_4438_; 
v_unused_4438_ = lean_ctor_get(v_c_4390_, 0);
lean_dec(v_unused_4438_);
v___x_4401_ = v_c_4390_;
v_isShared_4402_ = v_isSharedCheck_4437_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_alts_4399_);
lean_inc(v_discr_4398_);
lean_inc(v_resultType_4397_);
lean_dec(v_c_4390_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4437_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4403_; 
v___x_4403_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_4397_, v_a_4394_, v_a_4395_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v_a_4404_; size_t v_sz_4405_; size_t v___x_4406_; lean_object* v___x_4407_; 
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
lean_inc(v_a_4404_);
lean_dec_ref_known(v___x_4403_, 1);
v_sz_4405_ = lean_array_size(v_alts_4399_);
v___x_4406_ = ((size_t)0ULL);
v___x_4407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24(v_sz_4405_, v___x_4406_, v_alts_4399_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_);
if (lean_obj_tag(v___x_4407_) == 0)
{
lean_object* v_a_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4420_; 
v_a_4408_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4410_ = v___x_4407_;
v_isShared_4411_ = v_isSharedCheck_4420_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4407_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4420_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
lean_object* v___x_4412_; lean_object* v___x_4414_; 
v___x_4412_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
if (v_isShared_4402_ == 0)
{
lean_ctor_set(v___x_4401_, 3, v_a_4408_);
lean_ctor_set(v___x_4401_, 1, v_a_4404_);
lean_ctor_set(v___x_4401_, 0, v___x_4412_);
v___x_4414_ = v___x_4401_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v___x_4412_);
lean_ctor_set(v_reuseFailAlloc_4419_, 1, v_a_4404_);
lean_ctor_set(v_reuseFailAlloc_4419_, 2, v_discr_4398_);
lean_ctor_set(v_reuseFailAlloc_4419_, 3, v_a_4408_);
v___x_4414_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
lean_object* v___x_4415_; lean_object* v___x_4417_; 
v___x_4415_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4415_, 0, v___x_4414_);
if (v_isShared_4411_ == 0)
{
lean_ctor_set(v___x_4410_, 0, v___x_4415_);
v___x_4417_ = v___x_4410_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v___x_4415_);
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
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4428_; 
lean_dec(v_a_4404_);
lean_del_object(v___x_4401_);
lean_dec(v_discr_4398_);
v_a_4421_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4423_ = v___x_4407_;
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4407_);
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
else
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4436_; 
lean_del_object(v___x_4401_);
lean_dec_ref(v_alts_4399_);
lean_dec(v_discr_4398_);
v_a_4429_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4431_ = v___x_4403_;
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4403_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4434_; 
if (v_isShared_4432_ == 0)
{
v___x_4434_ = v___x_4431_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
return v___x_4434_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___redArg___boxed(lean_object* v_c_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_){
_start:
{
lean_object* v_res_4446_; 
v_res_4446_ = l_Lean_Compiler_LCNF_decToMono___redArg(v_c_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_);
lean_dec(v_a_4444_);
lean_dec_ref(v_a_4443_);
lean_dec(v_a_4442_);
lean_dec_ref(v_a_4441_);
lean_dec(v_a_4440_);
return v_res_4446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono___boxed(lean_object* v_decl_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_);
lean_dec(v_a_4452_);
lean_dec_ref(v_a_4451_);
lean_dec(v_a_4450_);
lean_dec_ref(v_a_4449_);
lean_dec(v_a_4448_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___boxed(lean_object* v_sz_4455_, lean_object* v_i_4456_, lean_object* v_bs_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
size_t v_sz_boxed_4464_; size_t v_i_boxed_4465_; lean_object* v_res_4466_; 
v_sz_boxed_4464_ = lean_unbox_usize(v_sz_4455_);
lean_dec(v_sz_4455_);
v_i_boxed_4465_ = lean_unbox_usize(v_i_4456_);
lean_dec(v_i_4456_);
v_res_4466_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v_sz_boxed_4464_, v_i_boxed_4465_, v_bs_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_dec(v___y_4460_);
lean_dec_ref(v___y_4459_);
lean_dec(v___y_4458_);
return v_res_4466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___boxed(lean_object* v_c_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_){
_start:
{
lean_object* v_res_4474_; 
v_res_4474_ = l_Lean_Compiler_LCNF_casesNOptionToMono___redArg(v_c_4467_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_);
lean_dec(v_a_4472_);
lean_dec_ref(v_a_4471_);
lean_dec(v_a_4470_);
lean_dec_ref(v_a_4469_);
lean_dec(v_a_4468_);
return v_res_4474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24___boxed(lean_object* v_sz_4475_, lean_object* v_i_4476_, lean_object* v_bs_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
size_t v_sz_boxed_4484_; size_t v_i_boxed_4485_; lean_object* v_res_4486_; 
v_sz_boxed_4484_ = lean_unbox_usize(v_sz_4475_);
lean_dec(v_sz_4475_);
v_i_boxed_4485_ = lean_unbox_usize(v_i_4476_);
lean_dec(v_i_4476_);
v_res_4486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24(v_sz_boxed_4484_, v_i_boxed_4485_, v_bs_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4478_);
return v_res_4486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___boxed(lean_object* v_c_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_){
_start:
{
lean_object* v_res_4494_; 
v_res_4494_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_4487_, v_a_4488_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_);
lean_dec(v_a_4492_);
lean_dec_ref(v_a_4491_);
lean_dec(v_a_4490_);
lean_dec_ref(v_a_4489_);
lean_dec(v_a_4488_);
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___boxed(lean_object* v_c_4495_, lean_object* v_uintName_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_){
_start:
{
lean_object* v_res_4503_; 
v_res_4503_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_4495_, v_uintName_4496_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_);
lean_dec(v_a_4501_);
lean_dec_ref(v_a_4500_);
lean_dec(v_a_4499_);
lean_dec_ref(v_a_4498_);
lean_dec(v_a_4497_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___boxed(lean_object* v_c_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_){
_start:
{
lean_object* v_res_4511_; 
v_res_4511_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_);
lean_dec(v_a_4509_);
lean_dec_ref(v_a_4508_);
lean_dec(v_a_4507_);
lean_dec_ref(v_a_4506_);
lean_dec(v_a_4505_);
return v_res_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___boxed(lean_object* v_c_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_){
_start:
{
lean_object* v_res_4519_; 
v_res_4519_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_c_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_);
lean_dec(v_a_4517_);
lean_dec_ref(v_a_4516_);
lean_dec(v_a_4515_);
lean_dec_ref(v_a_4514_);
lean_dec(v_a_4513_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___boxed(lean_object* v_c_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_){
_start:
{
lean_object* v_res_4527_; 
v_res_4527_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_4520_, v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_);
lean_dec(v_a_4525_);
lean_dec_ref(v_a_4524_);
lean_dec(v_a_4523_);
lean_dec_ref(v_a_4522_);
lean_dec(v_a_4521_);
return v_res_4527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg___boxed(lean_object* v_c_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_){
_start:
{
lean_object* v_res_4535_; 
v_res_4535_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_c_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_);
lean_dec(v_a_4533_);
lean_dec_ref(v_a_4532_);
lean_dec(v_a_4531_);
lean_dec_ref(v_a_4530_);
lean_dec(v_a_4529_);
return v_res_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___boxed(lean_object* v_c_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_){
_start:
{
lean_object* v_res_4543_; 
v_res_4543_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_);
lean_dec(v_a_4541_);
lean_dec_ref(v_a_4540_);
lean_dec(v_a_4539_);
lean_dec_ref(v_a_4538_);
lean_dec(v_a_4537_);
return v_res_4543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___boxed(lean_object* v___x_4544_, lean_object* v___x_4545_, lean_object* v_sz_4546_, lean_object* v_i_4547_, lean_object* v_bs_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_){
_start:
{
uint8_t v___x_52726__boxed_4555_; size_t v_sz_boxed_4556_; size_t v_i_boxed_4557_; lean_object* v_res_4558_; 
v___x_52726__boxed_4555_ = lean_unbox(v___x_4545_);
v_sz_boxed_4556_ = lean_unbox_usize(v_sz_4546_);
lean_dec(v_sz_4546_);
v_i_boxed_4557_ = lean_unbox_usize(v_i_4547_);
lean_dec(v_i_4547_);
v_res_4558_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(v___x_4544_, v___x_52726__boxed_4555_, v_sz_boxed_4556_, v_i_boxed_4557_, v_bs_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_);
lean_dec(v___y_4553_);
lean_dec_ref(v___y_4552_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
return v_res_4558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___boxed(lean_object* v_c_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_);
lean_dec(v_a_4564_);
lean_dec_ref(v_a_4563_);
lean_dec(v_a_4562_);
lean_dec_ref(v_a_4561_);
lean_dec(v_a_4560_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___boxed(lean_object* v_c_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_, v_a_4572_);
lean_dec(v_a_4572_);
lean_dec_ref(v_a_4571_);
lean_dec(v_a_4570_);
lean_dec_ref(v_a_4569_);
lean_dec(v_a_4568_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___boxed(lean_object* v_c_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_){
_start:
{
lean_object* v_res_4582_; 
v_res_4582_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_);
lean_dec(v_a_4580_);
lean_dec_ref(v_a_4579_);
lean_dec(v_a_4578_);
lean_dec_ref(v_a_4577_);
lean_dec(v_a_4576_);
return v_res_4582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18___boxed(lean_object* v___x_4583_, lean_object* v_sz_4584_, lean_object* v_i_4585_, lean_object* v_bs_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_){
_start:
{
size_t v_sz_boxed_4593_; size_t v_i_boxed_4594_; lean_object* v_res_4595_; 
v_sz_boxed_4593_ = lean_unbox_usize(v_sz_4584_);
lean_dec(v_sz_4584_);
v_i_boxed_4594_ = lean_unbox_usize(v_i_4585_);
lean_dec(v_i_4585_);
v_res_4595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18(v___x_4583_, v_sz_boxed_4593_, v_i_boxed_4594_, v_bs_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_);
lean_dec(v___y_4591_);
lean_dec_ref(v___y_4590_);
lean_dec(v___y_4589_);
lean_dec_ref(v___y_4588_);
lean_dec(v___y_4587_);
return v_res_4595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___boxed(lean_object* v_info_4596_, lean_object* v_c_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_){
_start:
{
lean_object* v_res_4604_; 
v_res_4604_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_info_4596_, v_c_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_);
lean_dec(v_a_4602_);
lean_dec_ref(v_a_4601_);
lean_dec(v_a_4600_);
lean_dec_ref(v_a_4599_);
lean_dec(v_a_4598_);
lean_dec_ref(v_info_4596_);
return v_res_4604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___boxed(lean_object* v___x_4605_, lean_object* v_sz_4606_, lean_object* v_i_4607_, lean_object* v_bs_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_){
_start:
{
size_t v_sz_boxed_4615_; size_t v_i_boxed_4616_; lean_object* v_res_4617_; 
v_sz_boxed_4615_ = lean_unbox_usize(v_sz_4606_);
lean_dec(v_sz_4606_);
v_i_boxed_4616_ = lean_unbox_usize(v_i_4607_);
lean_dec(v_i_4607_);
v_res_4617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22(v___x_4605_, v_sz_boxed_4615_, v_i_boxed_4616_, v_bs_4608_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_);
lean_dec(v___y_4613_);
lean_dec_ref(v___y_4612_);
lean_dec(v___y_4611_);
lean_dec_ref(v___y_4610_);
lean_dec(v___y_4609_);
return v_res_4617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___boxed(lean_object* v_c_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_){
_start:
{
lean_object* v_res_4625_; 
v_res_4625_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_4618_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_);
lean_dec(v_a_4623_);
lean_dec_ref(v_a_4622_);
lean_dec(v_a_4621_);
lean_dec_ref(v_a_4620_);
lean_dec(v_a_4619_);
lean_dec_ref(v_c_4618_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___boxed(lean_object* v___x_4626_, lean_object* v_sz_4627_, lean_object* v_i_4628_, lean_object* v_bs_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_){
_start:
{
size_t v_sz_boxed_4636_; size_t v_i_boxed_4637_; lean_object* v_res_4638_; 
v_sz_boxed_4636_ = lean_unbox_usize(v_sz_4627_);
lean_dec(v_sz_4627_);
v_i_boxed_4637_ = lean_unbox_usize(v_i_4628_);
lean_dec(v_i_4628_);
v_res_4638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20(v___x_4626_, v_sz_boxed_4636_, v_i_boxed_4637_, v_bs_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec(v___y_4630_);
return v_res_4638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono___boxed(lean_object* v_code_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_){
_start:
{
lean_object* v_res_4646_; 
v_res_4646_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_);
lean_dec(v_a_4644_);
lean_dec_ref(v_a_4643_);
lean_dec(v_a_4642_);
lean_dec_ref(v_a_4641_);
lean_dec(v_a_4640_);
return v_res_4646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono(lean_object* v_c_4647_, lean_object* v_x_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_){
_start:
{
lean_object* v___x_4655_; 
v___x_4655_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_4647_, v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_);
return v___x_4655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___boxed(lean_object* v_c_4656_, lean_object* v_x_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l_Lean_Compiler_LCNF_casesTaskToMono(v_c_4656_, v_x_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_);
lean_dec(v_a_4662_);
lean_dec_ref(v_a_4661_);
lean_dec(v_a_4660_);
lean_dec_ref(v_a_4659_);
lean_dec(v_a_4658_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono(lean_object* v_c_4665_, lean_object* v_x_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_){
_start:
{
lean_object* v___x_4673_; 
v___x_4673_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_4665_, v_a_4667_, v_a_4668_, v_a_4669_, v_a_4670_, v_a_4671_);
return v___x_4673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___boxed(lean_object* v_c_4674_, lean_object* v_x_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_){
_start:
{
lean_object* v_res_4682_; 
v_res_4682_ = l_Lean_Compiler_LCNF_casesThunkToMono(v_c_4674_, v_x_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_);
lean_dec(v_a_4680_);
lean_dec_ref(v_a_4679_);
lean_dec(v_a_4678_);
lean_dec_ref(v_a_4677_);
lean_dec(v_a_4676_);
lean_dec_ref(v_c_4674_);
return v_res_4682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono(lean_object* v_c_4683_, lean_object* v_x_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_){
_start:
{
lean_object* v___x_4691_; 
v___x_4691_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_c_4683_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
return v___x_4691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___boxed(lean_object* v_c_4692_, lean_object* v_x_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_){
_start:
{
lean_object* v_res_4700_; 
v_res_4700_ = l_Lean_Compiler_LCNF_casesFloat32ToMono(v_c_4692_, v_x_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_);
lean_dec(v_a_4698_);
lean_dec_ref(v_a_4697_);
lean_dec(v_a_4696_);
lean_dec_ref(v_a_4695_);
lean_dec(v_a_4694_);
return v_res_4700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono(lean_object* v_c_4701_, lean_object* v_x_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_){
_start:
{
lean_object* v___x_4709_; 
v___x_4709_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_c_4701_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_);
return v___x_4709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___boxed(lean_object* v_c_4710_, lean_object* v_x_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_){
_start:
{
lean_object* v_res_4718_; 
v_res_4718_ = l_Lean_Compiler_LCNF_casesFloatToMono(v_c_4710_, v_x_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_);
lean_dec(v_a_4716_);
lean_dec_ref(v_a_4715_);
lean_dec(v_a_4714_);
lean_dec_ref(v_a_4713_);
lean_dec(v_a_4712_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono(lean_object* v_c_4719_, lean_object* v_x_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_){
_start:
{
lean_object* v___x_4727_; 
v___x_4727_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_4719_, v_a_4721_, v_a_4722_, v_a_4723_, v_a_4724_, v_a_4725_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___boxed(lean_object* v_c_4728_, lean_object* v_x_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_){
_start:
{
lean_object* v_res_4736_; 
v_res_4736_ = l_Lean_Compiler_LCNF_casesStringToMono(v_c_4728_, v_x_4729_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_);
lean_dec(v_a_4734_);
lean_dec_ref(v_a_4733_);
lean_dec(v_a_4732_);
lean_dec_ref(v_a_4731_);
lean_dec(v_a_4730_);
return v_res_4736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono(lean_object* v_c_4737_, lean_object* v_x_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_){
_start:
{
lean_object* v___x_4745_; 
v___x_4745_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_4737_, v_a_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_);
return v___x_4745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___boxed(lean_object* v_c_4746_, lean_object* v_x_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_){
_start:
{
lean_object* v_res_4754_; 
v_res_4754_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono(v_c_4746_, v_x_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
lean_dec(v_a_4752_);
lean_dec_ref(v_a_4751_);
lean_dec(v_a_4750_);
lean_dec_ref(v_a_4749_);
lean_dec(v_a_4748_);
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono(lean_object* v_c_4755_, lean_object* v_x_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_){
_start:
{
lean_object* v___x_4763_; 
v___x_4763_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_4755_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
return v___x_4763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___boxed(lean_object* v_c_4764_, lean_object* v_x_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_){
_start:
{
lean_object* v_res_4772_; 
v_res_4772_ = l_Lean_Compiler_LCNF_casesByteArrayToMono(v_c_4764_, v_x_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_);
lean_dec(v_a_4770_);
lean_dec_ref(v_a_4769_);
lean_dec(v_a_4768_);
lean_dec_ref(v_a_4767_);
lean_dec(v_a_4766_);
return v_res_4772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono(lean_object* v_c_4773_, lean_object* v_x_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_){
_start:
{
lean_object* v___x_4781_; 
v___x_4781_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_4773_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_);
return v___x_4781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___boxed(lean_object* v_c_4782_, lean_object* v_x_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_){
_start:
{
lean_object* v_res_4790_; 
v_res_4790_ = l_Lean_Compiler_LCNF_casesArrayToMono(v_c_4782_, v_x_4783_, v_a_4784_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_);
lean_dec(v_a_4788_);
lean_dec_ref(v_a_4787_);
lean_dec(v_a_4786_);
lean_dec_ref(v_a_4785_);
lean_dec(v_a_4784_);
return v_res_4790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono(lean_object* v_c_4791_, lean_object* v_uintName_4792_, lean_object* v_x_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_){
_start:
{
lean_object* v___x_4800_; 
v___x_4800_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_4791_, v_uintName_4792_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_);
return v___x_4800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___boxed(lean_object* v_c_4801_, lean_object* v_uintName_4802_, lean_object* v_x_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_){
_start:
{
lean_object* v_res_4810_; 
v_res_4810_ = l_Lean_Compiler_LCNF_casesUIntToMono(v_c_4801_, v_uintName_4802_, v_x_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_);
lean_dec(v_a_4808_);
lean_dec_ref(v_a_4807_);
lean_dec(v_a_4806_);
lean_dec_ref(v_a_4805_);
lean_dec(v_a_4804_);
return v_res_4810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNOptionToMono(lean_object* v_c_4811_, lean_object* v_x_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_){
_start:
{
lean_object* v___x_4819_; 
v___x_4819_ = l_Lean_Compiler_LCNF_casesNOptionToMono___redArg(v_c_4811_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_);
return v___x_4819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNOptionToMono___boxed(lean_object* v_c_4820_, lean_object* v_x_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_){
_start:
{
lean_object* v_res_4828_; 
v_res_4828_ = l_Lean_Compiler_LCNF_casesNOptionToMono(v_c_4820_, v_x_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_);
lean_dec(v_a_4826_);
lean_dec_ref(v_a_4825_);
lean_dec(v_a_4824_);
lean_dec_ref(v_a_4823_);
lean_dec(v_a_4822_);
return v_res_4828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono(lean_object* v_c_4829_, lean_object* v_x_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_){
_start:
{
lean_object* v___x_4837_; 
v___x_4837_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_4829_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_);
return v___x_4837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___boxed(lean_object* v_c_4838_, lean_object* v_x_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_){
_start:
{
lean_object* v_res_4846_; 
v_res_4846_ = l_Lean_Compiler_LCNF_casesIntToMono(v_c_4838_, v_x_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_);
lean_dec(v_a_4844_);
lean_dec_ref(v_a_4843_);
lean_dec(v_a_4842_);
lean_dec_ref(v_a_4841_);
lean_dec(v_a_4840_);
return v_res_4846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono(lean_object* v_c_4847_, lean_object* v_x_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_){
_start:
{
lean_object* v___x_4855_; 
v___x_4855_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_4847_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_);
return v___x_4855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___boxed(lean_object* v_c_4856_, lean_object* v_x_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_){
_start:
{
lean_object* v_res_4864_; 
v_res_4864_ = l_Lean_Compiler_LCNF_casesNatToMono(v_c_4856_, v_x_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_);
lean_dec(v_a_4862_);
lean_dec_ref(v_a_4861_);
lean_dec(v_a_4860_);
lean_dec_ref(v_a_4859_);
lean_dec(v_a_4858_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono(lean_object* v_c_4865_, lean_object* v_x_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_){
_start:
{
lean_object* v___x_4873_; 
v___x_4873_ = l_Lean_Compiler_LCNF_decToMono___redArg(v_c_4865_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_);
return v___x_4873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___boxed(lean_object* v_c_4874_, lean_object* v_x_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_){
_start:
{
lean_object* v_res_4882_; 
v_res_4882_ = l_Lean_Compiler_LCNF_decToMono(v_c_4874_, v_x_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_);
lean_dec(v_a_4880_);
lean_dec_ref(v_a_4879_);
lean_dec(v_a_4878_);
lean_dec_ref(v_a_4877_);
lean_dec(v_a_4876_);
return v_res_4882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(size_t v_sz_4883_, size_t v_i_4884_, lean_object* v_bs_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_){
_start:
{
lean_object* v___x_4892_; 
v___x_4892_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_4883_, v_i_4884_, v_bs_4885_, v___y_4886_, v___y_4888_, v___y_4889_, v___y_4890_);
return v___x_4892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___boxed(lean_object* v_sz_4893_, lean_object* v_i_4894_, lean_object* v_bs_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_){
_start:
{
size_t v_sz_boxed_4902_; size_t v_i_boxed_4903_; lean_object* v_res_4904_; 
v_sz_boxed_4902_ = lean_unbox_usize(v_sz_4893_);
lean_dec(v_sz_4893_);
v_i_boxed_4903_ = lean_unbox_usize(v_i_4894_);
lean_dec(v_i_4894_);
v_res_4904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(v_sz_boxed_4902_, v_i_boxed_4903_, v_bs_4895_, v___y_4896_, v___y_4897_, v___y_4898_, v___y_4899_, v___y_4900_);
lean_dec(v___y_4900_);
lean_dec_ref(v___y_4899_);
lean_dec(v___y_4898_);
lean_dec_ref(v___y_4897_);
lean_dec(v___y_4896_);
return v_res_4904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(lean_object* v_f_4905_, lean_object* v_v_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_){
_start:
{
if (lean_obj_tag(v_v_4906_) == 0)
{
lean_object* v_code_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4937_; 
v_code_4913_ = lean_ctor_get(v_v_4906_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v_v_4906_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4915_ = v_v_4906_;
v_isShared_4916_ = v_isSharedCheck_4937_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_code_4913_);
lean_dec(v_v_4906_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4937_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___x_4917_; 
lean_inc(v___y_4911_);
lean_inc_ref(v___y_4910_);
lean_inc(v___y_4909_);
lean_inc_ref(v___y_4908_);
lean_inc(v___y_4907_);
v___x_4917_ = lean_apply_7(v_f_4905_, v_code_4913_, v___y_4907_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_, lean_box(0));
if (lean_obj_tag(v___x_4917_) == 0)
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4928_; 
v_a_4918_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4920_ = v___x_4917_;
v_isShared_4921_ = v_isSharedCheck_4928_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___x_4917_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4928_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4923_; 
if (v_isShared_4916_ == 0)
{
lean_ctor_set(v___x_4915_, 0, v_a_4918_);
v___x_4923_ = v___x_4915_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_a_4918_);
v___x_4923_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
lean_object* v___x_4925_; 
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 0, v___x_4923_);
v___x_4925_ = v___x_4920_;
goto v_reusejp_4924_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v___x_4923_);
v___x_4925_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4924_;
}
v_reusejp_4924_:
{
return v___x_4925_;
}
}
}
}
else
{
lean_object* v_a_4929_; lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_4936_; 
lean_del_object(v___x_4915_);
v_a_4929_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4936_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4936_ == 0)
{
v___x_4931_ = v___x_4917_;
v_isShared_4932_ = v_isSharedCheck_4936_;
goto v_resetjp_4930_;
}
else
{
lean_inc(v_a_4929_);
lean_dec(v___x_4917_);
v___x_4931_ = lean_box(0);
v_isShared_4932_ = v_isSharedCheck_4936_;
goto v_resetjp_4930_;
}
v_resetjp_4930_:
{
lean_object* v___x_4934_; 
if (v_isShared_4932_ == 0)
{
v___x_4934_ = v___x_4931_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v_a_4929_);
v___x_4934_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
return v___x_4934_;
}
}
}
}
}
else
{
lean_object* v___x_4938_; 
lean_dec_ref(v_f_4905_);
v___x_4938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4938_, 0, v_v_4906_);
return v___x_4938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg___boxed(lean_object* v_f_4939_, lean_object* v_v_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_){
_start:
{
lean_object* v_res_4947_; 
v_res_4947_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_4939_, v_v_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_);
lean_dec(v___y_4945_);
lean_dec_ref(v___y_4944_);
lean_dec(v___y_4943_);
lean_dec_ref(v___y_4942_);
lean_dec(v___y_4941_);
return v_res_4947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(uint8_t v_pu_4948_, lean_object* v_f_4949_, lean_object* v_v_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_){
_start:
{
lean_object* v___x_4957_; 
v___x_4957_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_4949_, v_v_4950_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_);
return v___x_4957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___boxed(lean_object* v_pu_4958_, lean_object* v_f_4959_, lean_object* v_v_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_){
_start:
{
uint8_t v_pu_boxed_4967_; lean_object* v_res_4968_; 
v_pu_boxed_4967_ = lean_unbox(v_pu_4958_);
v_res_4968_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(v_pu_boxed_4967_, v_f_4959_, v_v_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_);
lean_dec(v___y_4965_);
lean_dec_ref(v___y_4964_);
lean_dec(v___y_4963_);
lean_dec_ref(v___y_4962_);
lean_dec(v___y_4961_);
return v_res_4968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(lean_object* v_decl_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_){
_start:
{
lean_object* v_toSignature_4977_; lean_object* v_value_4978_; uint8_t v_recursive_4979_; lean_object* v_inlineAttr_x3f_4980_; lean_object* v___x_4982_; uint8_t v_isShared_4983_; uint8_t v_isSharedCheck_5050_; 
v_toSignature_4977_ = lean_ctor_get(v_decl_4970_, 0);
v_value_4978_ = lean_ctor_get(v_decl_4970_, 1);
v_recursive_4979_ = lean_ctor_get_uint8(v_decl_4970_, sizeof(void*)*3);
v_inlineAttr_x3f_4980_ = lean_ctor_get(v_decl_4970_, 2);
v_isSharedCheck_5050_ = !lean_is_exclusive(v_decl_4970_);
if (v_isSharedCheck_5050_ == 0)
{
v___x_4982_ = v_decl_4970_;
v_isShared_4983_ = v_isSharedCheck_5050_;
goto v_resetjp_4981_;
}
else
{
lean_inc(v_inlineAttr_x3f_4980_);
lean_inc(v_value_4978_);
lean_inc(v_toSignature_4977_);
lean_dec(v_decl_4970_);
v___x_4982_ = lean_box(0);
v_isShared_4983_ = v_isSharedCheck_5050_;
goto v_resetjp_4981_;
}
v_resetjp_4981_:
{
lean_object* v_name_4984_; lean_object* v_type_4985_; lean_object* v_params_4986_; uint8_t v_safe_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_5048_; 
v_name_4984_ = lean_ctor_get(v_toSignature_4977_, 0);
v_type_4985_ = lean_ctor_get(v_toSignature_4977_, 2);
v_params_4986_ = lean_ctor_get(v_toSignature_4977_, 3);
v_safe_4987_ = lean_ctor_get_uint8(v_toSignature_4977_, sizeof(void*)*4);
v_isSharedCheck_5048_ = !lean_is_exclusive(v_toSignature_4977_);
if (v_isSharedCheck_5048_ == 0)
{
lean_object* v_unused_5049_; 
v_unused_5049_ = lean_ctor_get(v_toSignature_4977_, 1);
lean_dec(v_unused_5049_);
v___x_4989_ = v_toSignature_4977_;
v_isShared_4990_ = v_isSharedCheck_5048_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_params_4986_);
lean_inc(v_type_4985_);
lean_inc(v_name_4984_);
lean_dec(v_toSignature_4977_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_5048_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4991_; 
v___x_4991_ = l_Lean_Compiler_LCNF_toMonoType(v_type_4985_, v_a_4974_, v_a_4975_);
if (lean_obj_tag(v___x_4991_) == 0)
{
lean_object* v_a_4992_; size_t v_sz_4993_; size_t v___x_4994_; lean_object* v___x_4995_; 
v_a_4992_ = lean_ctor_get(v___x_4991_, 0);
lean_inc(v_a_4992_);
lean_dec_ref_known(v___x_4991_, 1);
v_sz_4993_ = lean_array_size(v_params_4986_);
v___x_4994_ = ((size_t)0ULL);
v___x_4995_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_4993_, v___x_4994_, v_params_4986_, v_a_4971_, v_a_4973_, v_a_4974_, v_a_4975_);
if (lean_obj_tag(v___x_4995_) == 0)
{
lean_object* v_a_4996_; lean_object* v___f_4997_; lean_object* v___x_4998_; 
v_a_4996_ = lean_ctor_get(v___x_4995_, 0);
lean_inc(v_a_4996_);
lean_dec_ref_known(v___x_4995_, 1);
v___f_4997_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___closed__0));
v___x_4998_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v___f_4997_, v_value_4978_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_);
if (lean_obj_tag(v___x_4998_) == 0)
{
lean_object* v_a_4999_; lean_object* v___x_5000_; lean_object* v___x_5002_; 
v_a_4999_ = lean_ctor_get(v___x_4998_, 0);
lean_inc(v_a_4999_);
lean_dec_ref_known(v___x_4998_, 1);
v___x_5000_ = lean_box(0);
if (v_isShared_4990_ == 0)
{
lean_ctor_set(v___x_4989_, 3, v_a_4996_);
lean_ctor_set(v___x_4989_, 2, v_a_4992_);
lean_ctor_set(v___x_4989_, 1, v___x_5000_);
v___x_5002_ = v___x_4989_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v_name_4984_);
lean_ctor_set(v_reuseFailAlloc_5023_, 1, v___x_5000_);
lean_ctor_set(v_reuseFailAlloc_5023_, 2, v_a_4992_);
lean_ctor_set(v_reuseFailAlloc_5023_, 3, v_a_4996_);
lean_ctor_set_uint8(v_reuseFailAlloc_5023_, sizeof(void*)*4, v_safe_4987_);
v___x_5002_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
lean_object* v___x_5004_; 
if (v_isShared_4983_ == 0)
{
lean_ctor_set(v___x_4982_, 1, v_a_4999_);
lean_ctor_set(v___x_4982_, 0, v___x_5002_);
v___x_5004_ = v___x_4982_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v___x_5002_);
lean_ctor_set(v_reuseFailAlloc_5022_, 1, v_a_4999_);
lean_ctor_set(v_reuseFailAlloc_5022_, 2, v_inlineAttr_x3f_4980_);
lean_ctor_set_uint8(v_reuseFailAlloc_5022_, sizeof(void*)*3, v_recursive_4979_);
v___x_5004_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
lean_object* v___x_5005_; 
lean_inc_ref(v___x_5004_);
v___x_5005_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_5004_, v_a_4975_);
if (lean_obj_tag(v___x_5005_) == 0)
{
lean_object* v___x_5007_; uint8_t v_isShared_5008_; uint8_t v_isSharedCheck_5012_; 
v_isSharedCheck_5012_ = !lean_is_exclusive(v___x_5005_);
if (v_isSharedCheck_5012_ == 0)
{
lean_object* v_unused_5013_; 
v_unused_5013_ = lean_ctor_get(v___x_5005_, 0);
lean_dec(v_unused_5013_);
v___x_5007_ = v___x_5005_;
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
else
{
lean_dec(v___x_5005_);
v___x_5007_ = lean_box(0);
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
v_resetjp_5006_:
{
lean_object* v___x_5010_; 
if (v_isShared_5008_ == 0)
{
lean_ctor_set(v___x_5007_, 0, v___x_5004_);
v___x_5010_ = v___x_5007_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v___x_5004_);
v___x_5010_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
return v___x_5010_;
}
}
}
else
{
lean_object* v_a_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5021_; 
lean_dec_ref(v___x_5004_);
v_a_5014_ = lean_ctor_get(v___x_5005_, 0);
v_isSharedCheck_5021_ = !lean_is_exclusive(v___x_5005_);
if (v_isSharedCheck_5021_ == 0)
{
v___x_5016_ = v___x_5005_;
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_a_5014_);
lean_dec(v___x_5005_);
v___x_5016_ = lean_box(0);
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
v_resetjp_5015_:
{
lean_object* v___x_5019_; 
if (v_isShared_5017_ == 0)
{
v___x_5019_ = v___x_5016_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v_a_5014_);
v___x_5019_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
return v___x_5019_;
}
}
}
}
}
}
else
{
lean_object* v_a_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5031_; 
lean_dec(v_a_4996_);
lean_dec(v_a_4992_);
lean_del_object(v___x_4989_);
lean_dec(v_name_4984_);
lean_del_object(v___x_4982_);
lean_dec(v_inlineAttr_x3f_4980_);
v_a_5024_ = lean_ctor_get(v___x_4998_, 0);
v_isSharedCheck_5031_ = !lean_is_exclusive(v___x_4998_);
if (v_isSharedCheck_5031_ == 0)
{
v___x_5026_ = v___x_4998_;
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_a_5024_);
lean_dec(v___x_4998_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v___x_5029_; 
if (v_isShared_5027_ == 0)
{
v___x_5029_ = v___x_5026_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v_a_5024_);
v___x_5029_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
return v___x_5029_;
}
}
}
}
else
{
lean_object* v_a_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5039_; 
lean_dec(v_a_4992_);
lean_del_object(v___x_4989_);
lean_dec(v_name_4984_);
lean_del_object(v___x_4982_);
lean_dec(v_inlineAttr_x3f_4980_);
lean_dec_ref(v_value_4978_);
v_a_5032_ = lean_ctor_get(v___x_4995_, 0);
v_isSharedCheck_5039_ = !lean_is_exclusive(v___x_4995_);
if (v_isSharedCheck_5039_ == 0)
{
v___x_5034_ = v___x_4995_;
v_isShared_5035_ = v_isSharedCheck_5039_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_a_5032_);
lean_dec(v___x_4995_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5039_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
lean_object* v___x_5037_; 
if (v_isShared_5035_ == 0)
{
v___x_5037_ = v___x_5034_;
goto v_reusejp_5036_;
}
else
{
lean_object* v_reuseFailAlloc_5038_; 
v_reuseFailAlloc_5038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5038_, 0, v_a_5032_);
v___x_5037_ = v_reuseFailAlloc_5038_;
goto v_reusejp_5036_;
}
v_reusejp_5036_:
{
return v___x_5037_;
}
}
}
}
else
{
lean_object* v_a_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5047_; 
lean_del_object(v___x_4989_);
lean_dec_ref(v_params_4986_);
lean_dec(v_name_4984_);
lean_del_object(v___x_4982_);
lean_dec(v_inlineAttr_x3f_4980_);
lean_dec_ref(v_value_4978_);
v_a_5040_ = lean_ctor_get(v___x_4991_, 0);
v_isSharedCheck_5047_ = !lean_is_exclusive(v___x_4991_);
if (v_isSharedCheck_5047_ == 0)
{
v___x_5042_ = v___x_4991_;
v_isShared_5043_ = v_isSharedCheck_5047_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_a_5040_);
lean_dec(v___x_4991_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5047_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
lean_object* v___x_5045_; 
if (v_isShared_5043_ == 0)
{
v___x_5045_ = v___x_5042_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v_a_5040_);
v___x_5045_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
return v___x_5045_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___boxed(lean_object* v_decl_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_){
_start:
{
lean_object* v_res_5058_; 
v_res_5058_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_5051_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_);
lean_dec(v_a_5056_);
lean_dec_ref(v_a_5055_);
lean_dec(v_a_5054_);
lean_dec_ref(v_a_5053_);
lean_dec(v_a_5052_);
return v_res_5058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono(lean_object* v_decl_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_){
_start:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; 
v___x_5065_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_5066_ = lean_st_mk_ref(v___x_5065_);
v___x_5067_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_5059_, v___x_5066_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
if (lean_obj_tag(v___x_5067_) == 0)
{
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5076_; 
v_a_5068_ = lean_ctor_get(v___x_5067_, 0);
v_isSharedCheck_5076_ = !lean_is_exclusive(v___x_5067_);
if (v_isSharedCheck_5076_ == 0)
{
v___x_5070_ = v___x_5067_;
v_isShared_5071_ = v_isSharedCheck_5076_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v___x_5067_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5076_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5072_; lean_object* v___x_5074_; 
v___x_5072_ = lean_st_ref_get(v___x_5066_);
lean_dec(v___x_5066_);
lean_dec(v___x_5072_);
if (v_isShared_5071_ == 0)
{
v___x_5074_ = v___x_5070_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v_a_5068_);
v___x_5074_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
return v___x_5074_;
}
}
}
else
{
lean_dec(v___x_5066_);
return v___x_5067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono___boxed(lean_object* v_decl_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_){
_start:
{
lean_object* v_res_5083_; 
v_res_5083_ = l_Lean_Compiler_LCNF_Decl_toMono(v_decl_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_);
lean_dec(v_a_5081_);
lean_dec_ref(v_a_5080_);
lean_dec(v_a_5079_);
lean_dec_ref(v_a_5078_);
return v_res_5083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(size_t v_sz_5084_, size_t v_i_5085_, lean_object* v_bs_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_){
_start:
{
uint8_t v___x_5092_; 
v___x_5092_ = lean_usize_dec_lt(v_i_5085_, v_sz_5084_);
if (v___x_5092_ == 0)
{
lean_object* v___x_5093_; 
v___x_5093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5093_, 0, v_bs_5086_);
return v___x_5093_;
}
else
{
lean_object* v_v_5094_; lean_object* v___x_5095_; 
v_v_5094_ = lean_array_uget_borrowed(v_bs_5086_, v_i_5085_);
lean_inc(v_v_5094_);
v___x_5095_ = l_Lean_Compiler_LCNF_Decl_toMono(v_v_5094_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_);
if (lean_obj_tag(v___x_5095_) == 0)
{
lean_object* v_a_5096_; lean_object* v___x_5097_; lean_object* v_bs_x27_5098_; size_t v___x_5099_; size_t v___x_5100_; lean_object* v___x_5101_; 
v_a_5096_ = lean_ctor_get(v___x_5095_, 0);
lean_inc(v_a_5096_);
lean_dec_ref_known(v___x_5095_, 1);
v___x_5097_ = lean_unsigned_to_nat(0u);
v_bs_x27_5098_ = lean_array_uset(v_bs_5086_, v_i_5085_, v___x_5097_);
v___x_5099_ = ((size_t)1ULL);
v___x_5100_ = lean_usize_add(v_i_5085_, v___x_5099_);
v___x_5101_ = lean_array_uset(v_bs_x27_5098_, v_i_5085_, v_a_5096_);
v_i_5085_ = v___x_5100_;
v_bs_5086_ = v___x_5101_;
goto _start;
}
else
{
lean_object* v_a_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5110_; 
lean_dec_ref(v_bs_5086_);
v_a_5103_ = lean_ctor_get(v___x_5095_, 0);
v_isSharedCheck_5110_ = !lean_is_exclusive(v___x_5095_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5105_ = v___x_5095_;
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_a_5103_);
lean_dec(v___x_5095_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v___x_5108_; 
if (v_isShared_5106_ == 0)
{
v___x_5108_ = v___x_5105_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_a_5103_);
v___x_5108_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
return v___x_5108_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0___boxed(lean_object* v_sz_5111_, lean_object* v_i_5112_, lean_object* v_bs_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_){
_start:
{
size_t v_sz_boxed_5119_; size_t v_i_boxed_5120_; lean_object* v_res_5121_; 
v_sz_boxed_5119_ = lean_unbox_usize(v_sz_5111_);
lean_dec(v_sz_5111_);
v_i_boxed_5120_ = lean_unbox_usize(v_i_5112_);
lean_dec(v_i_5112_);
v_res_5121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_boxed_5119_, v_i_boxed_5120_, v_bs_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_);
lean_dec(v___y_5117_);
lean_dec_ref(v___y_5116_);
lean_dec(v___y_5115_);
lean_dec_ref(v___y_5114_);
return v_res_5121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0(lean_object* v_x_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_){
_start:
{
size_t v_sz_5128_; size_t v___x_5129_; lean_object* v___x_5130_; 
v_sz_5128_ = lean_array_size(v_x_5122_);
v___x_5129_ = ((size_t)0ULL);
v___x_5130_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_5128_, v___x_5129_, v_x_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_);
return v___x_5130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0___boxed(lean_object* v_x_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_){
_start:
{
lean_object* v_res_5137_; 
v_res_5137_ = l_Lean_Compiler_LCNF_toMono___lam__0(v_x_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_);
lean_dec(v___y_5135_);
lean_dec_ref(v___y_5134_);
lean_dec(v___y_5133_);
lean_dec_ref(v___y_5132_);
return v_res_5137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5220_; uint8_t v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; 
v___x_5220_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_));
v___x_5221_ = 1;
v___x_5222_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_));
v___x_5223_ = l_Lean_registerTraceClass(v___x_5220_, v___x_5221_, v___x_5222_);
return v___x_5223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2____boxed(lean_object* v_a_5224_){
_start:
{
lean_object* v_res_5225_; 
v_res_5225_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_();
return v_res_5225_;
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
