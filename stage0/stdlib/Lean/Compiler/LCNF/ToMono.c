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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_redArg"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__10_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__10_value),LEAN_SCALAR_PTR_LITERAL(174, 35, 1, 83, 6, 52, 87, 186)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__11_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Compiler.LCNF.ToMono"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__12_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Compiler.LCNF.LetValue.toMono"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__13_value;
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__14_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_LetValue_toMono___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__15;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__16_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LetValue_toMono___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__16_value)}};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___closed__17 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__17_value;
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
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_8236__overap_808_; lean_object* v___x_809_; 
v___x_805_ = l_StateRefT_x27_instMonad___redArg(v___x_804_);
v___x_806_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5);
v___x_807_ = l_instInhabitedOfMonad___redArg(v___x_805_, v___x_806_);
v___x_8236__overap_808_ = lean_panic_fn_borrowed(v___x_807_, v_msg_749_);
lean_dec(v___x_807_);
lean_inc(v___y_754_);
lean_inc_ref(v___y_753_);
lean_inc(v___y_752_);
lean_inc_ref(v___y_751_);
lean_inc(v___y_750_);
v___x_809_ = lean_apply_6(v___x_8236__overap_808_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, lean_box(0));
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
static lean_object* _init_l_Lean_Compiler_LCNF_LetValue_toMono___closed__15(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_880_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__14));
v___x_881_ = lean_unsigned_to_nat(6u);
v___x_882_ = lean_unsigned_to_nat(101u);
v___x_883_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__13));
v___x_884_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_885_ = l_mkPanicMessageWithDecl(v___x_884_, v___x_883_, v___x_882_, v___x_881_, v___x_880_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono(lean_object* v_e_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
switch(lean_obj_tag(v_e_890_))
{
case 2:
{
lean_object* v_typeName_897_; lean_object* v_idx_898_; lean_object* v_struct_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v_typeName_897_ = lean_ctor_get(v_e_890_, 0);
v_idx_898_ = lean_ctor_get(v_e_890_, 1);
v_struct_899_ = lean_ctor_get(v_e_890_, 2);
v___x_900_ = lean_st_ref_get(v_a_891_);
v___x_901_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_900_, v_struct_899_);
lean_dec(v___x_900_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; 
lean_inc(v_typeName_897_);
v___x_902_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_typeName_897_, v_a_894_, v_a_895_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_922_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_922_ == 0)
{
v___x_905_ = v___x_902_;
v_isShared_906_ = v_isSharedCheck_922_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_902_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_922_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
if (lean_obj_tag(v_a_903_) == 1)
{
lean_object* v_val_907_; lean_object* v_fieldIdx_908_; uint8_t v___x_909_; 
lean_inc(v_struct_899_);
lean_inc(v_idx_898_);
lean_dec_ref_known(v_e_890_, 3);
v_val_907_ = lean_ctor_get(v_a_903_, 0);
lean_inc(v_val_907_);
lean_dec_ref_known(v_a_903_, 1);
v_fieldIdx_908_ = lean_ctor_get(v_val_907_, 2);
lean_inc(v_fieldIdx_908_);
lean_dec(v_val_907_);
v___x_909_ = lean_nat_dec_eq(v_fieldIdx_908_, v_idx_898_);
lean_dec(v_idx_898_);
lean_dec(v_fieldIdx_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_912_; 
lean_dec(v_struct_899_);
v___x_910_ = lean_box(1);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_910_);
v___x_912_ = v___x_905_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_914_ = ((lean_object*)(l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0));
v___x_915_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_915_, 0, v_struct_899_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_915_);
v___x_917_ = v___x_905_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_915_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
else
{
lean_object* v___x_920_; 
lean_dec(v_a_903_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v_e_890_);
v___x_920_ = v___x_905_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_e_890_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec_ref_known(v_e_890_, 3);
v_a_923_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_902_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_902_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec_ref_known(v_e_890_, 3);
v___x_931_ = lean_box(1);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
return v___x_932_;
}
}
case 3:
{
lean_object* v_declName_933_; lean_object* v_args_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_1126_; 
v_declName_933_ = lean_ctor_get(v_e_890_, 0);
v_args_934_ = lean_ctor_get(v_e_890_, 2);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_e_890_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; 
v_unused_1127_ = lean_ctor_get(v_e_890_, 1);
lean_dec(v_unused_1127_);
v___x_936_ = v_e_890_;
v_isShared_937_ = v_isSharedCheck_1126_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_args_934_);
lean_inc(v_declName_933_);
lean_dec(v_e_890_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_1126_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v_type_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; uint8_t v___y_976_; lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__2));
v___x_999_ = lean_name_eq(v_declName_933_, v___x_998_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_1000_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__4));
v___x_1001_ = lean_name_eq(v_declName_933_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__7));
v___x_1003_ = lean_name_eq(v_declName_933_, v___x_1002_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; uint8_t v___x_1005_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; 
v___x_1004_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__9));
v___x_1005_ = lean_name_eq(v_declName_933_, v___x_1004_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1064_; lean_object* v_env_1065_; lean_object* v___x_1066_; 
v___x_1064_ = lean_st_ref_get(v_a_895_);
v_env_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc_ref(v_env_1065_);
lean_dec(v___x_1064_);
lean_inc(v_declName_933_);
v___x_1066_ = l_Lean_Environment_find_x3f(v_env_1065_, v_declName_933_, v___x_1005_);
if (lean_obj_tag(v___x_1066_) == 1)
{
lean_object* v_val_1067_; 
v_val_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_val_1067_);
lean_dec_ref_known(v___x_1066_, 1);
if (lean_obj_tag(v_val_1067_) == 6)
{
lean_object* v_val_1068_; lean_object* v_induct_1069_; lean_object* v_numParams_1070_; lean_object* v___x_1071_; 
lean_del_object(v___x_936_);
lean_dec(v_declName_933_);
v_val_1068_ = lean_ctor_get(v_val_1067_, 0);
lean_inc_ref(v_val_1068_);
lean_dec_ref_known(v_val_1067_, 1);
v_induct_1069_ = lean_ctor_get(v_val_1068_, 1);
v_numParams_1070_ = lean_ctor_get(v_val_1068_, 3);
lean_inc(v_induct_1069_);
v___x_1071_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_induct_1069_, v_a_894_, v_a_895_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
if (lean_obj_tag(v_a_1072_) == 1)
{
lean_object* v_val_1073_; lean_object* v_fieldIdx_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_inc(v_numParams_1070_);
lean_dec_ref(v_val_1068_);
v_val_1073_ = lean_ctor_get(v_a_1072_, 0);
lean_inc(v_val_1073_);
lean_dec_ref_known(v_a_1072_, 1);
v_fieldIdx_1074_ = lean_ctor_get(v_val_1073_, 2);
lean_inc(v_fieldIdx_1074_);
lean_dec(v_val_1073_);
v___x_1075_ = lean_box(0);
v___x_1076_ = lean_nat_add(v_numParams_1070_, v_fieldIdx_1074_);
lean_dec(v_fieldIdx_1074_);
lean_dec(v_numParams_1070_);
v___x_1077_ = lean_array_get(v___x_1075_, v_args_934_, v___x_1076_);
lean_dec(v___x_1076_);
lean_dec_ref(v_args_934_);
v___x_1078_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_1077_);
lean_dec(v___x_1077_);
v_e_890_ = v___x_1078_;
goto _start;
}
else
{
lean_object* v___x_1080_; 
lean_dec(v_a_1072_);
v___x_1080_ = l_Lean_Compiler_LCNF_ctorAppToMono(v_val_1068_, v_args_934_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
return v___x_1080_;
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec_ref(v_val_1068_);
lean_dec_ref(v_args_934_);
v_a_1081_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1071_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1071_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
else
{
lean_dec(v_val_1067_);
v___y_1007_ = v_a_891_;
v___y_1008_ = v_a_892_;
v___y_1009_ = v_a_893_;
v___y_1010_ = v_a_894_;
v___y_1011_ = v_a_895_;
goto v___jp_1006_;
}
}
else
{
lean_dec(v___x_1066_);
v___y_1007_ = v_a_891_;
v___y_1008_ = v_a_892_;
v___y_1009_ = v_a_893_;
v___y_1010_ = v_a_894_;
v___y_1011_ = v_a_895_;
goto v___jp_1006_;
}
}
else
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
lean_del_object(v___x_936_);
lean_dec_ref(v_args_934_);
lean_dec(v_declName_933_);
v___x_1089_ = lean_obj_once(&l_Lean_Compiler_LCNF_LetValue_toMono___closed__15, &l_Lean_Compiler_LCNF_LetValue_toMono___closed__15_once, _init_l_Lean_Compiler_LCNF_LetValue_toMono___closed__15);
v___x_1090_ = l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(v___x_1089_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
return v___x_1090_;
}
v___jp_1006_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_st_ref_get(v___y_1011_);
lean_dec(v___x_1012_);
lean_inc(v_declName_933_);
v___x_1013_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_933_, v___y_1011_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1014_);
lean_dec_ref_known(v___x_1013_, 1);
if (lean_obj_tag(v_a_1014_) == 1)
{
lean_object* v_val_1015_; lean_object* v_toSignature_1016_; lean_object* v_value_1017_; lean_object* v_type_1018_; lean_object* v_params_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v_val_1015_ = lean_ctor_get(v_a_1014_, 0);
lean_inc(v_val_1015_);
lean_dec_ref_known(v_a_1014_, 1);
v_toSignature_1016_ = lean_ctor_get(v_val_1015_, 0);
v_value_1017_ = lean_ctor_get(v_val_1015_, 1);
v_type_1018_ = lean_ctor_get(v_toSignature_1016_, 2);
v_params_1019_ = lean_ctor_get(v_toSignature_1016_, 3);
lean_inc_ref(v_params_1019_);
v___x_1020_ = lean_array_get_size(v_params_1019_);
v___x_1021_ = lean_array_get_size(v_args_934_);
v___x_1022_ = lean_nat_dec_le(v___x_1020_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_inc_ref(v_type_1018_);
lean_dec_ref(v_params_1019_);
lean_dec(v_val_1015_);
v_type_939_ = v_type_1018_;
v___y_940_ = v___y_1007_;
v___y_941_ = v___y_1008_;
v___y_942_ = v___y_1009_;
v___y_943_ = v___y_1010_;
v___y_944_ = v___y_1011_;
goto v___jp_938_;
}
else
{
if (lean_obj_tag(v_value_1017_) == 0)
{
lean_object* v_code_1023_; 
v_code_1023_ = lean_ctor_get(v_value_1017_, 0);
if (lean_obj_tag(v_code_1023_) == 0)
{
lean_object* v_decl_1024_; lean_object* v_value_1025_; 
v_decl_1024_ = lean_ctor_get(v_code_1023_, 0);
v_value_1025_ = lean_ctor_get(v_decl_1024_, 3);
if (lean_obj_tag(v_value_1025_) == 3)
{
lean_object* v_k_1026_; 
v_k_1026_ = lean_ctor_get(v_code_1023_, 1);
if (lean_obj_tag(v_k_1026_) == 5)
{
lean_object* v_fvarId_1027_; lean_object* v_declName_1028_; lean_object* v_args_1029_; lean_object* v_fvarId_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v_fvarId_1027_ = lean_ctor_get(v_decl_1024_, 0);
v_declName_1028_ = lean_ctor_get(v_value_1025_, 0);
v_args_1029_ = lean_ctor_get(v_value_1025_, 2);
lean_inc_ref(v_args_1029_);
v_fvarId_1030_ = lean_ctor_get(v_k_1026_, 0);
v___x_1031_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__11));
lean_inc(v_declName_933_);
v___x_1032_ = l_Lean_Name_append(v_declName_933_, v___x_1031_);
v___x_1033_ = lean_name_eq(v_declName_1028_, v___x_1032_);
if (v___x_1033_ == 0)
{
v___y_967_ = v___y_1007_;
v___y_968_ = v___y_1008_;
v___y_969_ = v_params_1019_;
v___y_970_ = v_val_1015_;
v___y_971_ = v___y_1009_;
v___y_972_ = v___y_1011_;
v___y_973_ = v___x_1032_;
v___y_974_ = v___y_1010_;
v___y_975_ = v_args_1029_;
v___y_976_ = v___x_1005_;
goto v___jp_966_;
}
else
{
uint8_t v___x_1034_; 
v___x_1034_ = l_Lean_instBEqFVarId_beq(v_fvarId_1030_, v_fvarId_1027_);
v___y_967_ = v___y_1007_;
v___y_968_ = v___y_1008_;
v___y_969_ = v_params_1019_;
v___y_970_ = v_val_1015_;
v___y_971_ = v___y_1009_;
v___y_972_ = v___y_1011_;
v___y_973_ = v___x_1032_;
v___y_974_ = v___y_1010_;
v___y_975_ = v_args_1029_;
v___y_976_ = v___x_1034_;
goto v___jp_966_;
}
}
else
{
lean_inc_ref(v_type_1018_);
lean_dec_ref(v_params_1019_);
lean_dec(v_val_1015_);
v_type_939_ = v_type_1018_;
v___y_940_ = v___y_1007_;
v___y_941_ = v___y_1008_;
v___y_942_ = v___y_1009_;
v___y_943_ = v___y_1010_;
v___y_944_ = v___y_1011_;
goto v___jp_938_;
}
}
else
{
lean_inc_ref(v_type_1018_);
lean_dec_ref(v_params_1019_);
lean_dec(v_val_1015_);
v_type_939_ = v_type_1018_;
v___y_940_ = v___y_1007_;
v___y_941_ = v___y_1008_;
v___y_942_ = v___y_1009_;
v___y_943_ = v___y_1010_;
v___y_944_ = v___y_1011_;
goto v___jp_938_;
}
}
else
{
lean_inc_ref(v_type_1018_);
lean_dec_ref(v_params_1019_);
lean_dec(v_val_1015_);
v_type_939_ = v_type_1018_;
v___y_940_ = v___y_1007_;
v___y_941_ = v___y_1008_;
v___y_942_ = v___y_1009_;
v___y_943_ = v___y_1010_;
v___y_944_ = v___y_1011_;
goto v___jp_938_;
}
}
else
{
lean_inc_ref(v_type_1018_);
lean_dec_ref(v_params_1019_);
lean_dec(v_val_1015_);
v_type_939_ = v_type_1018_;
v___y_940_ = v___y_1007_;
v___y_941_ = v___y_1008_;
v___y_942_ = v___y_1009_;
v___y_943_ = v___y_1010_;
v___y_944_ = v___y_1011_;
goto v___jp_938_;
}
}
}
else
{
size_t v_sz_1035_; size_t v___x_1036_; lean_object* v___x_1037_; 
lean_dec(v_a_1014_);
lean_del_object(v___x_936_);
v_sz_1035_ = lean_array_size(v_args_934_);
v___x_1036_ = ((size_t)0ULL);
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_1035_, v___x_1036_, v_args_934_, v___y_1007_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1047_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1047_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1047_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1042_ = lean_box(0);
v___x_1043_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1043_, 0, v_declName_933_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
lean_ctor_set(v___x_1043_, 2, v_a_1038_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1043_);
v___x_1045_ = v___x_1040_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec(v_declName_933_);
v_a_1048_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1037_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1037_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_del_object(v___x_936_);
lean_dec_ref(v_args_934_);
lean_dec(v_declName_933_);
v_a_1056_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1013_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1013_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
lean_del_object(v___x_936_);
lean_dec_ref(v_args_934_);
lean_dec(v_declName_933_);
v___x_1091_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__17));
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
return v___x_1092_;
}
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_del_object(v___x_936_);
lean_dec(v_declName_933_);
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_unsigned_to_nat(2u);
v___x_1095_ = lean_array_get_borrowed(v___x_1093_, v_args_934_, v___x_1094_);
if (lean_obj_tag(v___x_1095_) == 1)
{
lean_object* v_fvarId_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v_extraArgs_1100_; lean_object* v___x_1101_; 
v_fvarId_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_fvarId_1096_);
v___x_1097_ = lean_array_get_size(v_args_934_);
v___x_1098_ = lean_unsigned_to_nat(3u);
v___x_1099_ = lean_nat_sub(v___x_1097_, v___x_1098_);
v_extraArgs_1100_ = lean_mk_empty_array_with_capacity(v___x_1099_);
lean_dec(v___x_1099_);
v___x_1101_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v___x_1097_, v_args_934_, v___x_1098_, v_extraArgs_1100_, v_a_891_);
lean_dec_ref(v_args_934_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1110_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1110_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1110_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1106_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1106_, 0, v_fvarId_1096_);
lean_ctor_set(v___x_1106_, 1, v_a_1102_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1106_);
v___x_1108_ = v___x_1104_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec(v_fvarId_1096_);
v_a_1111_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1101_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1101_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_dec_ref(v_args_934_);
v___x_1119_ = lean_box(1);
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
return v___x_1120_;
}
}
}
else
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_del_object(v___x_936_);
lean_dec(v_declName_933_);
v___x_1121_ = lean_box(0);
v___x_1122_ = lean_unsigned_to_nat(2u);
v___x_1123_ = lean_array_get(v___x_1121_, v_args_934_, v___x_1122_);
lean_dec_ref(v_args_934_);
v___x_1124_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_1123_);
lean_dec(v___x_1123_);
v___x_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
return v___x_1125_;
}
v___jp_938_:
{
lean_object* v___x_945_; 
v___x_945_ = l_Lean_Compiler_LCNF_argsToMonoWithFnType(v_args_934_, v_type_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec_ref(v_args_934_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_957_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_957_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_957_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_957_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_950_ = lean_box(0);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 2, v_a_946_);
lean_ctor_set(v___x_936_, 1, v___x_950_);
v___x_952_ = v___x_936_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_declName_933_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v_a_946_);
v___x_952_ = v_reuseFailAlloc_956_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_954_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_952_);
v___x_954_ = v___x_948_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
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
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_del_object(v___x_936_);
lean_dec(v_declName_933_);
v_a_958_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_945_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_945_);
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
v___jp_966_:
{
if (v___y_976_ == 0)
{
lean_object* v_toSignature_977_; lean_object* v_type_978_; 
lean_dec_ref(v___y_975_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_969_);
v_toSignature_977_ = lean_ctor_get(v___y_970_, 0);
lean_inc_ref(v_toSignature_977_);
lean_dec_ref(v___y_970_);
v_type_978_ = lean_ctor_get(v_toSignature_977_, 2);
lean_inc_ref(v_type_978_);
lean_dec_ref(v_toSignature_977_);
v_type_939_ = v_type_978_;
v___y_940_ = v___y_967_;
v___y_941_ = v___y_968_;
v___y_942_ = v___y_971_;
v___y_943_ = v___y_974_;
v___y_944_ = v___y_972_;
goto v___jp_938_;
}
else
{
lean_object* v___x_979_; 
lean_dec_ref(v___y_970_);
lean_del_object(v___x_936_);
lean_dec(v_declName_933_);
v___x_979_ = l_Lean_Compiler_LCNF_argsToMonoRedArg(v_args_934_, v___y_969_, v___y_975_, v___y_967_, v___y_968_, v___y_971_, v___y_974_, v___y_972_);
lean_dec_ref(v___y_975_);
lean_dec_ref(v___y_969_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_989_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_989_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_989_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_989_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_984_ = lean_box(0);
v___x_985_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_985_, 0, v___y_973_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
lean_ctor_set(v___x_985_, 2, v_a_980_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v___x_985_);
v___x_987_ = v___x_982_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v___y_973_);
v_a_990_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_979_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_979_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_fvarId_1128_; lean_object* v_args_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1159_; 
v_fvarId_1128_ = lean_ctor_get(v_e_890_, 0);
v_args_1129_ = lean_ctor_get(v_e_890_, 1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_e_890_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1131_ = v_e_890_;
v_isShared_1132_ = v_isSharedCheck_1159_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_args_1129_);
lean_inc(v_fvarId_1128_);
lean_dec(v_e_890_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1159_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = lean_st_ref_get(v_a_891_);
v___x_1134_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_1133_, v_fvarId_1128_);
lean_dec(v___x_1133_);
if (v___x_1134_ == 0)
{
size_t v_sz_1135_; size_t v___x_1136_; lean_object* v___x_1137_; 
v_sz_1135_ = lean_array_size(v_args_1129_);
v___x_1136_ = ((size_t)0ULL);
v___x_1137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_1135_, v___x_1136_, v_args_1129_, v_a_891_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1148_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1140_ = v___x_1137_;
v_isShared_1141_ = v_isSharedCheck_1148_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1137_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1148_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 1, v_a_1138_);
v___x_1143_ = v___x_1131_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_fvarId_1128_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1145_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1143_);
v___x_1145_ = v___x_1140_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_del_object(v___x_1131_);
lean_dec(v_fvarId_1128_);
v_a_1149_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1137_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1137_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_del_object(v___x_1131_);
lean_dec_ref(v_args_1129_);
lean_dec(v_fvarId_1128_);
v___x_1157_ = lean_box(1);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
return v___x_1158_;
}
}
}
default: 
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v_e_890_);
return v___x_1160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___boxed(lean_object* v_e_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_Compiler_LCNF_LetValue_toMono(v_e_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
lean_dec(v_a_1162_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1(lean_object* v_upperBound_1169_, lean_object* v_args_1170_, lean_object* v_inst_1171_, lean_object* v_R_1172_, lean_object* v_a_1173_, lean_object* v_b_1174_, lean_object* v_c_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v_upperBound_1169_, v_args_1170_, v_a_1173_, v_b_1174_, v___y_1176_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___boxed(lean_object* v_upperBound_1183_, lean_object* v_args_1184_, lean_object* v_inst_1185_, lean_object* v_R_1186_, lean_object* v_a_1187_, lean_object* v_b_1188_, lean_object* v_c_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1(v_upperBound_1183_, v_args_1184_, v_inst_1185_, v_R_1186_, v_a_1187_, v_b_1188_, v_c_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v_args_1184_);
lean_dec(v_upperBound_1183_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono(lean_object* v_decl_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v_type_1204_; lean_object* v_value_1205_; lean_object* v___x_1206_; 
v_type_1204_ = lean_ctor_get(v_decl_1197_, 2);
v_value_1205_ = lean_ctor_get(v_decl_1197_, 3);
lean_inc_ref(v_type_1204_);
v___x_1206_ = l_Lean_Compiler_LCNF_toMonoType(v_type_1204_, v_a_1201_, v_a_1202_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1208_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1207_);
lean_dec_ref_known(v___x_1206_, 1);
lean_inc(v_value_1205_);
v___x_1208_ = l_Lean_Compiler_LCNF_LetValue_toMono(v_value_1205_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; uint8_t v___x_1210_; lean_object* v___x_1211_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1209_);
lean_dec_ref_known(v___x_1208_, 1);
v___x_1210_ = 0;
v___x_1211_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_1210_, v_decl_1197_, v_a_1207_, v_a_1209_, v_a_1200_);
return v___x_1211_;
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec(v_a_1207_);
lean_dec_ref(v_decl_1197_);
v_a_1212_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1208_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1208_);
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
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec_ref(v_decl_1197_);
v_a_1220_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1206_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1206_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono___boxed(lean_object* v_decl_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_Compiler_LCNF_LetDecl_toMono(v_decl_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(lean_object* v_msg_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v_toApplicative_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1307_; 
v___x_1243_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1244_ = l_StateRefT_x27_instMonad___redArg(v___x_1243_);
v_toApplicative_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1307_ == 0)
{
lean_object* v_unused_1308_; 
v_unused_1308_ = lean_ctor_get(v___x_1244_, 1);
lean_dec(v_unused_1308_);
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1307_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_toApplicative_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1307_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v_toFunctor_1249_; lean_object* v_toSeq_1250_; lean_object* v_toSeqLeft_1251_; lean_object* v_toSeqRight_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1305_; 
v_toFunctor_1249_ = lean_ctor_get(v_toApplicative_1245_, 0);
v_toSeq_1250_ = lean_ctor_get(v_toApplicative_1245_, 2);
v_toSeqLeft_1251_ = lean_ctor_get(v_toApplicative_1245_, 3);
v_toSeqRight_1252_ = lean_ctor_get(v_toApplicative_1245_, 4);
v_isSharedCheck_1305_ = !lean_is_exclusive(v_toApplicative_1245_);
if (v_isSharedCheck_1305_ == 0)
{
lean_object* v_unused_1306_; 
v_unused_1306_ = lean_ctor_get(v_toApplicative_1245_, 1);
lean_dec(v_unused_1306_);
v___x_1254_ = v_toApplicative_1245_;
v_isShared_1255_ = v_isSharedCheck_1305_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_toSeqRight_1252_);
lean_inc(v_toSeqLeft_1251_);
lean_inc(v_toSeq_1250_);
lean_inc(v_toFunctor_1249_);
lean_dec(v_toApplicative_1245_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1305_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___f_1256_; lean_object* v___f_1257_; lean_object* v___f_1258_; lean_object* v___f_1259_; lean_object* v___x_1260_; lean_object* v___f_1261_; lean_object* v___f_1262_; lean_object* v___f_1263_; lean_object* v___x_1265_; 
v___f_1256_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1257_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1249_);
v___f_1258_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1258_, 0, v_toFunctor_1249_);
v___f_1259_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1259_, 0, v_toFunctor_1249_);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___f_1258_);
lean_ctor_set(v___x_1260_, 1, v___f_1259_);
v___f_1261_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1261_, 0, v_toSeqRight_1252_);
v___f_1262_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1262_, 0, v_toSeqLeft_1251_);
v___f_1263_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1263_, 0, v_toSeq_1250_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 4, v___f_1261_);
lean_ctor_set(v___x_1254_, 3, v___f_1262_);
lean_ctor_set(v___x_1254_, 2, v___f_1263_);
lean_ctor_set(v___x_1254_, 1, v___f_1256_);
lean_ctor_set(v___x_1254_, 0, v___x_1260_);
v___x_1265_ = v___x_1254_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v___f_1256_);
lean_ctor_set(v_reuseFailAlloc_1304_, 2, v___f_1263_);
lean_ctor_set(v_reuseFailAlloc_1304_, 3, v___f_1262_);
lean_ctor_set(v_reuseFailAlloc_1304_, 4, v___f_1261_);
v___x_1265_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1267_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 1, v___f_1257_);
lean_ctor_set(v___x_1247_, 0, v___x_1265_);
v___x_1267_ = v___x_1247_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v___f_1257_);
v___x_1267_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1268_; lean_object* v_toApplicative_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1301_; 
v___x_1268_ = l_StateRefT_x27_instMonad___redArg(v___x_1267_);
v_toApplicative_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1301_ == 0)
{
lean_object* v_unused_1302_; 
v_unused_1302_ = lean_ctor_get(v___x_1268_, 1);
lean_dec(v_unused_1302_);
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1301_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_toApplicative_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1301_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v_toFunctor_1273_; lean_object* v_toSeq_1274_; lean_object* v_toSeqLeft_1275_; lean_object* v_toSeqRight_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1299_; 
v_toFunctor_1273_ = lean_ctor_get(v_toApplicative_1269_, 0);
v_toSeq_1274_ = lean_ctor_get(v_toApplicative_1269_, 2);
v_toSeqLeft_1275_ = lean_ctor_get(v_toApplicative_1269_, 3);
v_toSeqRight_1276_ = lean_ctor_get(v_toApplicative_1269_, 4);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_toApplicative_1269_);
if (v_isSharedCheck_1299_ == 0)
{
lean_object* v_unused_1300_; 
v_unused_1300_ = lean_ctor_get(v_toApplicative_1269_, 1);
lean_dec(v_unused_1300_);
v___x_1278_ = v_toApplicative_1269_;
v_isShared_1279_ = v_isSharedCheck_1299_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_toSeqRight_1276_);
lean_inc(v_toSeqLeft_1275_);
lean_inc(v_toSeq_1274_);
lean_inc(v_toFunctor_1273_);
lean_dec(v_toApplicative_1269_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1299_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___f_1280_; lean_object* v___f_1281_; lean_object* v___f_1282_; lean_object* v___f_1283_; lean_object* v___x_1284_; lean_object* v___f_1285_; lean_object* v___f_1286_; lean_object* v___f_1287_; lean_object* v___x_1289_; 
v___f_1280_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1281_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1273_);
v___f_1282_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1282_, 0, v_toFunctor_1273_);
v___f_1283_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1283_, 0, v_toFunctor_1273_);
v___x_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___f_1282_);
lean_ctor_set(v___x_1284_, 1, v___f_1283_);
v___f_1285_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1285_, 0, v_toSeqRight_1276_);
v___f_1286_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1286_, 0, v_toSeqLeft_1275_);
v___f_1287_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1287_, 0, v_toSeq_1274_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 4, v___f_1285_);
lean_ctor_set(v___x_1278_, 3, v___f_1286_);
lean_ctor_set(v___x_1278_, 2, v___f_1287_);
lean_ctor_set(v___x_1278_, 1, v___f_1280_);
lean_ctor_set(v___x_1278_, 0, v___x_1284_);
v___x_1289_ = v___x_1278_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1284_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v___f_1280_);
lean_ctor_set(v_reuseFailAlloc_1298_, 2, v___f_1287_);
lean_ctor_set(v_reuseFailAlloc_1298_, 3, v___f_1286_);
lean_ctor_set(v_reuseFailAlloc_1298_, 4, v___f_1285_);
v___x_1289_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1291_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 1, v___f_1281_);
lean_ctor_set(v___x_1271_, 0, v___x_1289_);
v___x_1291_ = v___x_1271_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v___f_1281_);
v___x_1291_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_4525__overap_1295_; lean_object* v___x_1296_; 
v___x_1292_ = l_StateRefT_x27_instMonad___redArg(v___x_1291_);
v___x_1293_ = lean_box(0);
v___x_1294_ = l_instInhabitedOfMonad___redArg(v___x_1292_, v___x_1293_);
v___x_4525__overap_1295_ = lean_panic_fn_borrowed(v___x_1294_, v_msg_1236_);
lean_dec(v___x_1294_);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
lean_inc(v___y_1239_);
lean_inc_ref(v___y_1238_);
lean_inc(v___y_1237_);
v___x_1296_ = lean_apply_6(v___x_4525__overap_1295_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, lean_box(0));
return v___x_1296_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0___boxed(lean_object* v_msg_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v_msg_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
return v_res_1316_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1318_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__14));
v___x_1319_ = lean_unsigned_to_nat(11u);
v___x_1320_ = lean_unsigned_to_nat(150u);
v___x_1321_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__0));
v___x_1322_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1323_ = l_mkPanicMessageWithDecl(v___x_1322_, v___x_1321_, v___x_1320_, v___x_1319_, v___x_1318_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(lean_object* v_upperBound_1324_, lean_object* v_a_1325_, lean_object* v_b_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v_a_1334_; uint8_t v___x_1338_; 
v___x_1338_ = lean_nat_dec_lt(v_a_1325_, v_upperBound_1324_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; 
lean_dec(v_a_1325_);
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v_b_1326_);
return v___x_1339_;
}
else
{
if (lean_obj_tag(v_b_1326_) == 7)
{
lean_object* v_body_1340_; 
v_body_1340_ = lean_ctor_get(v_b_1326_, 2);
lean_inc_ref(v_body_1340_);
lean_dec_ref_known(v_b_1326_, 3);
v_a_1334_ = v_body_1340_;
goto v___jp_1333_;
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1);
v___x_1342_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v___x_1341_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_dec_ref_known(v___x_1342_, 1);
v_a_1334_ = v_b_1326_;
goto v___jp_1333_;
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec_ref(v_b_1326_);
lean_dec(v_a_1325_);
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
v___jp_1333_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = lean_unsigned_to_nat(1u);
v___x_1336_ = lean_nat_add(v_a_1325_, v___x_1335_);
lean_dec(v_a_1325_);
v_a_1325_ = v___x_1336_;
v_b_1326_ = v_a_1334_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___boxed(lean_object* v_upperBound_1351_, lean_object* v_a_1352_, lean_object* v_b_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_upperBound_1351_, v_a_1352_, v_b_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec(v_upperBound_1351_);
return v_res_1360_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1361_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__14));
v___x_1362_ = lean_unsigned_to_nat(11u);
v___x_1363_ = lean_unsigned_to_nat(158u);
v___x_1364_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__0));
v___x_1365_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1366_ = l_mkPanicMessageWithDecl(v___x_1365_, v___x_1364_, v___x_1363_, v___x_1362_, v___x_1361_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(lean_object* v_upperBound_1367_, lean_object* v_a_1368_, lean_object* v_b_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_a_1377_; uint8_t v___x_1381_; 
v___x_1381_ = lean_nat_dec_lt(v_a_1368_, v_upperBound_1367_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
lean_dec(v_a_1368_);
v___x_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1382_, 0, v_b_1369_);
return v___x_1382_;
}
else
{
lean_object* v_fst_1383_; 
v_fst_1383_ = lean_ctor_get(v_b_1369_, 0);
lean_inc(v_fst_1383_);
if (lean_obj_tag(v_fst_1383_) == 7)
{
lean_object* v_snd_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1417_; 
v_snd_1384_ = lean_ctor_get(v_b_1369_, 1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_b_1369_);
if (v_isSharedCheck_1417_ == 0)
{
lean_object* v_unused_1418_; 
v_unused_1418_ = lean_ctor_get(v_b_1369_, 0);
lean_dec(v_unused_1418_);
v___x_1386_ = v_b_1369_;
v_isShared_1387_ = v_isSharedCheck_1417_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_snd_1384_);
lean_dec(v_b_1369_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1417_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v_binderName_1388_; lean_object* v_binderType_1389_; lean_object* v_body_1390_; lean_object* v___x_1391_; 
v_binderName_1388_ = lean_ctor_get(v_fst_1383_, 0);
lean_inc(v_binderName_1388_);
v_binderType_1389_ = lean_ctor_get(v_fst_1383_, 1);
lean_inc_ref(v_binderType_1389_);
v_body_1390_ = lean_ctor_get(v_fst_1383_, 2);
lean_inc_ref(v_body_1390_);
lean_dec_ref_known(v_fst_1383_, 3);
v___x_1391_ = l_Lean_Compiler_LCNF_toMonoType(v_binderType_1389_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; uint8_t v___x_1393_; uint8_t v___x_1394_; lean_object* v___x_1395_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v___x_1393_ = 0;
v___x_1394_ = 0;
v___x_1395_ = l_Lean_Compiler_LCNF_mkParam(v___x_1393_, v_binderName_1388_, v_a_1392_, v___x_1394_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1397_; lean_object* v___x_1399_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1395_, 1);
v___x_1397_ = lean_array_push(v_snd_1384_, v_a_1396_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 1, v___x_1397_);
lean_ctor_set(v___x_1386_, 0, v_body_1390_);
v___x_1399_ = v___x_1386_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_body_1390_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
v_a_1377_ = v___x_1399_;
goto v___jp_1376_;
}
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
lean_dec_ref(v_body_1390_);
lean_del_object(v___x_1386_);
lean_dec(v_snd_1384_);
lean_dec(v_a_1368_);
v_a_1401_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1395_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1395_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_dec_ref(v_body_1390_);
lean_dec(v_binderName_1388_);
lean_del_object(v___x_1386_);
lean_dec(v_snd_1384_);
lean_dec(v_a_1368_);
v_a_1409_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1391_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1391_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
else
{
lean_object* v_snd_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1436_; 
v_snd_1419_ = lean_ctor_get(v_b_1369_, 1);
v_isSharedCheck_1436_ = !lean_is_exclusive(v_b_1369_);
if (v_isSharedCheck_1436_ == 0)
{
lean_object* v_unused_1437_; 
v_unused_1437_ = lean_ctor_get(v_b_1369_, 0);
lean_dec(v_unused_1437_);
v___x_1421_ = v_b_1369_;
v_isShared_1422_ = v_isSharedCheck_1436_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_snd_1419_);
lean_dec(v_b_1369_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1436_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0);
v___x_1424_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v___x_1423_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v___x_1426_; 
lean_dec_ref_known(v___x_1424_, 1);
if (v_isShared_1422_ == 0)
{
v___x_1426_ = v___x_1421_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_fst_1383_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_snd_1419_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
v_a_1377_ = v___x_1426_;
goto v___jp_1376_;
}
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_del_object(v___x_1421_);
lean_dec(v_snd_1419_);
lean_dec(v_fst_1383_);
lean_dec(v_a_1368_);
v_a_1428_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1424_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1424_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___boxed(lean_object* v_upperBound_1438_, lean_object* v_a_1439_, lean_object* v_b_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_upperBound_1438_, v_a_1439_, v_b_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec(v_upperBound_1438_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(lean_object* v_ctorType_1448_, lean_object* v_numParams_1449_, lean_object* v_numNewFields_1450_, lean_object* v_oldFields_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = lean_unsigned_to_nat(0u);
v___x_1459_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_numParams_1449_, v___x_1458_, v_ctorType_1448_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref_known(v___x_1459_, 1);
v___x_1461_ = lean_array_get_size(v_oldFields_1451_);
v___x_1462_ = lean_nat_add(v___x_1461_, v_numNewFields_1450_);
v___x_1463_ = lean_mk_empty_array_with_capacity(v___x_1462_);
lean_dec(v___x_1462_);
v___x_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1464_, 0, v_a_1460_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
v___x_1465_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_numNewFields_1450_, v___x_1458_, v___x_1464_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1475_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1475_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1475_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v_snd_1470_; lean_object* v___x_1471_; lean_object* v___x_1473_; 
v_snd_1470_ = lean_ctor_get(v_a_1466_, 1);
lean_inc(v_snd_1470_);
lean_dec(v_a_1466_);
v___x_1471_ = l_Array_append___redArg(v_snd_1470_, v_oldFields_1451_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1471_);
v___x_1473_ = v___x_1468_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
v_a_1476_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1465_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1465_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
v_a_1484_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1459_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1459_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields___boxed(lean_object* v_ctorType_1492_, lean_object* v_numParams_1493_, lean_object* v_numNewFields_1494_, lean_object* v_oldFields_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(v_ctorType_1492_, v_numParams_1493_, v_numNewFields_1494_, v_oldFields_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
lean_dec(v_a_1496_);
lean_dec_ref(v_oldFields_1495_);
lean_dec(v_numNewFields_1494_);
lean_dec(v_numParams_1493_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1(lean_object* v_upperBound_1503_, lean_object* v_inst_1504_, lean_object* v_R_1505_, lean_object* v_a_1506_, lean_object* v_b_1507_, lean_object* v_c_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_upperBound_1503_, v_a_1506_, v_b_1507_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___boxed(lean_object* v_upperBound_1516_, lean_object* v_inst_1517_, lean_object* v_R_1518_, lean_object* v_a_1519_, lean_object* v_b_1520_, lean_object* v_c_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1(v_upperBound_1516_, v_inst_1517_, v_R_1518_, v_a_1519_, v_b_1520_, v_c_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec(v_upperBound_1516_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2(lean_object* v_upperBound_1529_, lean_object* v_inst_1530_, lean_object* v_R_1531_, lean_object* v_a_1532_, lean_object* v_b_1533_, lean_object* v_c_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_upperBound_1529_, v_a_1532_, v_b_1533_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___boxed(lean_object* v_upperBound_1542_, lean_object* v_inst_1543_, lean_object* v_R_1544_, lean_object* v_a_1545_, lean_object* v_b_1546_, lean_object* v_c_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2(v_upperBound_1542_, v_inst_1543_, v_R_1544_, v_a_1545_, v_b_1546_, v_c_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec(v_upperBound_1542_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(size_t v_sz_1555_, size_t v_i_1556_, lean_object* v_bs_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
uint8_t v___x_1563_; 
v___x_1563_ = lean_usize_dec_lt(v_i_1556_, v_sz_1555_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v_bs_1557_);
return v___x_1564_;
}
else
{
lean_object* v_v_1565_; lean_object* v___x_1566_; 
v_v_1565_ = lean_array_uget_borrowed(v_bs_1557_, v_i_1556_);
lean_inc(v_v_1565_);
v___x_1566_ = l_Lean_Compiler_LCNF_Param_toMono___redArg(v_v_1565_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1568_; lean_object* v_bs_x27_1569_; size_t v___x_1570_; size_t v___x_1571_; lean_object* v___x_1572_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v___x_1566_, 1);
v___x_1568_ = lean_unsigned_to_nat(0u);
v_bs_x27_1569_ = lean_array_uset(v_bs_1557_, v_i_1556_, v___x_1568_);
v___x_1570_ = ((size_t)1ULL);
v___x_1571_ = lean_usize_add(v_i_1556_, v___x_1570_);
v___x_1572_ = lean_array_uset(v_bs_x27_1569_, v_i_1556_, v_a_1567_);
v_i_1556_ = v___x_1571_;
v_bs_1557_ = v___x_1572_;
goto _start;
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec_ref(v_bs_1557_);
v_a_1574_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1566_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1566_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg___boxed(lean_object* v_sz_1582_, lean_object* v_i_1583_, lean_object* v_bs_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
size_t v_sz_boxed_1590_; size_t v_i_boxed_1591_; lean_object* v_res_1592_; 
v_sz_boxed_1590_ = lean_unbox_usize(v_sz_1582_);
lean_dec(v_sz_1582_);
v_i_boxed_1591_ = lean_unbox_usize(v_i_1583_);
lean_dec(v_i_1583_);
v_res_1592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_boxed_1590_, v_i_boxed_1591_, v_bs_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec(v___y_1585_);
return v_res_1592_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0(void){
_start:
{
uint8_t v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = 0;
v___x_1594_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(lean_object* v_msg_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v_toApplicative_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1666_; 
v___x_1602_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1603_ = l_StateRefT_x27_instMonad___redArg(v___x_1602_);
v_toApplicative_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1666_ == 0)
{
lean_object* v_unused_1667_; 
v_unused_1667_ = lean_ctor_get(v___x_1603_, 1);
lean_dec(v_unused_1667_);
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1666_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_toApplicative_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1666_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v_toFunctor_1608_; lean_object* v_toSeq_1609_; lean_object* v_toSeqLeft_1610_; lean_object* v_toSeqRight_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1664_; 
v_toFunctor_1608_ = lean_ctor_get(v_toApplicative_1604_, 0);
v_toSeq_1609_ = lean_ctor_get(v_toApplicative_1604_, 2);
v_toSeqLeft_1610_ = lean_ctor_get(v_toApplicative_1604_, 3);
v_toSeqRight_1611_ = lean_ctor_get(v_toApplicative_1604_, 4);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_toApplicative_1604_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; 
v_unused_1665_ = lean_ctor_get(v_toApplicative_1604_, 1);
lean_dec(v_unused_1665_);
v___x_1613_ = v_toApplicative_1604_;
v_isShared_1614_ = v_isSharedCheck_1664_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_toSeqRight_1611_);
lean_inc(v_toSeqLeft_1610_);
lean_inc(v_toSeq_1609_);
lean_inc(v_toFunctor_1608_);
lean_dec(v_toApplicative_1604_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1664_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___f_1615_; lean_object* v___f_1616_; lean_object* v___f_1617_; lean_object* v___f_1618_; lean_object* v___x_1619_; lean_object* v___f_1620_; lean_object* v___f_1621_; lean_object* v___f_1622_; lean_object* v___x_1624_; 
v___f_1615_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1616_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1608_);
v___f_1617_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1617_, 0, v_toFunctor_1608_);
v___f_1618_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1618_, 0, v_toFunctor_1608_);
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___f_1617_);
lean_ctor_set(v___x_1619_, 1, v___f_1618_);
v___f_1620_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1620_, 0, v_toSeqRight_1611_);
v___f_1621_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1621_, 0, v_toSeqLeft_1610_);
v___f_1622_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1622_, 0, v_toSeq_1609_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 4, v___f_1620_);
lean_ctor_set(v___x_1613_, 3, v___f_1621_);
lean_ctor_set(v___x_1613_, 2, v___f_1622_);
lean_ctor_set(v___x_1613_, 1, v___f_1615_);
lean_ctor_set(v___x_1613_, 0, v___x_1619_);
v___x_1624_ = v___x_1613_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1619_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v___f_1615_);
lean_ctor_set(v_reuseFailAlloc_1663_, 2, v___f_1622_);
lean_ctor_set(v_reuseFailAlloc_1663_, 3, v___f_1621_);
lean_ctor_set(v_reuseFailAlloc_1663_, 4, v___f_1620_);
v___x_1624_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
lean_object* v___x_1626_; 
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 1, v___f_1616_);
lean_ctor_set(v___x_1606_, 0, v___x_1624_);
v___x_1626_ = v___x_1606_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v___f_1616_);
v___x_1626_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
lean_object* v___x_1627_; lean_object* v_toApplicative_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1660_; 
v___x_1627_ = l_StateRefT_x27_instMonad___redArg(v___x_1626_);
v_toApplicative_1628_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; 
v_unused_1661_ = lean_ctor_get(v___x_1627_, 1);
lean_dec(v_unused_1661_);
v___x_1630_ = v___x_1627_;
v_isShared_1631_ = v_isSharedCheck_1660_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_toApplicative_1628_);
lean_dec(v___x_1627_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1660_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v_toFunctor_1632_; lean_object* v_toSeq_1633_; lean_object* v_toSeqLeft_1634_; lean_object* v_toSeqRight_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1658_; 
v_toFunctor_1632_ = lean_ctor_get(v_toApplicative_1628_, 0);
v_toSeq_1633_ = lean_ctor_get(v_toApplicative_1628_, 2);
v_toSeqLeft_1634_ = lean_ctor_get(v_toApplicative_1628_, 3);
v_toSeqRight_1635_ = lean_ctor_get(v_toApplicative_1628_, 4);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_toApplicative_1628_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; 
v_unused_1659_ = lean_ctor_get(v_toApplicative_1628_, 1);
lean_dec(v_unused_1659_);
v___x_1637_ = v_toApplicative_1628_;
v_isShared_1638_ = v_isSharedCheck_1658_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_toSeqRight_1635_);
lean_inc(v_toSeqLeft_1634_);
lean_inc(v_toSeq_1633_);
lean_inc(v_toFunctor_1632_);
lean_dec(v_toApplicative_1628_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1658_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___f_1639_; lean_object* v___f_1640_; lean_object* v___f_1641_; lean_object* v___f_1642_; lean_object* v___x_1643_; lean_object* v___f_1644_; lean_object* v___f_1645_; lean_object* v___f_1646_; lean_object* v___x_1648_; 
v___f_1639_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1640_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1632_);
v___f_1641_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1641_, 0, v_toFunctor_1632_);
v___f_1642_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1642_, 0, v_toFunctor_1632_);
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___f_1641_);
lean_ctor_set(v___x_1643_, 1, v___f_1642_);
v___f_1644_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1644_, 0, v_toSeqRight_1635_);
v___f_1645_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1645_, 0, v_toSeqLeft_1634_);
v___f_1646_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1646_, 0, v_toSeq_1633_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 4, v___f_1644_);
lean_ctor_set(v___x_1637_, 3, v___f_1645_);
lean_ctor_set(v___x_1637_, 2, v___f_1646_);
lean_ctor_set(v___x_1637_, 1, v___f_1639_);
lean_ctor_set(v___x_1637_, 0, v___x_1643_);
v___x_1648_ = v___x_1637_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v___f_1639_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v___f_1646_);
lean_ctor_set(v_reuseFailAlloc_1657_, 3, v___f_1645_);
lean_ctor_set(v_reuseFailAlloc_1657_, 4, v___f_1644_);
v___x_1648_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
lean_object* v___x_1650_; 
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 1, v___f_1640_);
lean_ctor_set(v___x_1630_, 0, v___x_1648_);
v___x_1650_ = v___x_1630_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v___f_1640_);
v___x_1650_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_30686__overap_1654_; lean_object* v___x_1655_; 
v___x_1651_ = l_StateRefT_x27_instMonad___redArg(v___x_1650_);
v___x_1652_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0);
v___x_1653_ = l_instInhabitedOfMonad___redArg(v___x_1651_, v___x_1652_);
v___x_30686__overap_1654_ = lean_panic_fn_borrowed(v___x_1653_, v_msg_1595_);
lean_dec(v___x_1653_);
lean_inc(v___y_1600_);
lean_inc_ref(v___y_1599_);
lean_inc(v___y_1598_);
lean_inc_ref(v___y_1597_);
lean_inc(v___y_1596_);
v___x_1655_ = lean_apply_6(v___x_30686__overap_1654_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, lean_box(0));
return v___x_1655_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___boxed(lean_object* v_msg_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v_msg_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__2(lean_object* v_msg_1676_){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0);
v___x_1678_ = lean_panic_fn_borrowed(v___x_1677_, v_msg_1676_);
return v___x_1678_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0(void){
_start:
{
uint8_t v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = 0;
v___x_1680_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(lean_object* v_msg_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v_toApplicative_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1752_; 
v___x_1688_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1689_ = l_StateRefT_x27_instMonad___redArg(v___x_1688_);
v_toApplicative_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1752_ == 0)
{
lean_object* v_unused_1753_; 
v_unused_1753_ = lean_ctor_get(v___x_1689_, 1);
lean_dec(v_unused_1753_);
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1752_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_toApplicative_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1752_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v_toFunctor_1694_; lean_object* v_toSeq_1695_; lean_object* v_toSeqLeft_1696_; lean_object* v_toSeqRight_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1750_; 
v_toFunctor_1694_ = lean_ctor_get(v_toApplicative_1690_, 0);
v_toSeq_1695_ = lean_ctor_get(v_toApplicative_1690_, 2);
v_toSeqLeft_1696_ = lean_ctor_get(v_toApplicative_1690_, 3);
v_toSeqRight_1697_ = lean_ctor_get(v_toApplicative_1690_, 4);
v_isSharedCheck_1750_ = !lean_is_exclusive(v_toApplicative_1690_);
if (v_isSharedCheck_1750_ == 0)
{
lean_object* v_unused_1751_; 
v_unused_1751_ = lean_ctor_get(v_toApplicative_1690_, 1);
lean_dec(v_unused_1751_);
v___x_1699_ = v_toApplicative_1690_;
v_isShared_1700_ = v_isSharedCheck_1750_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_toSeqRight_1697_);
lean_inc(v_toSeqLeft_1696_);
lean_inc(v_toSeq_1695_);
lean_inc(v_toFunctor_1694_);
lean_dec(v_toApplicative_1690_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1750_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___f_1701_; lean_object* v___f_1702_; lean_object* v___f_1703_; lean_object* v___f_1704_; lean_object* v___x_1705_; lean_object* v___f_1706_; lean_object* v___f_1707_; lean_object* v___f_1708_; lean_object* v___x_1710_; 
v___f_1701_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1702_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1694_);
v___f_1703_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1703_, 0, v_toFunctor_1694_);
v___f_1704_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1704_, 0, v_toFunctor_1694_);
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___f_1703_);
lean_ctor_set(v___x_1705_, 1, v___f_1704_);
v___f_1706_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1706_, 0, v_toSeqRight_1697_);
v___f_1707_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1707_, 0, v_toSeqLeft_1696_);
v___f_1708_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1708_, 0, v_toSeq_1695_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 4, v___f_1706_);
lean_ctor_set(v___x_1699_, 3, v___f_1707_);
lean_ctor_set(v___x_1699_, 2, v___f_1708_);
lean_ctor_set(v___x_1699_, 1, v___f_1701_);
lean_ctor_set(v___x_1699_, 0, v___x_1705_);
v___x_1710_ = v___x_1699_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1705_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v___f_1701_);
lean_ctor_set(v_reuseFailAlloc_1749_, 2, v___f_1708_);
lean_ctor_set(v_reuseFailAlloc_1749_, 3, v___f_1707_);
lean_ctor_set(v_reuseFailAlloc_1749_, 4, v___f_1706_);
v___x_1710_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
lean_object* v___x_1712_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 1, v___f_1702_);
lean_ctor_set(v___x_1692_, 0, v___x_1710_);
v___x_1712_ = v___x_1692_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v___f_1702_);
v___x_1712_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1713_; lean_object* v_toApplicative_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1746_; 
v___x_1713_ = l_StateRefT_x27_instMonad___redArg(v___x_1712_);
v_toApplicative_1714_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1746_ == 0)
{
lean_object* v_unused_1747_; 
v_unused_1747_ = lean_ctor_get(v___x_1713_, 1);
lean_dec(v_unused_1747_);
v___x_1716_ = v___x_1713_;
v_isShared_1717_ = v_isSharedCheck_1746_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_toApplicative_1714_);
lean_dec(v___x_1713_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1746_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v_toFunctor_1718_; lean_object* v_toSeq_1719_; lean_object* v_toSeqLeft_1720_; lean_object* v_toSeqRight_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1744_; 
v_toFunctor_1718_ = lean_ctor_get(v_toApplicative_1714_, 0);
v_toSeq_1719_ = lean_ctor_get(v_toApplicative_1714_, 2);
v_toSeqLeft_1720_ = lean_ctor_get(v_toApplicative_1714_, 3);
v_toSeqRight_1721_ = lean_ctor_get(v_toApplicative_1714_, 4);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_toApplicative_1714_);
if (v_isSharedCheck_1744_ == 0)
{
lean_object* v_unused_1745_; 
v_unused_1745_ = lean_ctor_get(v_toApplicative_1714_, 1);
lean_dec(v_unused_1745_);
v___x_1723_ = v_toApplicative_1714_;
v_isShared_1724_ = v_isSharedCheck_1744_;
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
v_isShared_1724_ = v_isSharedCheck_1744_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___f_1725_; lean_object* v___f_1726_; lean_object* v___f_1727_; lean_object* v___f_1728_; lean_object* v___x_1729_; lean_object* v___f_1730_; lean_object* v___f_1731_; lean_object* v___f_1732_; lean_object* v___x_1734_; 
v___f_1725_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1726_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
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
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v___f_1725_);
lean_ctor_set(v_reuseFailAlloc_1743_, 2, v___f_1732_);
lean_ctor_set(v_reuseFailAlloc_1743_, 3, v___f_1731_);
lean_ctor_set(v_reuseFailAlloc_1743_, 4, v___f_1730_);
v___x_1734_ = v_reuseFailAlloc_1743_;
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
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v___f_1726_);
v___x_1736_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_30701__overap_1740_; lean_object* v___x_1741_; 
v___x_1737_ = l_StateRefT_x27_instMonad___redArg(v___x_1736_);
v___x_1738_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_1739_ = l_instInhabitedOfMonad___redArg(v___x_1737_, v___x_1738_);
v___x_30701__overap_1740_ = lean_panic_fn_borrowed(v___x_1739_, v_msg_1681_);
lean_dec(v___x_1739_);
lean_inc(v___y_1686_);
lean_inc_ref(v___y_1685_);
lean_inc(v___y_1684_);
lean_inc_ref(v___y_1683_);
lean_inc(v___y_1682_);
v___x_1741_ = lean_apply_6(v___x_30701__overap_1740_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, lean_box(0));
return v___x_1741_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___boxed(lean_object* v_msg_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(v_msg_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
return v_res_1761_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__2(void){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1764_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__14));
v___x_1765_ = lean_unsigned_to_nat(9u);
v___x_1766_ = lean_unsigned_to_nat(641u);
v___x_1767_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__1));
v___x_1768_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__0));
v___x_1769_ = l_mkPanicMessageWithDecl(v___x_1768_, v___x_1767_, v___x_1766_, v___x_1765_, v___x_1764_);
return v___x_1769_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__4(void){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1772_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__3));
v___x_1773_ = lean_unsigned_to_nat(66u);
v___x_1774_ = lean_unsigned_to_nat(389u);
v___x_1775_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_1776_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1777_ = l_mkPanicMessageWithDecl(v___x_1776_, v___x_1775_, v___x_1774_, v___x_1773_, v___x_1772_);
return v___x_1777_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__5(void){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1778_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__14));
v___x_1779_ = lean_unsigned_to_nat(27u);
v___x_1780_ = lean_unsigned_to_nat(345u);
v___x_1781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_1782_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1783_ = l_mkPanicMessageWithDecl(v___x_1782_, v___x_1781_, v___x_1780_, v___x_1779_, v___x_1778_);
return v___x_1783_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__1(void){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1838_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_1839_ = lean_unsigned_to_nat(2u);
v___x_1840_ = lean_unsigned_to_nat(328u);
v___x_1841_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1842_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1843_ = l_mkPanicMessageWithDecl(v___x_1842_, v___x_1841_, v___x_1840_, v___x_1839_, v___x_1838_);
return v___x_1843_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__3(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1845_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__2));
v___x_1846_ = lean_unsigned_to_nat(2u);
v___x_1847_ = lean_unsigned_to_nat(330u);
v___x_1848_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1849_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1850_ = l_mkPanicMessageWithDecl(v___x_1849_, v___x_1848_, v___x_1847_, v___x_1846_, v___x_1845_);
return v___x_1850_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__5(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1852_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__4));
v___x_1853_ = lean_unsigned_to_nat(2u);
v___x_1854_ = lean_unsigned_to_nat(331u);
v___x_1855_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1856_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1857_ = l_mkPanicMessageWithDecl(v___x_1856_, v___x_1855_, v___x_1854_, v___x_1853_, v___x_1852_);
return v___x_1857_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__6(void){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1858_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__14));
v___x_1859_ = lean_unsigned_to_nat(41u);
v___x_1860_ = lean_unsigned_to_nat(329u);
v___x_1861_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1862_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1863_ = l_mkPanicMessageWithDecl(v___x_1862_, v___x_1861_, v___x_1860_, v___x_1859_, v___x_1858_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono(lean_object* v_info_1864_, lean_object* v_c_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v_discr_1872_; lean_object* v_alts_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1951_; 
v_discr_1872_ = lean_ctor_get(v_c_1865_, 2);
v_alts_1873_ = lean_ctor_get(v_c_1865_, 3);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_c_1865_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; lean_object* v_unused_1953_; 
v_unused_1952_ = lean_ctor_get(v_c_1865_, 1);
lean_dec(v_unused_1952_);
v_unused_1953_ = lean_ctor_get(v_c_1865_, 0);
lean_dec(v_unused_1953_);
v___x_1875_ = v_c_1865_;
v_isShared_1876_ = v_isSharedCheck_1951_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_alts_1873_);
lean_inc(v_discr_1872_);
lean_dec(v_c_1865_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1951_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; uint8_t v___x_1879_; 
v___x_1877_ = lean_array_get_size(v_alts_1873_);
v___x_1878_ = lean_unsigned_to_nat(1u);
v___x_1879_ = lean_nat_dec_eq(v___x_1877_, v___x_1878_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
lean_del_object(v___x_1875_);
lean_dec_ref(v_alts_1873_);
lean_dec(v_discr_1872_);
v___x_1880_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__1, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__1_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__1);
v___x_1881_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1880_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_);
return v___x_1881_;
}
else
{
uint8_t v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1882_ = 0;
v___x_1883_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_1884_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_1885_ = lean_unsigned_to_nat(0u);
v___x_1886_ = lean_array_get(v___x_1884_, v_alts_1873_, v___x_1885_);
lean_dec_ref(v_alts_1873_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_ctorName_1887_; lean_object* v_params_1888_; lean_object* v_code_1889_; lean_object* v_ctorName_1890_; lean_object* v_fieldIdx_1891_; uint8_t v___x_1892_; 
v_ctorName_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_ctorName_1887_);
v_params_1888_ = lean_ctor_get(v___x_1886_, 1);
lean_inc_ref(v_params_1888_);
v_code_1889_ = lean_ctor_get(v___x_1886_, 2);
lean_inc_ref(v_code_1889_);
lean_dec_ref_known(v___x_1886_, 3);
v_ctorName_1890_ = lean_ctor_get(v_info_1864_, 0);
v_fieldIdx_1891_ = lean_ctor_get(v_info_1864_, 2);
v___x_1892_ = lean_name_eq(v_ctorName_1887_, v_ctorName_1890_);
lean_dec(v_ctorName_1887_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
lean_dec_ref(v_code_1889_);
lean_dec_ref(v_params_1888_);
lean_del_object(v___x_1875_);
lean_dec(v_discr_1872_);
v___x_1893_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__3, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__3_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__3);
v___x_1894_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1893_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_);
return v___x_1894_;
}
else
{
lean_object* v___x_1895_; uint8_t v___x_1896_; 
v___x_1895_ = lean_array_get_size(v_params_1888_);
v___x_1896_ = lean_nat_dec_lt(v_fieldIdx_1891_, v___x_1895_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
lean_dec_ref(v_code_1889_);
lean_dec_ref(v_params_1888_);
lean_del_object(v___x_1875_);
lean_dec(v_discr_1872_);
v___x_1897_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__5, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__5_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__5);
v___x_1898_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1897_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_);
return v___x_1898_;
}
else
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1882_, v_params_1888_, v_a_1868_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_p_1900_; lean_object* v_fvarId_1901_; lean_object* v_binderName_1902_; lean_object* v_type_1903_; lean_object* v___x_1904_; 
lean_dec_ref_known(v___x_1899_, 1);
v_p_1900_ = lean_array_get(v___x_1883_, v_params_1888_, v_fieldIdx_1891_);
lean_dec_ref(v_params_1888_);
v_fvarId_1901_ = lean_ctor_get(v_p_1900_, 0);
lean_inc(v_fvarId_1901_);
v_binderName_1902_ = lean_ctor_get(v_p_1900_, 1);
lean_inc(v_binderName_1902_);
v_type_1903_ = lean_ctor_get(v_p_1900_, 2);
lean_inc_ref(v_type_1903_);
lean_dec(v_p_1900_);
v___x_1904_ = l_Lean_Compiler_LCNF_toMonoType(v_type_1903_, v_a_1869_, v_a_1870_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1906_; lean_object* v_lctx_1907_; lean_object* v_nextIdx_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1932_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
v___x_1906_ = lean_st_ref_take(v_a_1868_);
v_lctx_1907_ = lean_ctor_get(v___x_1906_, 0);
v_nextIdx_1908_ = lean_ctor_get(v___x_1906_, 1);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1910_ = v___x_1906_;
v_isShared_1911_ = v_isSharedCheck_1932_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_nextIdx_1908_);
lean_inc(v_lctx_1907_);
lean_dec(v___x_1906_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1932_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1915_; 
v___x_1912_ = ((lean_object*)(l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0));
v___x_1913_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1913_, 0, v_discr_1872_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 3, v___x_1913_);
lean_ctor_set(v___x_1875_, 2, v_a_1905_);
lean_ctor_set(v___x_1875_, 1, v_binderName_1902_);
lean_ctor_set(v___x_1875_, 0, v_fvarId_1901_);
v___x_1915_ = v___x_1875_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_fvarId_1901_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_binderName_1902_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_a_1905_);
lean_ctor_set(v_reuseFailAlloc_1931_, 3, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1916_; lean_object* v___x_1918_; 
lean_inc_ref(v___x_1915_);
v___x_1916_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1882_, v_lctx_1907_, v___x_1915_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v___x_1916_);
v___x_1918_ = v___x_1910_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_nextIdx_1908_);
v___x_1918_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = lean_st_ref_put(v_a_1868_, v___x_1918_);
v___x_1920_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1889_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1929_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_1929_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1929_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1915_);
lean_ctor_set(v___x_1925_, 1, v_a_1921_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1925_);
v___x_1927_ = v___x_1923_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
else
{
lean_dec_ref(v___x_1915_);
return v___x_1920_;
}
}
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v_binderName_1902_);
lean_dec(v_fvarId_1901_);
lean_dec_ref(v_code_1889_);
lean_del_object(v___x_1875_);
lean_dec(v_discr_1872_);
v_a_1933_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1904_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1904_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec_ref(v_code_1889_);
lean_dec_ref(v_params_1888_);
lean_del_object(v___x_1875_);
lean_dec(v_discr_1872_);
v_a_1941_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1899_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1899_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
}
else
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
lean_dec(v___x_1886_);
lean_del_object(v___x_1875_);
lean_dec(v_discr_1872_);
v___x_1949_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__6, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__6_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__6);
v___x_1950_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1949_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_);
return v___x_1950_;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1955_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__1));
v___x_1956_ = lean_unsigned_to_nat(70u);
v___x_1957_ = lean_unsigned_to_nat(399u);
v___x_1958_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_1959_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1960_ = l_mkPanicMessageWithDecl(v___x_1959_, v___x_1958_, v___x_1957_, v___x_1956_, v___x_1955_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(lean_object* v___x_1964_, uint8_t v___x_1965_, size_t v_sz_1966_, size_t v_i_1967_, lean_object* v_bs_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
uint8_t v___x_1975_; 
v___x_1975_ = lean_usize_dec_lt(v_i_1967_, v_sz_1966_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; 
lean_dec_ref(v___x_1964_);
v___x_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1976_, 0, v_bs_1968_);
return v___x_1976_;
}
else
{
lean_object* v_v_1977_; lean_object* v___x_1978_; lean_object* v_bs_x27_1979_; lean_object* v_a_1981_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; 
v_v_1977_ = lean_array_uget(v_bs_1968_, v_i_1967_);
v___x_1978_ = lean_unsigned_to_nat(0u);
v_bs_x27_1979_ = lean_array_uset(v_bs_1968_, v_i_1967_, v___x_1978_);
if (lean_obj_tag(v_v_1977_) == 0)
{
lean_object* v_ctorName_2003_; lean_object* v_params_2004_; lean_object* v_code_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2043_; 
v_ctorName_2003_ = lean_ctor_get(v_v_1977_, 0);
v_params_2004_ = lean_ctor_get(v_v_1977_, 1);
v_code_2005_ = lean_ctor_get(v_v_1977_, 2);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_v_1977_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2007_ = v_v_1977_;
v_isShared_2008_ = v_isSharedCheck_2043_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_code_2005_);
lean_inc(v_params_2004_);
lean_inc(v_ctorName_2003_);
lean_dec(v_v_1977_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2043_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4));
v___x_2010_ = l_Lean_Name_append(v_ctorName_2003_, v___x_2009_);
lean_inc(v___x_2010_);
lean_inc_ref(v___x_1964_);
v___x_2011_ = l_Lean_Environment_find_x3f(v___x_1964_, v___x_2010_, v___x_1965_);
if (lean_obj_tag(v___x_2011_) == 1)
{
lean_object* v_val_2012_; 
v_val_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_val_2012_);
lean_dec_ref_known(v___x_2011_, 1);
if (lean_obj_tag(v_val_2012_) == 6)
{
lean_object* v_val_2013_; lean_object* v_toConstantVal_2014_; lean_object* v_numParams_2015_; lean_object* v_numFields_2016_; lean_object* v_type_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v_val_2013_ = lean_ctor_get(v_val_2012_, 0);
lean_inc_ref(v_val_2013_);
lean_dec_ref_known(v_val_2012_, 1);
v_toConstantVal_2014_ = lean_ctor_get(v_val_2013_, 0);
lean_inc_ref(v_toConstantVal_2014_);
v_numParams_2015_ = lean_ctor_get(v_val_2013_, 3);
lean_inc(v_numParams_2015_);
v_numFields_2016_ = lean_ctor_get(v_val_2013_, 4);
lean_inc(v_numFields_2016_);
lean_dec_ref(v_val_2013_);
v_type_2017_ = lean_ctor_get(v_toConstantVal_2014_, 2);
lean_inc_ref(v_type_2017_);
lean_dec_ref(v_toConstantVal_2014_);
v___x_2018_ = lean_array_get_size(v_params_2004_);
v___x_2019_ = lean_nat_sub(v_numFields_2016_, v___x_2018_);
lean_dec(v_numFields_2016_);
v___x_2020_ = l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(v_type_2017_, v_numParams_2015_, v___x_2019_, v_params_2004_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec_ref(v_params_2004_);
lean_dec(v___x_2019_);
lean_dec(v_numParams_2015_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2022_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v___x_2020_, 1);
v___x_2022_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2005_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2025_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 2, v_a_2023_);
lean_ctor_set(v___x_2007_, 1, v_a_2021_);
lean_ctor_set(v___x_2007_, 0, v___x_2010_);
v___x_2025_ = v___x_2007_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_a_2021_);
lean_ctor_set(v_reuseFailAlloc_2026_, 2, v_a_2023_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
v_a_1981_ = v___x_2025_;
goto v___jp_1980_;
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec(v_a_2021_);
lean_dec(v___x_2010_);
lean_del_object(v___x_2007_);
lean_dec_ref(v_bs_x27_1979_);
lean_dec_ref(v___x_1964_);
v_a_2027_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2022_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2022_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec(v___x_2010_);
lean_del_object(v___x_2007_);
lean_dec_ref(v_code_2005_);
lean_dec_ref(v_bs_x27_1979_);
lean_dec_ref(v___x_1964_);
v_a_2035_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2020_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2020_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
else
{
lean_dec(v_val_2012_);
lean_dec(v___x_2010_);
lean_del_object(v___x_2007_);
lean_dec_ref(v_code_2005_);
lean_dec_ref(v_params_2004_);
v___y_1987_ = v___y_1969_;
v___y_1988_ = v___y_1970_;
v___y_1989_ = v___y_1971_;
v___y_1990_ = v___y_1972_;
v___y_1991_ = v___y_1973_;
goto v___jp_1986_;
}
}
else
{
lean_dec(v___x_2011_);
lean_dec(v___x_2010_);
lean_del_object(v___x_2007_);
lean_dec_ref(v_code_2005_);
lean_dec_ref(v_params_2004_);
v___y_1987_ = v___y_1969_;
v___y_1988_ = v___y_1970_;
v___y_1989_ = v___y_1971_;
v___y_1990_ = v___y_1972_;
v___y_1991_ = v___y_1973_;
goto v___jp_1986_;
}
}
}
else
{
lean_object* v_code_2044_; lean_object* v___x_2045_; 
v_code_2044_ = lean_ctor_get(v_v_1977_, 0);
lean_inc_ref(v_code_2044_);
v___x_2045_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2044_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2047_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___x_2045_, 1);
v___x_2047_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_1977_, v_a_2046_);
v_a_1981_ = v___x_2047_;
goto v___jp_1980_;
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec_ref_known(v_v_1977_, 1);
lean_dec_ref(v_bs_x27_1979_);
lean_dec_ref(v___x_1964_);
v_a_2048_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2045_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2045_);
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
v___jp_1980_:
{
size_t v___x_1982_; size_t v___x_1983_; lean_object* v___x_1984_; 
v___x_1982_ = ((size_t)1ULL);
v___x_1983_ = lean_usize_add(v_i_1967_, v___x_1982_);
v___x_1984_ = lean_array_uset(v_bs_x27_1979_, v_i_1967_, v_a_1981_);
v_i_1967_ = v___x_1983_;
v_bs_1968_ = v___x_1984_;
goto _start;
}
v___jp_1986_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2);
v___x_1993_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(v___x_1992_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1993_, 1);
v_a_1981_ = v_a_1994_;
goto v___jp_1980_;
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec_ref(v_bs_x27_1979_);
lean_dec_ref(v___x_1964_);
v_a_1995_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1993_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1993_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(size_t v_sz_2056_, size_t v_i_2057_, lean_object* v_bs_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
uint8_t v___x_2065_; 
v___x_2065_ = lean_usize_dec_lt(v_i_2057_, v_sz_2056_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2066_; 
v___x_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2066_, 0, v_bs_2058_);
return v___x_2066_;
}
else
{
lean_object* v_v_2067_; lean_object* v___x_2068_; lean_object* v_bs_x27_2069_; lean_object* v_a_2071_; 
v_v_2067_ = lean_array_uget(v_bs_2058_, v_i_2057_);
v___x_2068_ = lean_unsigned_to_nat(0u);
v_bs_x27_2069_ = lean_array_uset(v_bs_2058_, v_i_2057_, v___x_2068_);
if (lean_obj_tag(v_v_2067_) == 0)
{
lean_object* v_params_2076_; lean_object* v_code_2077_; size_t v_sz_2078_; size_t v___x_2079_; lean_object* v___x_2080_; 
v_params_2076_ = lean_ctor_get(v_v_2067_, 1);
v_code_2077_ = lean_ctor_get(v_v_2067_, 2);
v_sz_2078_ = lean_array_size(v_params_2076_);
v___x_2079_ = ((size_t)0ULL);
lean_inc_ref(v_params_2076_);
v___x_2080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_2078_, v___x_2079_, v_params_2076_, v___y_2059_, v___y_2061_, v___y_2062_, v___y_2063_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v___x_2082_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_a_2081_);
lean_dec_ref_known(v___x_2080_, 1);
lean_inc_ref(v_code_2077_);
v___x_2082_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2077_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; uint8_t v___x_2084_; lean_object* v___x_2085_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2082_, 1);
v___x_2084_ = 0;
v___x_2085_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v___x_2084_, v_v_2067_, v_a_2081_, v_a_2083_);
v_a_2071_ = v___x_2085_;
goto v___jp_2070_;
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec(v_a_2081_);
lean_dec_ref_known(v_v_2067_, 3);
lean_dec_ref(v_bs_x27_2069_);
v_a_2086_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2082_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2082_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
else
{
lean_dec_ref_known(v_v_2067_, 3);
lean_dec_ref(v_bs_x27_2069_);
return v___x_2080_;
}
}
else
{
lean_object* v_code_2094_; lean_object* v___x_2095_; 
v_code_2094_ = lean_ctor_get(v_v_2067_, 0);
lean_inc_ref(v_code_2094_);
v___x_2095_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2094_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2097_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v___x_2097_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_2067_, v_a_2096_);
v_a_2071_ = v___x_2097_;
goto v___jp_2070_;
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec_ref_known(v_v_2067_, 1);
lean_dec_ref(v_bs_x27_2069_);
v_a_2098_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2095_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2095_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
v___jp_2070_:
{
size_t v___x_2072_; size_t v___x_2073_; lean_object* v___x_2074_; 
v___x_2072_ = ((size_t)1ULL);
v___x_2073_ = lean_usize_add(v_i_2057_, v___x_2072_);
v___x_2074_ = lean_array_uset(v_bs_x27_2069_, v_i_2057_, v_a_2071_);
v_i_2057_ = v___x_2073_;
v_bs_2058_ = v___x_2074_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2107_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2108_ = lean_unsigned_to_nat(2u);
v___x_2109_ = lean_unsigned_to_nat(317u);
v___x_2110_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0));
v___x_2111_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2112_ = l_mkPanicMessageWithDecl(v___x_2111_, v___x_2110_, v___x_2109_, v___x_2108_, v___x_2107_);
return v___x_2112_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2117_ = lean_box(0);
v___x_2118_ = lean_unsigned_to_nat(2u);
v___x_2119_ = lean_mk_empty_array_with_capacity(v___x_2118_);
v___x_2120_ = lean_array_push(v___x_2119_, v___x_2117_);
return v___x_2120_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2121_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__14));
v___x_2122_ = lean_unsigned_to_nat(34u);
v___x_2123_ = lean_unsigned_to_nat(318u);
v___x_2124_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0));
v___x_2125_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2126_ = l_mkPanicMessageWithDecl(v___x_2125_, v___x_2124_, v___x_2123_, v___x_2122_, v___x_2121_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg(lean_object* v_c_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v_discr_2134_; lean_object* v_alts_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2204_; 
v_discr_2134_ = lean_ctor_get(v_c_2127_, 2);
v_alts_2135_ = lean_ctor_get(v_c_2127_, 3);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_c_2127_);
if (v_isSharedCheck_2204_ == 0)
{
lean_object* v_unused_2205_; lean_object* v_unused_2206_; 
v_unused_2205_ = lean_ctor_get(v_c_2127_, 1);
lean_dec(v_unused_2205_);
v_unused_2206_ = lean_ctor_get(v_c_2127_, 0);
lean_dec(v_unused_2206_);
v___x_2137_ = v_c_2127_;
v_isShared_2138_ = v_isSharedCheck_2204_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_alts_2135_);
lean_inc(v_discr_2134_);
lean_dec(v_c_2127_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2204_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2139_ = lean_array_get_size(v_alts_2135_);
v___x_2140_ = lean_unsigned_to_nat(1u);
v___x_2141_ = lean_nat_dec_eq(v___x_2139_, v___x_2140_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_del_object(v___x_2137_);
lean_dec_ref(v_alts_2135_);
lean_dec(v_discr_2134_);
v___x_2142_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1);
v___x_2143_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2142_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
return v___x_2143_;
}
else
{
uint8_t v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2144_ = 0;
v___x_2145_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2146_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2147_ = lean_unsigned_to_nat(0u);
v___x_2148_ = lean_array_get(v___x_2146_, v_alts_2135_, v___x_2147_);
lean_dec_ref(v_alts_2135_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_params_2149_; lean_object* v_code_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2200_; 
v_params_2149_ = lean_ctor_get(v___x_2148_, 1);
v_code_2150_ = lean_ctor_get(v___x_2148_, 2);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2200_ == 0)
{
lean_object* v_unused_2201_; 
v_unused_2201_ = lean_ctor_get(v___x_2148_, 0);
lean_dec(v_unused_2201_);
v___x_2152_ = v___x_2148_;
v_isShared_2153_ = v_isSharedCheck_2200_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_code_2150_);
lean_inc(v_params_2149_);
lean_dec(v___x_2148_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2200_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2144_, v_params_2149_, v_a_2130_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v_fvarId_2157_; lean_object* v_binderName_2158_; lean_object* v_lctx_2159_; lean_object* v_nextIdx_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2191_; 
lean_dec_ref_known(v___x_2154_, 1);
v___x_2155_ = lean_st_ref_take(v_a_2130_);
v___x_2156_ = lean_array_get(v___x_2145_, v_params_2149_, v___x_2147_);
lean_dec_ref(v_params_2149_);
v_fvarId_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_fvarId_2157_);
v_binderName_2158_ = lean_ctor_get(v___x_2156_, 1);
lean_inc(v_binderName_2158_);
lean_dec(v___x_2156_);
v_lctx_2159_ = lean_ctor_get(v___x_2155_, 0);
v_nextIdx_2160_ = lean_ctor_get(v___x_2155_, 1);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2162_ = v___x_2155_;
v_isShared_2163_ = v_isSharedCheck_2191_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_nextIdx_2160_);
lean_inc(v_lctx_2159_);
lean_dec(v___x_2155_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2191_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2164_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__4));
v___x_2165_ = lean_box(0);
v___x_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2166_, 0, v_discr_2134_);
v___x_2167_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_2168_ = lean_array_push(v___x_2167_, v___x_2166_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set_tag(v___x_2152_, 3);
lean_ctor_set(v___x_2152_, 2, v___x_2168_);
lean_ctor_set(v___x_2152_, 1, v___x_2165_);
lean_ctor_set(v___x_2152_, 0, v___x_2164_);
v___x_2170_ = v___x_2152_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v___x_2165_);
lean_ctor_set(v_reuseFailAlloc_2190_, 2, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2171_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 3, v___x_2170_);
lean_ctor_set(v___x_2137_, 2, v___x_2171_);
lean_ctor_set(v___x_2137_, 1, v_binderName_2158_);
lean_ctor_set(v___x_2137_, 0, v_fvarId_2157_);
v___x_2173_ = v___x_2137_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_fvarId_2157_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_binderName_2158_);
lean_ctor_set(v_reuseFailAlloc_2189_, 2, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2189_, 3, v___x_2170_);
v___x_2173_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2174_; lean_object* v___x_2176_; 
lean_inc_ref(v___x_2173_);
v___x_2174_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2144_, v_lctx_2159_, v___x_2173_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v___x_2174_);
v___x_2176_ = v___x_2162_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2174_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_nextIdx_2160_);
v___x_2176_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = lean_st_ref_put(v_a_2130_, v___x_2176_);
v___x_2178_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2150_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2187_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2187_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2178_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2187_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2173_);
lean_ctor_set(v___x_2183_, 1, v_a_2179_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2183_);
v___x_2185_ = v___x_2181_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
else
{
lean_dec_ref(v___x_2173_);
return v___x_2178_;
}
}
}
}
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_del_object(v___x_2152_);
lean_dec_ref(v_code_2150_);
lean_dec_ref(v_params_2149_);
lean_del_object(v___x_2137_);
lean_dec(v_discr_2134_);
v_a_2192_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2154_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2154_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
else
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
lean_dec(v___x_2148_);
lean_del_object(v___x_2137_);
lean_dec(v_discr_2134_);
v___x_2202_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5);
v___x_2203_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2202_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
return v___x_2203_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2208_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2209_ = lean_unsigned_to_nat(2u);
v___x_2210_ = lean_unsigned_to_nat(297u);
v___x_2211_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0));
v___x_2212_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2213_ = l_mkPanicMessageWithDecl(v___x_2212_, v___x_2211_, v___x_2210_, v___x_2209_, v___x_2208_);
return v___x_2213_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2220_ = lean_box(0);
v___x_2221_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__7));
v___x_2222_ = l_Lean_Expr_const___override(v___x_2221_, v___x_2220_);
return v___x_2222_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2223_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__14));
v___x_2224_ = lean_unsigned_to_nat(34u);
v___x_2225_ = lean_unsigned_to_nat(298u);
v___x_2226_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0));
v___x_2227_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2228_ = l_mkPanicMessageWithDecl(v___x_2227_, v___x_2226_, v___x_2225_, v___x_2224_, v___x_2223_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg(lean_object* v_c_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_){
_start:
{
lean_object* v_discr_2236_; lean_object* v_alts_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v_discr_2236_ = lean_ctor_get(v_c_2229_, 2);
v_alts_2237_ = lean_ctor_get(v_c_2229_, 3);
v___x_2238_ = lean_array_get_size(v_alts_2237_);
v___x_2239_ = lean_unsigned_to_nat(1u);
v___x_2240_ = lean_nat_dec_eq(v___x_2238_, v___x_2239_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1);
v___x_2242_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2241_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
return v___x_2242_;
}
else
{
uint8_t v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2243_ = 0;
v___x_2244_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2245_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2246_ = lean_unsigned_to_nat(0u);
v___x_2247_ = lean_array_get(v___x_2245_, v_alts_2237_, v___x_2246_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_params_2248_; lean_object* v_code_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2345_; 
v_params_2248_ = lean_ctor_get(v___x_2247_, 1);
v_code_2249_ = lean_ctor_get(v___x_2247_, 2);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2345_ == 0)
{
lean_object* v_unused_2346_; 
v_unused_2346_ = lean_ctor_get(v___x_2247_, 0);
lean_dec(v_unused_2346_);
v___x_2251_ = v___x_2247_;
v_isShared_2252_ = v_isSharedCheck_2345_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_code_2249_);
lean_inc(v_params_2248_);
lean_dec(v___x_2247_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2345_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2243_, v_params_2248_, v_a_2232_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
lean_dec_ref_known(v___x_2253_, 1);
v___x_2254_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3));
v___x_2255_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2254_, v_a_2232_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2263_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_a_2256_);
lean_dec_ref_known(v___x_2255_, 1);
lean_inc(v_discr_2236_);
v___x_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2257_, 0, v_discr_2236_);
v___x_2258_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5));
v___x_2259_ = lean_box(0);
v___x_2260_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_2261_ = lean_array_push(v___x_2260_, v___x_2257_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set_tag(v___x_2251_, 3);
lean_ctor_set(v___x_2251_, 2, v___x_2261_);
lean_ctor_set(v___x_2251_, 1, v___x_2259_);
lean_ctor_set(v___x_2251_, 0, v___x_2258_);
v___x_2263_ = v___x_2251_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2328_, 2, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2265_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2243_, v_a_2256_, v___x_2264_, v___x_2263_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; lean_object* v___x_2269_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref_known(v___x_2265_, 1);
v___x_2267_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8);
v___x_2268_ = 0;
v___x_2269_ = l_Lean_Compiler_LCNF_mkAuxParam(v___x_2243_, v___x_2267_, v___x_2268_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2271_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2269_, 1);
v___x_2271_ = l_Lean_mkArrow(v___x_2267_, v___x_2264_, v_a_2233_, v_a_2234_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v_fvarId_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v_fvarId_2276_; lean_object* v_binderName_2277_; lean_object* v_lctx_2278_; lean_object* v_nextIdx_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2303_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2272_);
lean_dec_ref_known(v___x_2271_, 1);
v_fvarId_2273_ = lean_ctor_get(v_a_2266_, 0);
v___x_2274_ = lean_st_ref_take(v_a_2232_);
v___x_2275_ = lean_array_get(v___x_2244_, v_params_2248_, v___x_2246_);
lean_dec_ref(v_params_2248_);
v_fvarId_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_fvarId_2276_);
v_binderName_2277_ = lean_ctor_get(v___x_2275_, 1);
lean_inc(v_binderName_2277_);
lean_dec(v___x_2275_);
v_lctx_2278_ = lean_ctor_get(v___x_2274_, 0);
v_nextIdx_2279_ = lean_ctor_get(v___x_2274_, 1);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2281_ = v___x_2274_;
v_isShared_2282_ = v_isSharedCheck_2303_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_nextIdx_2279_);
lean_inc(v_lctx_2278_);
lean_dec(v___x_2274_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2303_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; 
lean_inc(v_fvarId_2273_);
v___x_2283_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2283_, 0, v_fvarId_2273_);
v___x_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2284_, 0, v_a_2266_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
v___x_2285_ = lean_mk_empty_array_with_capacity(v___x_2239_);
v___x_2286_ = lean_array_push(v___x_2285_, v_a_2270_);
v___x_2287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2287_, 0, v_fvarId_2276_);
lean_ctor_set(v___x_2287_, 1, v_binderName_2277_);
lean_ctor_set(v___x_2287_, 2, v___x_2286_);
lean_ctor_set(v___x_2287_, 3, v_a_2272_);
lean_ctor_set(v___x_2287_, 4, v___x_2284_);
lean_inc_ref(v___x_2287_);
v___x_2288_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_2243_, v_lctx_2278_, v___x_2287_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v___x_2288_);
v___x_2290_ = v___x_2281_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2288_);
lean_ctor_set(v_reuseFailAlloc_2302_, 1, v_nextIdx_2279_);
v___x_2290_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = lean_st_ref_put(v_a_2232_, v___x_2290_);
v___x_2292_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2249_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2301_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2295_ = v___x_2292_;
v_isShared_2296_ = v_isSharedCheck_2301_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2292_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2301_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2297_; lean_object* v___x_2299_; 
v___x_2297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2287_);
lean_ctor_set(v___x_2297_, 1, v_a_2293_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v___x_2297_);
v___x_2299_ = v___x_2295_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
else
{
lean_dec_ref_known(v___x_2287_, 5);
return v___x_2292_;
}
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec(v_a_2270_);
lean_dec(v_a_2266_);
lean_dec_ref(v_code_2249_);
lean_dec_ref(v_params_2248_);
v_a_2304_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2271_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2271_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec(v_a_2266_);
lean_dec_ref(v_code_2249_);
lean_dec_ref(v_params_2248_);
v_a_2312_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2269_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2269_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
lean_dec_ref(v_code_2249_);
lean_dec_ref(v_params_2248_);
v_a_2320_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2265_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2265_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
lean_del_object(v___x_2251_);
lean_dec_ref(v_code_2249_);
lean_dec_ref(v_params_2248_);
v_a_2329_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2255_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2255_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2329_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_del_object(v___x_2251_);
lean_dec_ref(v_code_2249_);
lean_dec_ref(v_params_2248_);
v_a_2337_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2253_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2253_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
else
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
lean_dec(v___x_2247_);
v___x_2347_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9);
v___x_2348_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2347_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
return v___x_2348_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2350_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2351_ = lean_unsigned_to_nat(2u);
v___x_2352_ = lean_unsigned_to_nat(286u);
v___x_2353_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0));
v___x_2354_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2355_ = l_mkPanicMessageWithDecl(v___x_2354_, v___x_2353_, v___x_2352_, v___x_2351_, v___x_2350_);
return v___x_2355_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2360_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__14));
v___x_2361_ = lean_unsigned_to_nat(34u);
v___x_2362_ = lean_unsigned_to_nat(287u);
v___x_2363_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0));
v___x_2364_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2365_ = l_mkPanicMessageWithDecl(v___x_2364_, v___x_2363_, v___x_2362_, v___x_2361_, v___x_2360_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(lean_object* v_c_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_){
_start:
{
lean_object* v_discr_2373_; lean_object* v_alts_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2443_; 
v_discr_2373_ = lean_ctor_get(v_c_2366_, 2);
v_alts_2374_ = lean_ctor_get(v_c_2366_, 3);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_c_2366_);
if (v_isSharedCheck_2443_ == 0)
{
lean_object* v_unused_2444_; lean_object* v_unused_2445_; 
v_unused_2444_ = lean_ctor_get(v_c_2366_, 1);
lean_dec(v_unused_2444_);
v_unused_2445_ = lean_ctor_get(v_c_2366_, 0);
lean_dec(v_unused_2445_);
v___x_2376_ = v_c_2366_;
v_isShared_2377_ = v_isSharedCheck_2443_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_alts_2374_);
lean_inc(v_discr_2373_);
lean_dec(v_c_2366_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2443_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2378_ = lean_array_get_size(v_alts_2374_);
v___x_2379_ = lean_unsigned_to_nat(1u);
v___x_2380_ = lean_nat_dec_eq(v___x_2378_, v___x_2379_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
lean_del_object(v___x_2376_);
lean_dec_ref(v_alts_2374_);
lean_dec(v_discr_2373_);
v___x_2381_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1);
v___x_2382_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2381_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_2382_;
}
else
{
uint8_t v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2383_ = 0;
v___x_2384_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2385_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2386_ = lean_unsigned_to_nat(0u);
v___x_2387_ = lean_array_get(v___x_2385_, v_alts_2374_, v___x_2386_);
lean_dec_ref(v_alts_2374_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_params_2388_; lean_object* v_code_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2439_; 
v_params_2388_ = lean_ctor_get(v___x_2387_, 1);
v_code_2389_ = lean_ctor_get(v___x_2387_, 2);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2439_ == 0)
{
lean_object* v_unused_2440_; 
v_unused_2440_ = lean_ctor_get(v___x_2387_, 0);
lean_dec(v_unused_2440_);
v___x_2391_ = v___x_2387_;
v_isShared_2392_ = v_isSharedCheck_2439_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_code_2389_);
lean_inc(v_params_2388_);
lean_dec(v___x_2387_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2439_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2383_, v_params_2388_, v_a_2369_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v_fvarId_2396_; lean_object* v_binderName_2397_; lean_object* v_lctx_2398_; lean_object* v_nextIdx_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2430_; 
lean_dec_ref_known(v___x_2393_, 1);
v___x_2394_ = lean_st_ref_take(v_a_2369_);
v___x_2395_ = lean_array_get(v___x_2384_, v_params_2388_, v___x_2386_);
lean_dec_ref(v_params_2388_);
v_fvarId_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_fvarId_2396_);
v_binderName_2397_ = lean_ctor_get(v___x_2395_, 1);
lean_inc(v_binderName_2397_);
lean_dec(v___x_2395_);
v_lctx_2398_ = lean_ctor_get(v___x_2394_, 0);
v_nextIdx_2399_ = lean_ctor_get(v___x_2394_, 1);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2401_ = v___x_2394_;
v_isShared_2402_ = v_isSharedCheck_2430_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_nextIdx_2399_);
lean_inc(v_lctx_2398_);
lean_dec(v___x_2394_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2430_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2403_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__4));
v___x_2404_ = lean_box(0);
v___x_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2405_, 0, v_discr_2373_);
v___x_2406_ = lean_mk_empty_array_with_capacity(v___x_2379_);
v___x_2407_ = lean_array_push(v___x_2406_, v___x_2405_);
if (v_isShared_2392_ == 0)
{
lean_ctor_set_tag(v___x_2391_, 3);
lean_ctor_set(v___x_2391_, 2, v___x_2407_);
lean_ctor_set(v___x_2391_, 1, v___x_2404_);
lean_ctor_set(v___x_2391_, 0, v___x_2403_);
v___x_2409_ = v___x_2391_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2403_);
lean_ctor_set(v_reuseFailAlloc_2429_, 1, v___x_2404_);
lean_ctor_set(v_reuseFailAlloc_2429_, 2, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2410_; lean_object* v___x_2412_; 
v___x_2410_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 3, v___x_2409_);
lean_ctor_set(v___x_2376_, 2, v___x_2410_);
lean_ctor_set(v___x_2376_, 1, v_binderName_2397_);
lean_ctor_set(v___x_2376_, 0, v_fvarId_2396_);
v___x_2412_ = v___x_2376_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_fvarId_2396_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_binderName_2397_);
lean_ctor_set(v_reuseFailAlloc_2428_, 2, v___x_2410_);
lean_ctor_set(v_reuseFailAlloc_2428_, 3, v___x_2409_);
v___x_2412_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
lean_object* v___x_2413_; lean_object* v___x_2415_; 
lean_inc_ref(v___x_2412_);
v___x_2413_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2383_, v_lctx_2398_, v___x_2412_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 0, v___x_2413_);
v___x_2415_ = v___x_2401_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_nextIdx_2399_);
v___x_2415_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2416_ = lean_st_ref_put(v_a_2369_, v___x_2415_);
v___x_2417_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2389_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2426_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2426_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2426_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2412_);
lean_ctor_set(v___x_2422_, 1, v_a_2418_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v___x_2422_);
v___x_2424_ = v___x_2420_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
else
{
lean_dec_ref(v___x_2412_);
return v___x_2417_;
}
}
}
}
}
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_del_object(v___x_2391_);
lean_dec_ref(v_code_2389_);
lean_dec_ref(v_params_2388_);
lean_del_object(v___x_2376_);
lean_dec(v_discr_2373_);
v_a_2431_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2393_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2393_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
}
else
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
lean_dec(v___x_2387_);
lean_del_object(v___x_2376_);
lean_dec(v_discr_2373_);
v___x_2441_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5);
v___x_2442_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2441_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_2442_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2447_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2448_ = lean_unsigned_to_nat(2u);
v___x_2449_ = lean_unsigned_to_nat(275u);
v___x_2450_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0));
v___x_2451_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2452_ = l_mkPanicMessageWithDecl(v___x_2451_, v___x_2450_, v___x_2449_, v___x_2448_, v___x_2447_);
return v___x_2452_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2456_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__14));
v___x_2457_ = lean_unsigned_to_nat(34u);
v___x_2458_ = lean_unsigned_to_nat(276u);
v___x_2459_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0));
v___x_2460_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2461_ = l_mkPanicMessageWithDecl(v___x_2460_, v___x_2459_, v___x_2458_, v___x_2457_, v___x_2456_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg(lean_object* v_c_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v_discr_2469_; lean_object* v_alts_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2539_; 
v_discr_2469_ = lean_ctor_get(v_c_2462_, 2);
v_alts_2470_ = lean_ctor_get(v_c_2462_, 3);
v_isSharedCheck_2539_ = !lean_is_exclusive(v_c_2462_);
if (v_isSharedCheck_2539_ == 0)
{
lean_object* v_unused_2540_; lean_object* v_unused_2541_; 
v_unused_2540_ = lean_ctor_get(v_c_2462_, 1);
lean_dec(v_unused_2540_);
v_unused_2541_ = lean_ctor_get(v_c_2462_, 0);
lean_dec(v_unused_2541_);
v___x_2472_ = v_c_2462_;
v_isShared_2473_ = v_isSharedCheck_2539_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_alts_2470_);
lean_inc(v_discr_2469_);
lean_dec(v_c_2462_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2539_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; uint8_t v___x_2476_; 
v___x_2474_ = lean_array_get_size(v_alts_2470_);
v___x_2475_ = lean_unsigned_to_nat(1u);
v___x_2476_ = lean_nat_dec_eq(v___x_2474_, v___x_2475_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
lean_del_object(v___x_2472_);
lean_dec_ref(v_alts_2470_);
lean_dec(v_discr_2469_);
v___x_2477_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1);
v___x_2478_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2477_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_);
return v___x_2478_;
}
else
{
uint8_t v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2479_ = 0;
v___x_2480_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2481_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2482_ = lean_unsigned_to_nat(0u);
v___x_2483_ = lean_array_get(v___x_2481_, v_alts_2470_, v___x_2482_);
lean_dec_ref(v_alts_2470_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_params_2484_; lean_object* v_code_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2535_; 
v_params_2484_ = lean_ctor_get(v___x_2483_, 1);
v_code_2485_ = lean_ctor_get(v___x_2483_, 2);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2535_ == 0)
{
lean_object* v_unused_2536_; 
v_unused_2536_ = lean_ctor_get(v___x_2483_, 0);
lean_dec(v_unused_2536_);
v___x_2487_ = v___x_2483_;
v_isShared_2488_ = v_isSharedCheck_2535_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_code_2485_);
lean_inc(v_params_2484_);
lean_dec(v___x_2483_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2535_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2489_; 
v___x_2489_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2479_, v_params_2484_, v_a_2465_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v_fvarId_2492_; lean_object* v_binderName_2493_; lean_object* v_lctx_2494_; lean_object* v_nextIdx_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2526_; 
lean_dec_ref_known(v___x_2489_, 1);
v___x_2490_ = lean_st_ref_take(v_a_2465_);
v___x_2491_ = lean_array_get(v___x_2480_, v_params_2484_, v___x_2482_);
lean_dec_ref(v_params_2484_);
v_fvarId_2492_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_fvarId_2492_);
v_binderName_2493_ = lean_ctor_get(v___x_2491_, 1);
lean_inc(v_binderName_2493_);
lean_dec(v___x_2491_);
v_lctx_2494_ = lean_ctor_get(v___x_2490_, 0);
v_nextIdx_2495_ = lean_ctor_get(v___x_2490_, 1);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2497_ = v___x_2490_;
v_isShared_2498_ = v_isSharedCheck_2526_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_nextIdx_2495_);
lean_inc(v_lctx_2494_);
lean_dec(v___x_2490_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2526_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2505_; 
v___x_2499_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__3));
v___x_2500_ = lean_box(0);
v___x_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2501_, 0, v_discr_2469_);
v___x_2502_ = lean_mk_empty_array_with_capacity(v___x_2475_);
v___x_2503_ = lean_array_push(v___x_2502_, v___x_2501_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set_tag(v___x_2487_, 3);
lean_ctor_set(v___x_2487_, 2, v___x_2503_);
lean_ctor_set(v___x_2487_, 1, v___x_2500_);
lean_ctor_set(v___x_2487_, 0, v___x_2499_);
v___x_2505_ = v___x_2487_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v___x_2500_);
lean_ctor_set(v_reuseFailAlloc_2525_, 2, v___x_2503_);
v___x_2505_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v___x_2506_; lean_object* v___x_2508_; 
v___x_2506_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 3, v___x_2505_);
lean_ctor_set(v___x_2472_, 2, v___x_2506_);
lean_ctor_set(v___x_2472_, 1, v_binderName_2493_);
lean_ctor_set(v___x_2472_, 0, v_fvarId_2492_);
v___x_2508_ = v___x_2472_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_fvarId_2492_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v_binderName_2493_);
lean_ctor_set(v_reuseFailAlloc_2524_, 2, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2524_, 3, v___x_2505_);
v___x_2508_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2509_; lean_object* v___x_2511_; 
lean_inc_ref(v___x_2508_);
v___x_2509_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2479_, v_lctx_2494_, v___x_2508_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 0, v___x_2509_);
v___x_2511_ = v___x_2497_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2509_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v_nextIdx_2495_);
v___x_2511_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = lean_st_ref_put(v_a_2465_, v___x_2511_);
v___x_2513_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2485_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2522_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2516_ = v___x_2513_;
v_isShared_2517_ = v_isSharedCheck_2522_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2513_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2522_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2518_; lean_object* v___x_2520_; 
v___x_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2508_);
lean_ctor_set(v___x_2518_, 1, v_a_2514_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v___x_2518_);
v___x_2520_ = v___x_2516_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
else
{
lean_dec_ref(v___x_2508_);
return v___x_2513_;
}
}
}
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_del_object(v___x_2487_);
lean_dec_ref(v_code_2485_);
lean_dec_ref(v_params_2484_);
lean_del_object(v___x_2472_);
lean_dec(v_discr_2469_);
v_a_2527_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2489_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2489_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
else
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
lean_dec(v___x_2483_);
lean_del_object(v___x_2472_);
lean_dec(v_discr_2469_);
v___x_2537_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4);
v___x_2538_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2537_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_);
return v___x_2538_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2543_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2544_ = lean_unsigned_to_nat(2u);
v___x_2545_ = lean_unsigned_to_nat(264u);
v___x_2546_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0));
v___x_2547_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2548_ = l_mkPanicMessageWithDecl(v___x_2547_, v___x_2546_, v___x_2545_, v___x_2544_, v___x_2543_);
return v___x_2548_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2553_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__14));
v___x_2554_ = lean_unsigned_to_nat(34u);
v___x_2555_ = lean_unsigned_to_nat(265u);
v___x_2556_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0));
v___x_2557_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2558_ = l_mkPanicMessageWithDecl(v___x_2557_, v___x_2556_, v___x_2555_, v___x_2554_, v___x_2553_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg(lean_object* v_c_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_){
_start:
{
lean_object* v_discr_2566_; lean_object* v_alts_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2636_; 
v_discr_2566_ = lean_ctor_get(v_c_2559_, 2);
v_alts_2567_ = lean_ctor_get(v_c_2559_, 3);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_c_2559_);
if (v_isSharedCheck_2636_ == 0)
{
lean_object* v_unused_2637_; lean_object* v_unused_2638_; 
v_unused_2637_ = lean_ctor_get(v_c_2559_, 1);
lean_dec(v_unused_2637_);
v_unused_2638_ = lean_ctor_get(v_c_2559_, 0);
lean_dec(v_unused_2638_);
v___x_2569_ = v_c_2559_;
v_isShared_2570_ = v_isSharedCheck_2636_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_alts_2567_);
lean_inc(v_discr_2566_);
lean_dec(v_c_2559_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2636_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2571_ = lean_array_get_size(v_alts_2567_);
v___x_2572_ = lean_unsigned_to_nat(1u);
v___x_2573_ = lean_nat_dec_eq(v___x_2571_, v___x_2572_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
lean_del_object(v___x_2569_);
lean_dec_ref(v_alts_2567_);
lean_dec(v_discr_2566_);
v___x_2574_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1);
v___x_2575_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2574_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_);
return v___x_2575_;
}
else
{
uint8_t v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2576_ = 0;
v___x_2577_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2578_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2579_ = lean_unsigned_to_nat(0u);
v___x_2580_ = lean_array_get(v___x_2578_, v_alts_2567_, v___x_2579_);
lean_dec_ref(v_alts_2567_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_params_2581_; lean_object* v_code_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2632_; 
v_params_2581_ = lean_ctor_get(v___x_2580_, 1);
v_code_2582_ = lean_ctor_get(v___x_2580_, 2);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2632_ == 0)
{
lean_object* v_unused_2633_; 
v_unused_2633_ = lean_ctor_get(v___x_2580_, 0);
lean_dec(v_unused_2633_);
v___x_2584_ = v___x_2580_;
v_isShared_2585_ = v_isSharedCheck_2632_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_code_2582_);
lean_inc(v_params_2581_);
lean_dec(v___x_2580_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2632_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2576_, v_params_2581_, v_a_2562_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v_fvarId_2589_; lean_object* v_binderName_2590_; lean_object* v_lctx_2591_; lean_object* v_nextIdx_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2623_; 
lean_dec_ref_known(v___x_2586_, 1);
v___x_2587_ = lean_st_ref_take(v_a_2562_);
v___x_2588_ = lean_array_get(v___x_2577_, v_params_2581_, v___x_2579_);
lean_dec_ref(v_params_2581_);
v_fvarId_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_fvarId_2589_);
v_binderName_2590_ = lean_ctor_get(v___x_2588_, 1);
lean_inc(v_binderName_2590_);
lean_dec(v___x_2588_);
v_lctx_2591_ = lean_ctor_get(v___x_2587_, 0);
v_nextIdx_2592_ = lean_ctor_get(v___x_2587_, 1);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2594_ = v___x_2587_;
v_isShared_2595_ = v_isSharedCheck_2623_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_nextIdx_2592_);
lean_inc(v_lctx_2591_);
lean_dec(v___x_2587_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2623_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2602_; 
v___x_2596_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__4));
v___x_2597_ = lean_box(0);
v___x_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2598_, 0, v_discr_2566_);
v___x_2599_ = lean_mk_empty_array_with_capacity(v___x_2572_);
v___x_2600_ = lean_array_push(v___x_2599_, v___x_2598_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set_tag(v___x_2584_, 3);
lean_ctor_set(v___x_2584_, 2, v___x_2600_);
lean_ctor_set(v___x_2584_, 1, v___x_2597_);
lean_ctor_set(v___x_2584_, 0, v___x_2596_);
v___x_2602_ = v___x_2584_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2622_, 2, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2603_; lean_object* v___x_2605_; 
v___x_2603_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 3, v___x_2602_);
lean_ctor_set(v___x_2569_, 2, v___x_2603_);
lean_ctor_set(v___x_2569_, 1, v_binderName_2590_);
lean_ctor_set(v___x_2569_, 0, v_fvarId_2589_);
v___x_2605_ = v___x_2569_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_fvarId_2589_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v_binderName_2590_);
lean_ctor_set(v_reuseFailAlloc_2621_, 2, v___x_2603_);
lean_ctor_set(v_reuseFailAlloc_2621_, 3, v___x_2602_);
v___x_2605_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
lean_object* v___x_2606_; lean_object* v___x_2608_; 
lean_inc_ref(v___x_2605_);
v___x_2606_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2576_, v_lctx_2591_, v___x_2605_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2606_);
v___x_2608_ = v___x_2594_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2606_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v_nextIdx_2592_);
v___x_2608_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = lean_st_ref_put(v_a_2562_, v___x_2608_);
v___x_2610_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2582_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2619_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2613_ = v___x_2610_;
v_isShared_2614_ = v_isSharedCheck_2619_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2610_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2619_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2615_; lean_object* v___x_2617_; 
v___x_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2605_);
lean_ctor_set(v___x_2615_, 1, v_a_2611_);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 0, v___x_2615_);
v___x_2617_ = v___x_2613_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
else
{
lean_dec_ref(v___x_2605_);
return v___x_2610_;
}
}
}
}
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_del_object(v___x_2584_);
lean_dec_ref(v_code_2582_);
lean_dec_ref(v_params_2581_);
lean_del_object(v___x_2569_);
lean_dec(v_discr_2566_);
v_a_2624_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2586_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2586_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
}
else
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_dec(v___x_2580_);
lean_del_object(v___x_2569_);
lean_dec(v_discr_2566_);
v___x_2634_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5);
v___x_2635_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2634_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_);
return v___x_2635_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2640_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2641_ = lean_unsigned_to_nat(2u);
v___x_2642_ = lean_unsigned_to_nat(253u);
v___x_2643_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0));
v___x_2644_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2645_ = l_mkPanicMessageWithDecl(v___x_2644_, v___x_2643_, v___x_2642_, v___x_2641_, v___x_2640_);
return v___x_2645_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2650_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__14));
v___x_2651_ = lean_unsigned_to_nat(34u);
v___x_2652_ = lean_unsigned_to_nat(254u);
v___x_2653_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0));
v___x_2654_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2655_ = l_mkPanicMessageWithDecl(v___x_2654_, v___x_2653_, v___x_2652_, v___x_2651_, v___x_2650_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(lean_object* v_c_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v_discr_2663_; lean_object* v_alts_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2733_; 
v_discr_2663_ = lean_ctor_get(v_c_2656_, 2);
v_alts_2664_ = lean_ctor_get(v_c_2656_, 3);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_c_2656_);
if (v_isSharedCheck_2733_ == 0)
{
lean_object* v_unused_2734_; lean_object* v_unused_2735_; 
v_unused_2734_ = lean_ctor_get(v_c_2656_, 1);
lean_dec(v_unused_2734_);
v_unused_2735_ = lean_ctor_get(v_c_2656_, 0);
lean_dec(v_unused_2735_);
v___x_2666_ = v_c_2656_;
v_isShared_2667_ = v_isSharedCheck_2733_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_alts_2664_);
lean_inc(v_discr_2663_);
lean_dec(v_c_2656_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2733_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v___x_2668_ = lean_array_get_size(v_alts_2664_);
v___x_2669_ = lean_unsigned_to_nat(1u);
v___x_2670_ = lean_nat_dec_eq(v___x_2668_, v___x_2669_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
lean_del_object(v___x_2666_);
lean_dec_ref(v_alts_2664_);
lean_dec(v_discr_2663_);
v___x_2671_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1);
v___x_2672_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2671_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
return v___x_2672_;
}
else
{
uint8_t v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2673_ = 0;
v___x_2674_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2675_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2676_ = lean_unsigned_to_nat(0u);
v___x_2677_ = lean_array_get(v___x_2675_, v_alts_2664_, v___x_2676_);
lean_dec_ref(v_alts_2664_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_params_2678_; lean_object* v_code_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2729_; 
v_params_2678_ = lean_ctor_get(v___x_2677_, 1);
v_code_2679_ = lean_ctor_get(v___x_2677_, 2);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2729_ == 0)
{
lean_object* v_unused_2730_; 
v_unused_2730_ = lean_ctor_get(v___x_2677_, 0);
lean_dec(v_unused_2730_);
v___x_2681_ = v___x_2677_;
v_isShared_2682_ = v_isSharedCheck_2729_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_code_2679_);
lean_inc(v_params_2678_);
lean_dec(v___x_2677_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2729_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2673_, v_params_2678_, v_a_2659_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v_fvarId_2686_; lean_object* v_binderName_2687_; lean_object* v_lctx_2688_; lean_object* v_nextIdx_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2720_; 
lean_dec_ref_known(v___x_2683_, 1);
v___x_2684_ = lean_st_ref_take(v_a_2659_);
v___x_2685_ = lean_array_get(v___x_2674_, v_params_2678_, v___x_2676_);
lean_dec_ref(v_params_2678_);
v_fvarId_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_fvarId_2686_);
v_binderName_2687_ = lean_ctor_get(v___x_2685_, 1);
lean_inc(v_binderName_2687_);
lean_dec(v___x_2685_);
v_lctx_2688_ = lean_ctor_get(v___x_2684_, 0);
v_nextIdx_2689_ = lean_ctor_get(v___x_2684_, 1);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2691_ = v___x_2684_;
v_isShared_2692_ = v_isSharedCheck_2720_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_nextIdx_2689_);
lean_inc(v_lctx_2688_);
lean_dec(v___x_2684_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2720_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2693_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__3));
v___x_2694_ = lean_box(0);
v___x_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2695_, 0, v_discr_2663_);
v___x_2696_ = lean_mk_empty_array_with_capacity(v___x_2669_);
v___x_2697_ = lean_array_push(v___x_2696_, v___x_2695_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set_tag(v___x_2681_, 3);
lean_ctor_set(v___x_2681_, 2, v___x_2697_);
lean_ctor_set(v___x_2681_, 1, v___x_2694_);
lean_ctor_set(v___x_2681_, 0, v___x_2693_);
v___x_2699_ = v___x_2681_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2693_);
lean_ctor_set(v_reuseFailAlloc_2719_, 1, v___x_2694_);
lean_ctor_set(v_reuseFailAlloc_2719_, 2, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2700_; lean_object* v___x_2702_; 
v___x_2700_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 3, v___x_2699_);
lean_ctor_set(v___x_2666_, 2, v___x_2700_);
lean_ctor_set(v___x_2666_, 1, v_binderName_2687_);
lean_ctor_set(v___x_2666_, 0, v_fvarId_2686_);
v___x_2702_ = v___x_2666_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_fvarId_2686_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v_binderName_2687_);
lean_ctor_set(v_reuseFailAlloc_2718_, 2, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2718_, 3, v___x_2699_);
v___x_2702_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2703_; lean_object* v___x_2705_; 
lean_inc_ref(v___x_2702_);
v___x_2703_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2673_, v_lctx_2688_, v___x_2702_);
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 0, v___x_2703_);
v___x_2705_ = v___x_2691_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2703_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_nextIdx_2689_);
v___x_2705_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = lean_st_ref_put(v_a_2659_, v___x_2705_);
v___x_2707_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2679_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2716_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2710_ = v___x_2707_;
v_isShared_2711_ = v_isSharedCheck_2716_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2716_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2712_; lean_object* v___x_2714_; 
v___x_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2702_);
lean_ctor_set(v___x_2712_, 1, v_a_2708_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v___x_2712_);
v___x_2714_ = v___x_2710_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2712_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
else
{
lean_dec_ref(v___x_2702_);
return v___x_2707_;
}
}
}
}
}
}
else
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
lean_del_object(v___x_2681_);
lean_dec_ref(v_code_2679_);
lean_dec_ref(v_params_2678_);
lean_del_object(v___x_2666_);
lean_dec(v_discr_2663_);
v_a_2721_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___x_2683_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2683_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
}
else
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
lean_dec(v___x_2677_);
lean_del_object(v___x_2666_);
lean_dec(v_discr_2663_);
v___x_2731_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4);
v___x_2732_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2731_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
return v___x_2732_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2737_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2738_ = lean_unsigned_to_nat(2u);
v___x_2739_ = lean_unsigned_to_nat(241u);
v___x_2740_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0));
v___x_2741_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2742_ = l_mkPanicMessageWithDecl(v___x_2741_, v___x_2740_, v___x_2739_, v___x_2738_, v___x_2737_);
return v___x_2742_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2746_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__14));
v___x_2747_ = lean_unsigned_to_nat(34u);
v___x_2748_ = lean_unsigned_to_nat(242u);
v___x_2749_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0));
v___x_2750_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2751_ = l_mkPanicMessageWithDecl(v___x_2750_, v___x_2749_, v___x_2748_, v___x_2747_, v___x_2746_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(lean_object* v_c_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_){
_start:
{
lean_object* v_discr_2759_; lean_object* v_alts_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2829_; 
v_discr_2759_ = lean_ctor_get(v_c_2752_, 2);
v_alts_2760_ = lean_ctor_get(v_c_2752_, 3);
v_isSharedCheck_2829_ = !lean_is_exclusive(v_c_2752_);
if (v_isSharedCheck_2829_ == 0)
{
lean_object* v_unused_2830_; lean_object* v_unused_2831_; 
v_unused_2830_ = lean_ctor_get(v_c_2752_, 1);
lean_dec(v_unused_2830_);
v_unused_2831_ = lean_ctor_get(v_c_2752_, 0);
lean_dec(v_unused_2831_);
v___x_2762_ = v_c_2752_;
v_isShared_2763_ = v_isSharedCheck_2829_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_alts_2760_);
lean_inc(v_discr_2759_);
lean_dec(v_c_2752_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2829_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; uint8_t v___x_2766_; 
v___x_2764_ = lean_array_get_size(v_alts_2760_);
v___x_2765_ = lean_unsigned_to_nat(1u);
v___x_2766_ = lean_nat_dec_eq(v___x_2764_, v___x_2765_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
lean_del_object(v___x_2762_);
lean_dec_ref(v_alts_2760_);
lean_dec(v_discr_2759_);
v___x_2767_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1);
v___x_2768_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2767_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_);
return v___x_2768_;
}
else
{
uint8_t v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2769_ = 0;
v___x_2770_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2771_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2772_ = lean_unsigned_to_nat(0u);
v___x_2773_ = lean_array_get(v___x_2771_, v_alts_2760_, v___x_2772_);
lean_dec_ref(v_alts_2760_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_params_2774_; lean_object* v_code_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2825_; 
v_params_2774_ = lean_ctor_get(v___x_2773_, 1);
v_code_2775_ = lean_ctor_get(v___x_2773_, 2);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2825_ == 0)
{
lean_object* v_unused_2826_; 
v_unused_2826_ = lean_ctor_get(v___x_2773_, 0);
lean_dec(v_unused_2826_);
v___x_2777_ = v___x_2773_;
v_isShared_2778_ = v_isSharedCheck_2825_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_code_2775_);
lean_inc(v_params_2774_);
lean_dec(v___x_2773_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2825_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; 
v___x_2779_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2769_, v_params_2774_, v_a_2755_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v_fvarId_2782_; lean_object* v_binderName_2783_; lean_object* v_lctx_2784_; lean_object* v_nextIdx_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2816_; 
lean_dec_ref_known(v___x_2779_, 1);
v___x_2780_ = lean_st_ref_take(v_a_2755_);
v___x_2781_ = lean_array_get(v___x_2770_, v_params_2774_, v___x_2772_);
lean_dec_ref(v_params_2774_);
v_fvarId_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_fvarId_2782_);
v_binderName_2783_ = lean_ctor_get(v___x_2781_, 1);
lean_inc(v_binderName_2783_);
lean_dec(v___x_2781_);
v_lctx_2784_ = lean_ctor_get(v___x_2780_, 0);
v_nextIdx_2785_ = lean_ctor_get(v___x_2780_, 1);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2787_ = v___x_2780_;
v_isShared_2788_ = v_isSharedCheck_2816_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_nextIdx_2785_);
lean_inc(v_lctx_2784_);
lean_dec(v___x_2780_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2816_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2795_; 
v___x_2789_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__4));
v___x_2790_ = lean_box(0);
v___x_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2791_, 0, v_discr_2759_);
v___x_2792_ = lean_mk_empty_array_with_capacity(v___x_2765_);
v___x_2793_ = lean_array_push(v___x_2792_, v___x_2791_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set_tag(v___x_2777_, 3);
lean_ctor_set(v___x_2777_, 2, v___x_2793_);
lean_ctor_set(v___x_2777_, 1, v___x_2790_);
lean_ctor_set(v___x_2777_, 0, v___x_2789_);
v___x_2795_ = v___x_2777_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2789_);
lean_ctor_set(v_reuseFailAlloc_2815_, 1, v___x_2790_);
lean_ctor_set(v_reuseFailAlloc_2815_, 2, v___x_2793_);
v___x_2795_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2796_; lean_object* v___x_2798_; 
v___x_2796_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 3, v___x_2795_);
lean_ctor_set(v___x_2762_, 2, v___x_2796_);
lean_ctor_set(v___x_2762_, 1, v_binderName_2783_);
lean_ctor_set(v___x_2762_, 0, v_fvarId_2782_);
v___x_2798_ = v___x_2762_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_fvarId_2782_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_binderName_2783_);
lean_ctor_set(v_reuseFailAlloc_2814_, 2, v___x_2796_);
lean_ctor_set(v_reuseFailAlloc_2814_, 3, v___x_2795_);
v___x_2798_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
lean_object* v___x_2799_; lean_object* v___x_2801_; 
lean_inc_ref(v___x_2798_);
v___x_2799_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2769_, v_lctx_2784_, v___x_2798_);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v___x_2799_);
v___x_2801_ = v___x_2787_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2799_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v_nextIdx_2785_);
v___x_2801_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = lean_st_ref_put(v_a_2755_, v___x_2801_);
v___x_2803_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2775_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2812_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2806_ = v___x_2803_;
v_isShared_2807_ = v_isSharedCheck_2812_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2803_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2812_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2808_; lean_object* v___x_2810_; 
v___x_2808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2798_);
lean_ctor_set(v___x_2808_, 1, v_a_2804_);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v___x_2808_);
v___x_2810_ = v___x_2806_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2808_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
else
{
lean_dec_ref(v___x_2798_);
return v___x_2803_;
}
}
}
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
lean_del_object(v___x_2777_);
lean_dec_ref(v_code_2775_);
lean_dec_ref(v_params_2774_);
lean_del_object(v___x_2762_);
lean_dec(v_discr_2759_);
v_a_2817_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2779_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2779_);
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
}
else
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
lean_dec(v___x_2773_);
lean_del_object(v___x_2762_);
lean_dec(v_discr_2759_);
v___x_2827_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5);
v___x_2828_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2827_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_);
return v___x_2828_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2833_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2834_ = lean_unsigned_to_nat(2u);
v___x_2835_ = lean_unsigned_to_nat(229u);
v___x_2836_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0));
v___x_2837_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2838_ = l_mkPanicMessageWithDecl(v___x_2837_, v___x_2836_, v___x_2835_, v___x_2834_, v___x_2833_);
return v___x_2838_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6(void){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2843_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__14));
v___x_2844_ = lean_unsigned_to_nat(34u);
v___x_2845_ = lean_unsigned_to_nat(230u);
v___x_2846_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0));
v___x_2847_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2848_ = l_mkPanicMessageWithDecl(v___x_2847_, v___x_2846_, v___x_2845_, v___x_2844_, v___x_2843_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg(lean_object* v_c_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_){
_start:
{
lean_object* v_discr_2856_; lean_object* v_alts_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2926_; 
v_discr_2856_ = lean_ctor_get(v_c_2849_, 2);
v_alts_2857_ = lean_ctor_get(v_c_2849_, 3);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_c_2849_);
if (v_isSharedCheck_2926_ == 0)
{
lean_object* v_unused_2927_; lean_object* v_unused_2928_; 
v_unused_2927_ = lean_ctor_get(v_c_2849_, 1);
lean_dec(v_unused_2927_);
v_unused_2928_ = lean_ctor_get(v_c_2849_, 0);
lean_dec(v_unused_2928_);
v___x_2859_ = v_c_2849_;
v_isShared_2860_ = v_isSharedCheck_2926_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_alts_2857_);
lean_inc(v_discr_2856_);
lean_dec(v_c_2849_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2926_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
v___x_2861_ = lean_array_get_size(v_alts_2857_);
v___x_2862_ = lean_unsigned_to_nat(1u);
v___x_2863_ = lean_nat_dec_eq(v___x_2861_, v___x_2862_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
lean_del_object(v___x_2859_);
lean_dec_ref(v_alts_2857_);
lean_dec(v_discr_2856_);
v___x_2864_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1);
v___x_2865_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2864_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_);
return v___x_2865_;
}
else
{
uint8_t v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2866_ = 0;
v___x_2867_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2868_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2869_ = lean_unsigned_to_nat(0u);
v___x_2870_ = lean_array_get(v___x_2868_, v_alts_2857_, v___x_2869_);
lean_dec_ref(v_alts_2857_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v_params_2871_; lean_object* v_code_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2922_; 
v_params_2871_ = lean_ctor_get(v___x_2870_, 1);
v_code_2872_ = lean_ctor_get(v___x_2870_, 2);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2922_ == 0)
{
lean_object* v_unused_2923_; 
v_unused_2923_ = lean_ctor_get(v___x_2870_, 0);
lean_dec(v_unused_2923_);
v___x_2874_ = v___x_2870_;
v_isShared_2875_ = v_isSharedCheck_2922_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_code_2872_);
lean_inc(v_params_2871_);
lean_dec(v___x_2870_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2922_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2876_; 
v___x_2876_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2866_, v_params_2871_, v_a_2852_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v_fvarId_2879_; lean_object* v_binderName_2880_; lean_object* v_lctx_2881_; lean_object* v_nextIdx_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2913_; 
lean_dec_ref_known(v___x_2876_, 1);
v___x_2877_ = lean_st_ref_take(v_a_2852_);
v___x_2878_ = lean_array_get(v___x_2867_, v_params_2871_, v___x_2869_);
lean_dec_ref(v_params_2871_);
v_fvarId_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_fvarId_2879_);
v_binderName_2880_ = lean_ctor_get(v___x_2878_, 1);
lean_inc(v_binderName_2880_);
lean_dec(v___x_2878_);
v_lctx_2881_ = lean_ctor_get(v___x_2877_, 0);
v_nextIdx_2882_ = lean_ctor_get(v___x_2877_, 1);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2884_ = v___x_2877_;
v_isShared_2885_ = v_isSharedCheck_2913_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_nextIdx_2882_);
lean_inc(v_lctx_2881_);
lean_dec(v___x_2877_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2913_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2892_; 
v___x_2886_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__4));
v___x_2887_ = lean_box(0);
v___x_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2888_, 0, v_discr_2856_);
v___x_2889_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_2890_ = lean_array_push(v___x_2889_, v___x_2888_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set_tag(v___x_2874_, 3);
lean_ctor_set(v___x_2874_, 2, v___x_2890_);
lean_ctor_set(v___x_2874_, 1, v___x_2887_);
lean_ctor_set(v___x_2874_, 0, v___x_2886_);
v___x_2892_ = v___x_2874_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2886_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v___x_2887_);
lean_ctor_set(v_reuseFailAlloc_2912_, 2, v___x_2890_);
v___x_2892_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
lean_object* v___x_2893_; lean_object* v___x_2895_; 
v___x_2893_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 3, v___x_2892_);
lean_ctor_set(v___x_2859_, 2, v___x_2893_);
lean_ctor_set(v___x_2859_, 1, v_binderName_2880_);
lean_ctor_set(v___x_2859_, 0, v_fvarId_2879_);
v___x_2895_ = v___x_2859_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_fvarId_2879_);
lean_ctor_set(v_reuseFailAlloc_2911_, 1, v_binderName_2880_);
lean_ctor_set(v_reuseFailAlloc_2911_, 2, v___x_2893_);
lean_ctor_set(v_reuseFailAlloc_2911_, 3, v___x_2892_);
v___x_2895_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_object* v___x_2896_; lean_object* v___x_2898_; 
lean_inc_ref(v___x_2895_);
v___x_2896_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2866_, v_lctx_2881_, v___x_2895_);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v___x_2896_);
v___x_2898_ = v___x_2884_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2896_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_nextIdx_2882_);
v___x_2898_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = lean_st_ref_put(v_a_2852_, v___x_2898_);
v___x_2900_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2872_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2909_; 
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2903_ = v___x_2900_;
v_isShared_2904_ = v_isSharedCheck_2909_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2900_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2909_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2905_; lean_object* v___x_2907_; 
v___x_2905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2895_);
lean_ctor_set(v___x_2905_, 1, v_a_2901_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v___x_2905_);
v___x_2907_ = v___x_2903_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2905_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
else
{
lean_dec_ref(v___x_2895_);
return v___x_2900_;
}
}
}
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_del_object(v___x_2874_);
lean_dec_ref(v_code_2872_);
lean_dec_ref(v_params_2871_);
lean_del_object(v___x_2859_);
lean_dec(v_discr_2856_);
v_a_2914_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2876_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2876_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
}
else
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
lean_dec(v___x_2870_);
lean_del_object(v___x_2859_);
lean_dec(v_discr_2856_);
v___x_2924_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6);
v___x_2925_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2924_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_);
return v___x_2925_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2(void){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2930_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2931_ = lean_unsigned_to_nat(2u);
v___x_2932_ = lean_unsigned_to_nat(218u);
v___x_2933_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0));
v___x_2934_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2935_ = l_mkPanicMessageWithDecl(v___x_2934_, v___x_2933_, v___x_2932_, v___x_2931_, v___x_2930_);
return v___x_2935_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2937_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__14));
v___x_2938_ = lean_unsigned_to_nat(34u);
v___x_2939_ = lean_unsigned_to_nat(219u);
v___x_2940_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0));
v___x_2941_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2942_ = l_mkPanicMessageWithDecl(v___x_2941_, v___x_2940_, v___x_2939_, v___x_2938_, v___x_2937_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg(lean_object* v_c_2943_, lean_object* v_uintName_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_){
_start:
{
lean_object* v_discr_2951_; lean_object* v_alts_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_3022_; 
v_discr_2951_ = lean_ctor_get(v_c_2943_, 2);
v_alts_2952_ = lean_ctor_get(v_c_2943_, 3);
v_isSharedCheck_3022_ = !lean_is_exclusive(v_c_2943_);
if (v_isSharedCheck_3022_ == 0)
{
lean_object* v_unused_3023_; lean_object* v_unused_3024_; 
v_unused_3023_ = lean_ctor_get(v_c_2943_, 1);
lean_dec(v_unused_3023_);
v_unused_3024_ = lean_ctor_get(v_c_2943_, 0);
lean_dec(v_unused_3024_);
v___x_2954_ = v_c_2943_;
v_isShared_2955_ = v_isSharedCheck_3022_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_alts_2952_);
lean_inc(v_discr_2951_);
lean_dec(v_c_2943_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_3022_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; 
v___x_2956_ = lean_array_get_size(v_alts_2952_);
v___x_2957_ = lean_unsigned_to_nat(1u);
v___x_2958_ = lean_nat_dec_eq(v___x_2956_, v___x_2957_);
if (v___x_2958_ == 0)
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
lean_del_object(v___x_2954_);
lean_dec_ref(v_alts_2952_);
lean_dec(v_discr_2951_);
lean_dec(v_uintName_2944_);
v___x_2959_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2);
v___x_2960_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2959_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_);
return v___x_2960_;
}
else
{
uint8_t v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2961_ = 0;
v___x_2962_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2963_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2964_ = lean_unsigned_to_nat(0u);
v___x_2965_ = lean_array_get(v___x_2963_, v_alts_2952_, v___x_2964_);
lean_dec_ref(v_alts_2952_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_params_2966_; lean_object* v_code_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_3018_; 
v_params_2966_ = lean_ctor_get(v___x_2965_, 1);
v_code_2967_ = lean_ctor_get(v___x_2965_, 2);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_3018_ == 0)
{
lean_object* v_unused_3019_; 
v_unused_3019_ = lean_ctor_get(v___x_2965_, 0);
lean_dec(v_unused_3019_);
v___x_2969_ = v___x_2965_;
v_isShared_2970_ = v_isSharedCheck_3018_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_code_2967_);
lean_inc(v_params_2966_);
lean_dec(v___x_2965_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_3018_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2961_, v_params_2966_, v_a_2947_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v_fvarId_2974_; lean_object* v_binderName_2975_; lean_object* v_lctx_2976_; lean_object* v_nextIdx_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_3009_; 
lean_dec_ref_known(v___x_2971_, 1);
v___x_2972_ = lean_st_ref_take(v_a_2947_);
v___x_2973_ = lean_array_get(v___x_2962_, v_params_2966_, v___x_2964_);
lean_dec_ref(v_params_2966_);
v_fvarId_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_fvarId_2974_);
v_binderName_2975_ = lean_ctor_get(v___x_2973_, 1);
lean_inc(v_binderName_2975_);
lean_dec(v___x_2973_);
v_lctx_2976_ = lean_ctor_get(v___x_2972_, 0);
v_nextIdx_2977_ = lean_ctor_get(v___x_2972_, 1);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_2979_ = v___x_2972_;
v_isShared_2980_ = v_isSharedCheck_3009_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_nextIdx_2977_);
lean_inc(v_lctx_2976_);
lean_dec(v___x_2972_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_3009_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2988_; 
v___x_2981_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3));
v___x_2982_ = l_Lean_Name_str___override(v_uintName_2944_, v___x_2981_);
v___x_2983_ = lean_box(0);
v___x_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2984_, 0, v_discr_2951_);
v___x_2985_ = lean_mk_empty_array_with_capacity(v___x_2957_);
v___x_2986_ = lean_array_push(v___x_2985_, v___x_2984_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set_tag(v___x_2969_, 3);
lean_ctor_set(v___x_2969_, 2, v___x_2986_);
lean_ctor_set(v___x_2969_, 1, v___x_2983_);
lean_ctor_set(v___x_2969_, 0, v___x_2982_);
v___x_2988_ = v___x_2969_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_2982_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v___x_2983_);
lean_ctor_set(v_reuseFailAlloc_3008_, 2, v___x_2986_);
v___x_2988_ = v_reuseFailAlloc_3008_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
lean_object* v___x_2989_; lean_object* v___x_2991_; 
v___x_2989_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 3, v___x_2988_);
lean_ctor_set(v___x_2954_, 2, v___x_2989_);
lean_ctor_set(v___x_2954_, 1, v_binderName_2975_);
lean_ctor_set(v___x_2954_, 0, v_fvarId_2974_);
v___x_2991_ = v___x_2954_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_fvarId_2974_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v_binderName_2975_);
lean_ctor_set(v_reuseFailAlloc_3007_, 2, v___x_2989_);
lean_ctor_set(v_reuseFailAlloc_3007_, 3, v___x_2988_);
v___x_2991_ = v_reuseFailAlloc_3007_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
lean_object* v___x_2992_; lean_object* v___x_2994_; 
lean_inc_ref(v___x_2991_);
v___x_2992_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2961_, v_lctx_2976_, v___x_2991_);
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 0, v___x_2992_);
v___x_2994_ = v___x_2979_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v_nextIdx_2977_);
v___x_2994_ = v_reuseFailAlloc_3006_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2995_ = lean_st_ref_put(v_a_2947_, v___x_2994_);
v___x_2996_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2967_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3005_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2999_ = v___x_2996_;
v_isShared_3000_ = v_isSharedCheck_3005_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2996_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3005_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3001_; lean_object* v___x_3003_; 
v___x_3001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3001_, 0, v___x_2991_);
lean_ctor_set(v___x_3001_, 1, v_a_2997_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 0, v___x_3001_);
v___x_3003_ = v___x_2999_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_3001_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
else
{
lean_dec_ref(v___x_2991_);
return v___x_2996_;
}
}
}
}
}
}
else
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_del_object(v___x_2969_);
lean_dec_ref(v_code_2967_);
lean_dec_ref(v_params_2966_);
lean_del_object(v___x_2954_);
lean_dec(v_discr_2951_);
lean_dec(v_uintName_2944_);
v_a_3010_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_2971_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_2971_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
}
else
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
lean_dec(v___x_2965_);
lean_del_object(v___x_2954_);
lean_dec(v_discr_2951_);
lean_dec(v_uintName_2944_);
v___x_3020_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4);
v___x_3021_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3020_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_);
return v___x_3021_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3025_ = lean_box(0);
v___x_3026_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0));
v___x_3027_ = l_Lean_mkConst(v___x_3026_, v___x_3025_);
return v___x_3027_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3034_ = lean_box(0);
v___x_3035_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3));
v___x_3036_ = l_Lean_mkConst(v___x_3035_, v___x_3034_);
return v___x_3036_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7(void){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3047_ = lean_box(0);
v___x_3048_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6));
v___x_3049_ = l_Lean_mkConst(v___x_3048_, v___x_3047_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(lean_object* v___x_3082_, size_t v_sz_3083_, size_t v_i_3084_, lean_object* v_bs_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
uint8_t v___x_3092_; 
v___x_3092_ = lean_usize_dec_lt(v_i_3084_, v_sz_3083_);
if (v___x_3092_ == 0)
{
lean_object* v___x_3093_; 
lean_dec(v___x_3082_);
v___x_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3093_, 0, v_bs_3085_);
return v___x_3093_;
}
else
{
lean_object* v_v_3094_; lean_object* v___x_3095_; lean_object* v_bs_x27_3096_; lean_object* v_a_3098_; 
v_v_3094_ = lean_array_uget(v_bs_3085_, v_i_3084_);
v___x_3095_ = lean_unsigned_to_nat(0u);
v_bs_x27_3096_ = lean_array_uset(v_bs_3085_, v_i_3084_, v___x_3095_);
if (lean_obj_tag(v_v_3094_) == 0)
{
lean_object* v_ctorName_3103_; lean_object* v_params_3104_; lean_object* v_code_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3232_; 
v_ctorName_3103_ = lean_ctor_get(v_v_3094_, 0);
v_params_3104_ = lean_ctor_get(v_v_3094_, 1);
v_code_3105_ = lean_ctor_get(v_v_3094_, 2);
v_isSharedCheck_3232_ = !lean_is_exclusive(v_v_3094_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3107_ = v_v_3094_;
v_isShared_3108_ = v_isSharedCheck_3232_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_code_3105_);
lean_inc(v_params_3104_);
lean_inc(v_ctorName_3103_);
lean_dec(v_v_3094_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3232_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
uint8_t v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3109_ = 0;
v___x_3110_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_3111_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3109_, v_params_3104_, v___y_3088_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; uint8_t v___x_3116_; 
lean_dec_ref_known(v___x_3111_, 1);
v___x_3112_ = lean_box(0);
v___x_3113_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3114_ = lean_array_get(v___x_3110_, v_params_3104_, v___x_3095_);
lean_dec_ref(v_params_3104_);
v___x_3115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__1));
v___x_3116_ = lean_name_eq(v_ctorName_3103_, v___x_3115_);
lean_dec(v_ctorName_3103_);
if (v___x_3116_ == 0)
{
lean_object* v___x_3117_; lean_object* v_fvarId_3118_; lean_object* v_binderName_3119_; lean_object* v_lctx_3120_; lean_object* v_nextIdx_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3152_; 
v___x_3117_ = lean_st_ref_take(v___y_3088_);
v_fvarId_3118_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_fvarId_3118_);
v_binderName_3119_ = lean_ctor_get(v___x_3114_, 1);
lean_inc(v_binderName_3119_);
lean_dec(v___x_3114_);
v_lctx_3120_ = lean_ctor_get(v___x_3117_, 0);
v_nextIdx_3121_ = lean_ctor_get(v___x_3117_, 1);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3123_ = v___x_3117_;
v_isShared_3124_ = v_isSharedCheck_3152_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_nextIdx_3121_);
lean_inc(v_lctx_3120_);
lean_dec(v___x_3117_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3152_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3133_; 
v___x_3125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__3));
v___x_3126_ = lean_unsigned_to_nat(1u);
v___x_3127_ = lean_mk_empty_array_with_capacity(v___x_3126_);
lean_inc(v___x_3082_);
v___x_3128_ = lean_array_push(v___x_3127_, v___x_3082_);
v___x_3129_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3125_);
lean_ctor_set(v___x_3129_, 1, v___x_3112_);
lean_ctor_set(v___x_3129_, 2, v___x_3128_);
v___x_3130_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3130_, 0, v_fvarId_3118_);
lean_ctor_set(v___x_3130_, 1, v_binderName_3119_);
lean_ctor_set(v___x_3130_, 2, v___x_3113_);
lean_ctor_set(v___x_3130_, 3, v___x_3129_);
lean_inc_ref(v___x_3130_);
v___x_3131_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3109_, v_lctx_3120_, v___x_3130_);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 0, v___x_3131_);
v___x_3133_ = v___x_3123_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___x_3131_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v_nextIdx_3121_);
v___x_3133_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3134_ = lean_st_ref_put(v___y_3088_, v___x_3133_);
v___x_3135_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3105_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3141_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3136_);
lean_dec_ref_known(v___x_3135_, 1);
v___x_3137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__10));
v___x_3138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2));
v___x_3139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3130_);
lean_ctor_set(v___x_3139_, 1, v_a_3136_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 2, v___x_3139_);
lean_ctor_set(v___x_3107_, 1, v___x_3138_);
lean_ctor_set(v___x_3107_, 0, v___x_3137_);
v___x_3141_ = v___x_3107_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3137_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v___x_3138_);
lean_ctor_set(v_reuseFailAlloc_3142_, 2, v___x_3139_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
v_a_3098_ = v___x_3141_;
goto v___jp_3097_;
}
}
else
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
lean_dec_ref_known(v___x_3130_, 4);
lean_del_object(v___x_3107_);
lean_dec_ref(v_bs_x27_3096_);
lean_dec(v___x_3082_);
v_a_3143_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3135_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3135_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
}
}
else
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__5));
v___x_3154_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__3));
v___x_3155_ = lean_unsigned_to_nat(1u);
v___x_3156_ = lean_mk_empty_array_with_capacity(v___x_3155_);
lean_inc(v___x_3082_);
v___x_3157_ = lean_array_push(v___x_3156_, v___x_3082_);
v___x_3158_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3154_);
lean_ctor_set(v___x_3158_, 1, v___x_3112_);
lean_ctor_set(v___x_3158_, 2, v___x_3157_);
v___x_3159_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3109_, v___x_3153_, v___x_3113_, v___x_3158_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref_known(v___x_3159_, 1);
v___x_3161_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__4));
v___x_3162_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6));
v___x_3163_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3109_, v___x_3161_, v___x_3113_, v___x_3162_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v_fvarId_3165_; lean_object* v_fvarId_3166_; lean_object* v___x_3167_; lean_object* v_fvarId_3168_; lean_object* v_binderName_3169_; lean_object* v_lctx_3170_; lean_object* v_nextIdx_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3207_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3164_);
lean_dec_ref_known(v___x_3163_, 1);
v_fvarId_3165_ = lean_ctor_get(v_a_3160_, 0);
v_fvarId_3166_ = lean_ctor_get(v_a_3164_, 0);
v___x_3167_ = lean_st_ref_take(v___y_3088_);
v_fvarId_3168_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_fvarId_3168_);
v_binderName_3169_ = lean_ctor_get(v___x_3114_, 1);
lean_inc(v_binderName_3169_);
lean_dec(v___x_3114_);
v_lctx_3170_ = lean_ctor_get(v___x_3167_, 0);
v_nextIdx_3171_ = lean_ctor_get(v___x_3167_, 1);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3173_ = v___x_3167_;
v_isShared_3174_ = v_isSharedCheck_3207_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_nextIdx_3171_);
lean_inc(v_lctx_3170_);
lean_dec(v___x_3167_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3207_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3186_; 
v___x_3175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__8));
lean_inc(v_fvarId_3165_);
v___x_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3176_, 0, v_fvarId_3165_);
lean_inc(v_fvarId_3166_);
v___x_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3177_, 0, v_fvarId_3166_);
v___x_3178_ = lean_unsigned_to_nat(2u);
v___x_3179_ = lean_mk_empty_array_with_capacity(v___x_3178_);
v___x_3180_ = lean_array_push(v___x_3179_, v___x_3176_);
v___x_3181_ = lean_array_push(v___x_3180_, v___x_3177_);
v___x_3182_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3175_);
lean_ctor_set(v___x_3182_, 1, v___x_3112_);
lean_ctor_set(v___x_3182_, 2, v___x_3181_);
v___x_3183_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3183_, 0, v_fvarId_3168_);
lean_ctor_set(v___x_3183_, 1, v_binderName_3169_);
lean_ctor_set(v___x_3183_, 2, v___x_3113_);
lean_ctor_set(v___x_3183_, 3, v___x_3182_);
lean_inc_ref(v___x_3183_);
v___x_3184_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3109_, v_lctx_3170_, v___x_3183_);
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 0, v___x_3184_);
v___x_3186_ = v___x_3173_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3184_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_nextIdx_3171_);
v___x_3186_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = lean_st_ref_put(v___y_3088_, v___x_3186_);
v___x_3188_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3105_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_a_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3196_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3189_);
lean_dec_ref_known(v___x_3188_, 1);
v___x_3190_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1));
v___x_3191_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2));
v___x_3192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3183_);
lean_ctor_set(v___x_3192_, 1, v_a_3189_);
v___x_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3193_, 0, v_a_3164_);
lean_ctor_set(v___x_3193_, 1, v___x_3192_);
v___x_3194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3194_, 0, v_a_3160_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 2, v___x_3194_);
lean_ctor_set(v___x_3107_, 1, v___x_3191_);
lean_ctor_set(v___x_3107_, 0, v___x_3190_);
v___x_3196_ = v___x_3107_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3190_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v___x_3191_);
lean_ctor_set(v_reuseFailAlloc_3197_, 2, v___x_3194_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
v_a_3098_ = v___x_3196_;
goto v___jp_3097_;
}
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_dec_ref_known(v___x_3183_, 4);
lean_dec(v_a_3164_);
lean_dec(v_a_3160_);
lean_del_object(v___x_3107_);
lean_dec_ref(v_bs_x27_3096_);
lean_dec(v___x_3082_);
v_a_3198_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3188_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3188_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_dec(v_a_3160_);
lean_dec(v___x_3114_);
lean_del_object(v___x_3107_);
lean_dec_ref(v_code_3105_);
lean_dec_ref(v_bs_x27_3096_);
lean_dec(v___x_3082_);
v_a_3208_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3163_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3163_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec(v___x_3114_);
lean_del_object(v___x_3107_);
lean_dec_ref(v_code_3105_);
lean_dec_ref(v_bs_x27_3096_);
lean_dec(v___x_3082_);
v_a_3216_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3159_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3159_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
}
else
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_del_object(v___x_3107_);
lean_dec_ref(v_code_3105_);
lean_dec_ref(v_params_3104_);
lean_dec(v_ctorName_3103_);
lean_dec_ref(v_bs_x27_3096_);
lean_dec(v___x_3082_);
v_a_3224_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3111_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3111_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
}
else
{
lean_object* v_code_3233_; lean_object* v___x_3234_; 
v_code_3233_ = lean_ctor_get(v_v_3094_, 0);
lean_inc_ref(v_code_3233_);
v___x_3234_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3233_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___x_3236_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_a_3235_);
lean_dec_ref_known(v___x_3234_, 1);
v___x_3236_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_3094_, v_a_3235_);
v_a_3098_ = v___x_3236_;
goto v___jp_3097_;
}
else
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
lean_dec_ref_known(v_v_3094_, 1);
lean_dec_ref(v_bs_x27_3096_);
lean_dec(v___x_3082_);
v_a_3237_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3239_ = v___x_3234_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3234_);
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
v___jp_3097_:
{
size_t v___x_3099_; size_t v___x_3100_; lean_object* v___x_3101_; 
v___x_3099_ = ((size_t)1ULL);
v___x_3100_ = lean_usize_add(v_i_3084_, v___x_3099_);
v___x_3101_ = lean_array_uset(v_bs_x27_3096_, v_i_3084_, v_a_3098_);
v_i_3084_ = v___x_3100_;
v_bs_3085_ = v___x_3101_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg(lean_object* v_c_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_){
_start:
{
lean_object* v_resultType_3252_; lean_object* v_discr_3253_; lean_object* v_alts_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3351_; 
v_resultType_3252_ = lean_ctor_get(v_c_3245_, 1);
v_discr_3253_ = lean_ctor_get(v_c_3245_, 2);
v_alts_3254_ = lean_ctor_get(v_c_3245_, 3);
v_isSharedCheck_3351_ = !lean_is_exclusive(v_c_3245_);
if (v_isSharedCheck_3351_ == 0)
{
lean_object* v_unused_3352_; 
v_unused_3352_ = lean_ctor_get(v_c_3245_, 0);
lean_dec(v_unused_3352_);
v___x_3256_ = v_c_3245_;
v_isShared_3257_ = v_isSharedCheck_3351_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_alts_3254_);
lean_inc(v_discr_3253_);
lean_inc(v_resultType_3252_);
lean_dec(v_c_3245_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3351_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3258_; 
v___x_3258_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3252_, v_a_3249_, v_a_3250_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; uint8_t v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_a_3259_);
lean_dec_ref_known(v___x_3258_, 1);
v___x_3260_ = 0;
v___x_3261_ = lean_box(0);
v___x_3262_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3263_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__1));
v___x_3264_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__17));
v___x_3265_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3260_, v___x_3263_, v___x_3262_, v___x_3264_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; lean_object* v_fvarId_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3266_);
lean_dec_ref_known(v___x_3265_, 1);
v_fvarId_3267_ = lean_ctor_get(v_a_3266_, 0);
v___x_3268_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__5));
v___x_3269_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6, &l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6);
v___x_3270_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__8));
lean_inc(v_fvarId_3267_);
v___x_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3271_, 0, v_fvarId_3267_);
v___x_3272_ = lean_unsigned_to_nat(1u);
v___x_3273_ = lean_mk_empty_array_with_capacity(v___x_3272_);
v___x_3274_ = lean_array_push(v___x_3273_, v___x_3271_);
v___x_3275_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3270_);
lean_ctor_set(v___x_3275_, 1, v___x_3261_);
lean_ctor_set(v___x_3275_, 2, v___x_3274_);
v___x_3276_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3260_, v___x_3268_, v___x_3269_, v___x_3275_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; lean_object* v_fvarId_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3277_);
lean_dec_ref_known(v___x_3276_, 1);
v_fvarId_3278_ = lean_ctor_get(v_a_3277_, 0);
v___x_3279_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__10));
v___x_3280_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6));
v___x_3281_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7);
v___x_3282_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12));
v___x_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3283_, 0, v_discr_3253_);
lean_inc(v_fvarId_3278_);
v___x_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3284_, 0, v_fvarId_3278_);
v___x_3285_ = lean_unsigned_to_nat(2u);
v___x_3286_ = lean_mk_empty_array_with_capacity(v___x_3285_);
lean_inc_ref(v___x_3283_);
v___x_3287_ = lean_array_push(v___x_3286_, v___x_3283_);
v___x_3288_ = lean_array_push(v___x_3287_, v___x_3284_);
v___x_3289_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3282_);
lean_ctor_set(v___x_3289_, 1, v___x_3261_);
lean_ctor_set(v___x_3289_, 2, v___x_3288_);
v___x_3290_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3260_, v___x_3279_, v___x_3281_, v___x_3289_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v_a_3291_; size_t v_sz_3292_; size_t v___x_3293_; lean_object* v___x_3294_; 
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
lean_inc(v_a_3291_);
lean_dec_ref_known(v___x_3290_, 1);
v_sz_3292_ = lean_array_size(v_alts_3254_);
v___x_3293_ = ((size_t)0ULL);
v___x_3294_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(v___x_3283_, v_sz_3292_, v___x_3293_, v_alts_3254_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3310_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3297_ = v___x_3294_;
v_isShared_3298_ = v_isSharedCheck_3310_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3310_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v_fvarId_3299_; lean_object* v___x_3301_; 
v_fvarId_3299_ = lean_ctor_get(v_a_3291_, 0);
lean_inc(v_fvarId_3299_);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 3, v_a_3295_);
lean_ctor_set(v___x_3256_, 2, v_fvarId_3299_);
lean_ctor_set(v___x_3256_, 1, v_a_3259_);
lean_ctor_set(v___x_3256_, 0, v___x_3280_);
v___x_3301_ = v___x_3256_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3280_);
lean_ctor_set(v_reuseFailAlloc_3309_, 1, v_a_3259_);
lean_ctor_set(v_reuseFailAlloc_3309_, 2, v_fvarId_3299_);
lean_ctor_set(v_reuseFailAlloc_3309_, 3, v_a_3295_);
v___x_3301_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3307_; 
v___x_3302_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
v___x_3303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3303_, 0, v_a_3291_);
lean_ctor_set(v___x_3303_, 1, v___x_3302_);
v___x_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3304_, 0, v_a_3277_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3305_, 0, v_a_3266_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v___x_3305_);
v___x_3307_ = v___x_3297_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v___x_3305_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
else
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
lean_dec(v_a_3291_);
lean_dec(v_a_3277_);
lean_dec(v_a_3266_);
lean_dec(v_a_3259_);
lean_del_object(v___x_3256_);
v_a_3311_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3313_ = v___x_3294_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3294_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3311_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
}
else
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3326_; 
lean_dec_ref_known(v___x_3283_, 1);
lean_dec(v_a_3277_);
lean_dec(v_a_3266_);
lean_dec(v_a_3259_);
lean_del_object(v___x_3256_);
lean_dec_ref(v_alts_3254_);
v_a_3319_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3321_ = v___x_3290_;
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3290_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3319_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
else
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3334_; 
lean_dec(v_a_3266_);
lean_dec(v_a_3259_);
lean_del_object(v___x_3256_);
lean_dec_ref(v_alts_3254_);
lean_dec(v_discr_3253_);
v_a_3327_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___x_3276_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3276_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3332_; 
if (v_isShared_3330_ == 0)
{
v___x_3332_ = v___x_3329_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
lean_dec(v_a_3259_);
lean_del_object(v___x_3256_);
lean_dec_ref(v_alts_3254_);
lean_dec(v_discr_3253_);
v_a_3335_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3265_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3265_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3340_; 
if (v_isShared_3338_ == 0)
{
v___x_3340_ = v___x_3337_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3335_);
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
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
lean_del_object(v___x_3256_);
lean_dec_ref(v_alts_3254_);
lean_dec(v_discr_3253_);
v_a_3343_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3345_ = v___x_3258_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3258_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
if (v_isShared_3346_ == 0)
{
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3343_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(lean_object* v___x_3362_, size_t v_sz_3363_, size_t v_i_3364_, lean_object* v_bs_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
uint8_t v___x_3372_; 
v___x_3372_ = lean_usize_dec_lt(v_i_3364_, v_sz_3363_);
if (v___x_3372_ == 0)
{
lean_object* v___x_3373_; 
lean_dec(v___x_3362_);
v___x_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3373_, 0, v_bs_3365_);
return v___x_3373_;
}
else
{
lean_object* v_v_3374_; lean_object* v___x_3375_; lean_object* v_bs_x27_3376_; lean_object* v_a_3378_; 
v_v_3374_ = lean_array_uget(v_bs_3365_, v_i_3364_);
v___x_3375_ = lean_unsigned_to_nat(0u);
v_bs_x27_3376_ = lean_array_uset(v_bs_3365_, v_i_3364_, v___x_3375_);
if (lean_obj_tag(v_v_3374_) == 0)
{
lean_object* v_ctorName_3383_; lean_object* v_params_3384_; lean_object* v_code_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3472_; 
v_ctorName_3383_ = lean_ctor_get(v_v_3374_, 0);
v_params_3384_ = lean_ctor_get(v_v_3374_, 1);
v_code_3385_ = lean_ctor_get(v_v_3374_, 2);
v_isSharedCheck_3472_ = !lean_is_exclusive(v_v_3374_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3387_ = v_v_3374_;
v_isShared_3388_ = v_isSharedCheck_3472_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_code_3385_);
lean_inc(v_params_3384_);
lean_inc(v_ctorName_3383_);
lean_dec(v_v_3374_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3472_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
uint8_t v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3389_ = 0;
v___x_3390_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_3391_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3389_, v_params_3384_, v___y_3368_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v___x_3392_; uint8_t v___x_3393_; 
lean_dec_ref_known(v___x_3391_, 1);
v___x_3392_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__9));
v___x_3393_ = lean_name_eq(v_ctorName_3383_, v___x_3392_);
lean_dec(v_ctorName_3383_);
if (v___x_3393_ == 0)
{
lean_object* v___x_3394_; 
lean_dec_ref(v_params_3384_);
v___x_3394_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3385_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3399_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_a_3395_);
lean_dec_ref_known(v___x_3394_, 1);
v___x_3396_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1));
v___x_3397_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2));
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 2, v_a_3395_);
lean_ctor_set(v___x_3387_, 1, v___x_3397_);
lean_ctor_set(v___x_3387_, 0, v___x_3396_);
v___x_3399_ = v___x_3387_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3396_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v___x_3397_);
lean_ctor_set(v_reuseFailAlloc_3400_, 2, v_a_3395_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
v_a_3378_ = v___x_3399_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
lean_del_object(v___x_3387_);
lean_dec_ref(v_bs_x27_3376_);
lean_dec(v___x_3362_);
v_a_3401_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3394_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3394_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3401_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
else
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3409_ = lean_box(0);
v___x_3410_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3411_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__4));
v___x_3412_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6));
v___x_3413_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3389_, v___x_3411_, v___x_3410_, v___x_3412_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v_fvarId_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v_fvarId_3418_; lean_object* v_binderName_3419_; lean_object* v_lctx_3420_; lean_object* v_nextIdx_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3455_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
lean_dec_ref_known(v___x_3413_, 1);
v_fvarId_3415_ = lean_ctor_get(v_a_3414_, 0);
v___x_3416_ = lean_st_ref_take(v___y_3368_);
v___x_3417_ = lean_array_get(v___x_3390_, v_params_3384_, v___x_3375_);
lean_dec_ref(v_params_3384_);
v_fvarId_3418_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_fvarId_3418_);
v_binderName_3419_ = lean_ctor_get(v___x_3417_, 1);
lean_inc(v_binderName_3419_);
lean_dec(v___x_3417_);
v_lctx_3420_ = lean_ctor_get(v___x_3416_, 0);
v_nextIdx_3421_ = lean_ctor_get(v___x_3416_, 1);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3423_ = v___x_3416_;
v_isShared_3424_ = v_isSharedCheck_3455_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_nextIdx_3421_);
lean_inc(v_lctx_3420_);
lean_dec(v___x_3416_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3455_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3435_; 
v___x_3425_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__8));
lean_inc(v_fvarId_3415_);
v___x_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3426_, 0, v_fvarId_3415_);
v___x_3427_ = lean_unsigned_to_nat(2u);
v___x_3428_ = lean_mk_empty_array_with_capacity(v___x_3427_);
lean_inc(v___x_3362_);
v___x_3429_ = lean_array_push(v___x_3428_, v___x_3362_);
v___x_3430_ = lean_array_push(v___x_3429_, v___x_3426_);
v___x_3431_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3425_);
lean_ctor_set(v___x_3431_, 1, v___x_3409_);
lean_ctor_set(v___x_3431_, 2, v___x_3430_);
v___x_3432_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3432_, 0, v_fvarId_3418_);
lean_ctor_set(v___x_3432_, 1, v_binderName_3419_);
lean_ctor_set(v___x_3432_, 2, v___x_3410_);
lean_ctor_set(v___x_3432_, 3, v___x_3431_);
lean_inc_ref(v___x_3432_);
v___x_3433_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3389_, v_lctx_3420_, v___x_3432_);
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 0, v___x_3433_);
v___x_3435_ = v___x_3423_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3433_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_nextIdx_3421_);
v___x_3435_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = lean_st_ref_put(v___y_3368_, v___x_3435_);
v___x_3437_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3385_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3444_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref_known(v___x_3437_, 1);
v___x_3439_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__10));
v___x_3440_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2));
v___x_3441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3432_);
lean_ctor_set(v___x_3441_, 1, v_a_3438_);
v___x_3442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3442_, 0, v_a_3414_);
lean_ctor_set(v___x_3442_, 1, v___x_3441_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 2, v___x_3442_);
lean_ctor_set(v___x_3387_, 1, v___x_3440_);
lean_ctor_set(v___x_3387_, 0, v___x_3439_);
v___x_3444_ = v___x_3387_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3439_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v___x_3440_);
lean_ctor_set(v_reuseFailAlloc_3445_, 2, v___x_3442_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
v_a_3378_ = v___x_3444_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
lean_dec_ref_known(v___x_3432_, 4);
lean_dec(v_a_3414_);
lean_del_object(v___x_3387_);
lean_dec_ref(v_bs_x27_3376_);
lean_dec(v___x_3362_);
v_a_3446_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3437_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3437_);
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
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
lean_del_object(v___x_3387_);
lean_dec_ref(v_code_3385_);
lean_dec_ref(v_params_3384_);
lean_dec_ref(v_bs_x27_3376_);
lean_dec(v___x_3362_);
v_a_3456_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3413_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3413_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_del_object(v___x_3387_);
lean_dec_ref(v_code_3385_);
lean_dec_ref(v_params_3384_);
lean_dec(v_ctorName_3383_);
lean_dec_ref(v_bs_x27_3376_);
lean_dec(v___x_3362_);
v_a_3464_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3391_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3391_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
}
else
{
lean_object* v_code_3473_; lean_object* v___x_3474_; 
v_code_3473_ = lean_ctor_get(v_v_3374_, 0);
lean_inc_ref(v_code_3473_);
v___x_3474_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3473_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; lean_object* v___x_3476_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3475_);
lean_dec_ref_known(v___x_3474_, 1);
v___x_3476_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_3374_, v_a_3475_);
v_a_3378_ = v___x_3476_;
goto v___jp_3377_;
}
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
lean_dec_ref_known(v_v_3374_, 1);
lean_dec_ref(v_bs_x27_3376_);
lean_dec(v___x_3362_);
v_a_3477_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3474_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3474_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
v___jp_3377_:
{
size_t v___x_3379_; size_t v___x_3380_; lean_object* v___x_3381_; 
v___x_3379_ = ((size_t)1ULL);
v___x_3380_ = lean_usize_add(v_i_3364_, v___x_3379_);
v___x_3381_ = lean_array_uset(v_bs_x27_3376_, v_i_3364_, v_a_3378_);
v_i_3364_ = v___x_3380_;
v_bs_3365_ = v___x_3381_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg(lean_object* v_c_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_){
_start:
{
lean_object* v_resultType_3492_; lean_object* v_discr_3493_; lean_object* v_alts_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3571_; 
v_resultType_3492_ = lean_ctor_get(v_c_3485_, 1);
v_discr_3493_ = lean_ctor_get(v_c_3485_, 2);
v_alts_3494_ = lean_ctor_get(v_c_3485_, 3);
v_isSharedCheck_3571_ = !lean_is_exclusive(v_c_3485_);
if (v_isSharedCheck_3571_ == 0)
{
lean_object* v_unused_3572_; 
v_unused_3572_ = lean_ctor_get(v_c_3485_, 0);
lean_dec(v_unused_3572_);
v___x_3496_ = v_c_3485_;
v_isShared_3497_ = v_isSharedCheck_3571_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_alts_3494_);
lean_inc(v_discr_3493_);
lean_inc(v_resultType_3492_);
lean_dec(v_c_3485_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3571_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3492_, v_a_3489_, v_a_3490_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; uint8_t v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3499_);
lean_dec_ref_known(v___x_3498_, 1);
v___x_3500_ = 0;
v___x_3501_ = lean_box(0);
v___x_3502_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3503_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__2));
v___x_3504_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__17));
v___x_3505_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3500_, v___x_3503_, v___x_3502_, v___x_3504_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; lean_object* v_fvarId_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3506_);
lean_dec_ref_known(v___x_3505_, 1);
v_fvarId_3507_ = lean_ctor_get(v_a_3506_, 0);
v___x_3508_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__4));
v___x_3509_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6));
v___x_3510_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7);
v___x_3511_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__9));
v___x_3512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3512_, 0, v_discr_3493_);
lean_inc(v_fvarId_3507_);
v___x_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3513_, 0, v_fvarId_3507_);
v___x_3514_ = lean_unsigned_to_nat(2u);
v___x_3515_ = lean_mk_empty_array_with_capacity(v___x_3514_);
lean_inc_ref(v___x_3512_);
v___x_3516_ = lean_array_push(v___x_3515_, v___x_3512_);
v___x_3517_ = lean_array_push(v___x_3516_, v___x_3513_);
v___x_3518_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3511_);
lean_ctor_set(v___x_3518_, 1, v___x_3501_);
lean_ctor_set(v___x_3518_, 2, v___x_3517_);
v___x_3519_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3500_, v___x_3508_, v___x_3510_, v___x_3518_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; size_t v_sz_3521_; size_t v___x_3522_; lean_object* v___x_3523_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref_known(v___x_3519_, 1);
v_sz_3521_ = lean_array_size(v_alts_3494_);
v___x_3522_ = ((size_t)0ULL);
v___x_3523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(v___x_3512_, v_sz_3521_, v___x_3522_, v_alts_3494_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3538_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3526_ = v___x_3523_;
v_isShared_3527_ = v_isSharedCheck_3538_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3523_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3538_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v_fvarId_3528_; lean_object* v___x_3530_; 
v_fvarId_3528_ = lean_ctor_get(v_a_3520_, 0);
lean_inc(v_fvarId_3528_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 3, v_a_3524_);
lean_ctor_set(v___x_3496_, 2, v_fvarId_3528_);
lean_ctor_set(v___x_3496_, 1, v_a_3499_);
lean_ctor_set(v___x_3496_, 0, v___x_3509_);
v___x_3530_ = v___x_3496_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3509_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_a_3499_);
lean_ctor_set(v_reuseFailAlloc_3537_, 2, v_fvarId_3528_);
lean_ctor_set(v_reuseFailAlloc_3537_, 3, v_a_3524_);
v___x_3530_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3535_; 
v___x_3531_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3530_);
v___x_3532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3532_, 0, v_a_3520_);
lean_ctor_set(v___x_3532_, 1, v___x_3531_);
v___x_3533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3533_, 0, v_a_3506_);
lean_ctor_set(v___x_3533_, 1, v___x_3532_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 0, v___x_3533_);
v___x_3535_ = v___x_3526_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3533_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec(v_a_3520_);
lean_dec(v_a_3506_);
lean_dec(v_a_3499_);
lean_del_object(v___x_3496_);
v_a_3539_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3523_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3523_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
else
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3554_; 
lean_dec_ref_known(v___x_3512_, 1);
lean_dec(v_a_3506_);
lean_dec(v_a_3499_);
lean_del_object(v___x_3496_);
lean_dec_ref(v_alts_3494_);
v_a_3547_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___x_3519_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3519_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3552_; 
if (v_isShared_3550_ == 0)
{
v___x_3552_ = v___x_3549_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_a_3547_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
lean_dec(v_a_3499_);
lean_del_object(v___x_3496_);
lean_dec_ref(v_alts_3494_);
lean_dec(v_discr_3493_);
v_a_3555_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___x_3505_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3505_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
if (v_isShared_3558_ == 0)
{
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3555_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_del_object(v___x_3496_);
lean_dec_ref(v_alts_3494_);
lean_dec(v_discr_3493_);
v_a_3563_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3498_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3498_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono(lean_object* v_code_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_){
_start:
{
lean_object* v_decl_3581_; lean_object* v_k_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; 
switch(lean_obj_tag(v_code_3573_))
{
case 0:
{
lean_object* v_decl_3697_; lean_object* v_k_3698_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v_value_3754_; 
v_decl_3697_ = lean_ctor_get(v_code_3573_, 0);
v_k_3698_ = lean_ctor_get(v_code_3573_, 1);
v_value_3754_ = lean_ctor_get(v_decl_3697_, 3);
lean_inc(v_value_3754_);
if (lean_obj_tag(v_value_3754_) == 3)
{
lean_object* v_declName_3755_; 
v_declName_3755_ = lean_ctor_get(v_value_3754_, 0);
lean_inc(v_declName_3755_);
if (lean_obj_tag(v_declName_3755_) == 1)
{
lean_object* v_pre_3756_; 
v_pre_3756_ = lean_ctor_get(v_declName_3755_, 0);
lean_inc(v_pre_3756_);
if (lean_obj_tag(v_pre_3756_) == 1)
{
lean_object* v_pre_3757_; 
v_pre_3757_ = lean_ctor_get(v_pre_3756_, 0);
if (lean_obj_tag(v_pre_3757_) == 0)
{
lean_object* v_type_3758_; lean_object* v_args_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3829_; 
v_type_3758_ = lean_ctor_get(v_decl_3697_, 2);
v_args_3759_ = lean_ctor_get(v_value_3754_, 2);
v_isSharedCheck_3829_ = !lean_is_exclusive(v_value_3754_);
if (v_isSharedCheck_3829_ == 0)
{
lean_object* v_unused_3830_; lean_object* v_unused_3831_; 
v_unused_3830_ = lean_ctor_get(v_value_3754_, 1);
lean_dec(v_unused_3830_);
v_unused_3831_ = lean_ctor_get(v_value_3754_, 0);
lean_dec(v_unused_3831_);
v___x_3761_ = v_value_3754_;
v_isShared_3762_ = v_isSharedCheck_3829_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_args_3759_);
lean_dec(v_value_3754_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3829_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v_str_3763_; lean_object* v_str_3764_; lean_object* v___x_3765_; uint8_t v___x_3766_; 
v_str_3763_ = lean_ctor_get(v_declName_3755_, 1);
lean_inc_ref(v_str_3763_);
lean_dec_ref_known(v_declName_3755_, 2);
v_str_3764_ = lean_ctor_get(v_pre_3756_, 1);
lean_inc_ref(v_str_3764_);
lean_dec_ref_known(v_pre_3756_, 2);
v___x_3765_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__5));
v___x_3766_ = lean_string_dec_eq(v_str_3764_, v___x_3765_);
lean_dec_ref(v_str_3764_);
if (v___x_3766_ == 0)
{
lean_dec_ref(v_str_3763_);
lean_del_object(v___x_3761_);
lean_dec_ref(v_args_3759_);
v___y_3700_ = v_a_3574_;
v___y_3701_ = v_a_3575_;
v___y_3702_ = v_a_3576_;
v___y_3703_ = v_a_3577_;
v___y_3704_ = v_a_3578_;
goto v___jp_3699_;
}
else
{
lean_object* v___x_3767_; uint8_t v___x_3768_; 
v___x_3767_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__8));
v___x_3768_ = lean_string_dec_eq(v_str_3763_, v___x_3767_);
lean_dec_ref(v_str_3763_);
if (v___x_3768_ == 0)
{
lean_del_object(v___x_3761_);
lean_dec_ref(v_args_3759_);
v___y_3700_ = v_a_3574_;
v___y_3701_ = v_a_3575_;
v___y_3702_ = v_a_3576_;
v___y_3703_ = v_a_3577_;
v___y_3704_ = v_a_3578_;
goto v___jp_3699_;
}
else
{
lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3826_; 
lean_inc_ref(v_type_3758_);
lean_inc_ref(v_k_3698_);
lean_inc_ref(v_decl_3697_);
v_isSharedCheck_3826_ = !lean_is_exclusive(v_code_3573_);
if (v_isSharedCheck_3826_ == 0)
{
lean_object* v_unused_3827_; lean_object* v_unused_3828_; 
v_unused_3827_ = lean_ctor_get(v_code_3573_, 1);
lean_dec(v_unused_3827_);
v_unused_3828_ = lean_ctor_get(v_code_3573_, 0);
lean_dec(v_unused_3828_);
v___x_3770_ = v_code_3573_;
v_isShared_3771_ = v_isSharedCheck_3826_;
goto v_resetjp_3769_;
}
else
{
lean_dec(v_code_3573_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3826_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; uint8_t v___x_3774_; 
v___x_3772_ = lean_array_get_size(v_args_3759_);
v___x_3773_ = lean_unsigned_to_nat(1u);
v___x_3774_ = lean_nat_dec_eq(v___x_3772_, v___x_3773_);
if (v___x_3774_ == 0)
{
lean_object* v___x_3775_; lean_object* v___x_3776_; 
lean_del_object(v___x_3770_);
lean_del_object(v___x_3761_);
lean_dec_ref(v_args_3759_);
lean_dec_ref(v_type_3758_);
lean_dec_ref(v_k_3698_);
lean_dec_ref(v_decl_3697_);
v___x_3775_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__5, &l_Lean_Compiler_LCNF_Code_toMono___closed__5_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__5);
v___x_3776_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3775_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
return v___x_3776_;
}
else
{
uint8_t v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3777_ = 0;
v___x_3778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6));
v___x_3779_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3));
v___x_3780_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_3777_, v___x_3778_, v___x_3779_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v_a_3781_; lean_object* v_fvarId_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3793_; 
v_a_3781_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_a_3781_);
lean_dec_ref_known(v___x_3780_, 1);
v_fvarId_3782_ = lean_ctor_get(v_a_3781_, 0);
v___x_3783_ = lean_unsigned_to_nat(0u);
v___x_3784_ = lean_array_fget(v_args_3759_, v___x_3783_);
lean_dec_ref(v_args_3759_);
v___x_3785_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__7));
v___x_3786_ = lean_box(0);
lean_inc(v_fvarId_3782_);
v___x_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3787_, 0, v_fvarId_3782_);
v___x_3788_ = lean_unsigned_to_nat(2u);
v___x_3789_ = lean_mk_empty_array_with_capacity(v___x_3788_);
v___x_3790_ = lean_array_push(v___x_3789_, v___x_3784_);
v___x_3791_ = lean_array_push(v___x_3790_, v___x_3787_);
if (v_isShared_3762_ == 0)
{
lean_ctor_set(v___x_3761_, 2, v___x_3791_);
lean_ctor_set(v___x_3761_, 1, v___x_3786_);
lean_ctor_set(v___x_3761_, 0, v___x_3785_);
v___x_3793_ = v___x_3761_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3785_);
lean_ctor_set(v_reuseFailAlloc_3817_, 1, v___x_3786_);
lean_ctor_set(v_reuseFailAlloc_3817_, 2, v___x_3791_);
v___x_3793_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
lean_object* v___x_3794_; 
v___x_3794_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_3777_, v_decl_3697_, v_type_3758_, v___x_3793_, v_a_3576_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_a_3795_; lean_object* v___x_3796_; 
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3795_);
lean_dec_ref_known(v___x_3794_, 1);
v___x_3796_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3698_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3808_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3799_ = v___x_3796_;
v_isShared_3800_ = v_isSharedCheck_3808_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3796_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3808_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 1, v_a_3797_);
lean_ctor_set(v___x_3770_, 0, v_a_3795_);
v___x_3802_ = v___x_3770_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3795_);
lean_ctor_set(v_reuseFailAlloc_3807_, 1, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
lean_object* v___x_3803_; lean_object* v___x_3805_; 
v___x_3803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3803_, 0, v_a_3781_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
if (v_isShared_3800_ == 0)
{
lean_ctor_set(v___x_3799_, 0, v___x_3803_);
v___x_3805_ = v___x_3799_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3803_);
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
lean_dec(v_a_3795_);
lean_dec(v_a_3781_);
lean_del_object(v___x_3770_);
return v___x_3796_;
}
}
else
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
lean_dec(v_a_3781_);
lean_del_object(v___x_3770_);
lean_dec_ref(v_k_3698_);
v_a_3809_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___x_3794_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3794_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3809_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_del_object(v___x_3770_);
lean_del_object(v___x_3761_);
lean_dec_ref(v_args_3759_);
lean_dec_ref(v_type_3758_);
lean_dec_ref(v_k_3698_);
lean_dec_ref(v_decl_3697_);
v_a_3818_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3780_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3780_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
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
lean_dec_ref_known(v_pre_3756_, 2);
lean_dec_ref_known(v_declName_3755_, 2);
lean_dec_ref_known(v_value_3754_, 3);
v___y_3700_ = v_a_3574_;
v___y_3701_ = v_a_3575_;
v___y_3702_ = v_a_3576_;
v___y_3703_ = v_a_3577_;
v___y_3704_ = v_a_3578_;
goto v___jp_3699_;
}
}
else
{
lean_dec(v_pre_3756_);
lean_dec_ref_known(v_declName_3755_, 2);
lean_dec_ref_known(v_value_3754_, 3);
v___y_3700_ = v_a_3574_;
v___y_3701_ = v_a_3575_;
v___y_3702_ = v_a_3576_;
v___y_3703_ = v_a_3577_;
v___y_3704_ = v_a_3578_;
goto v___jp_3699_;
}
}
else
{
lean_dec_ref_known(v_value_3754_, 3);
lean_dec(v_declName_3755_);
v___y_3700_ = v_a_3574_;
v___y_3701_ = v_a_3575_;
v___y_3702_ = v_a_3576_;
v___y_3703_ = v_a_3577_;
v___y_3704_ = v_a_3578_;
goto v___jp_3699_;
}
}
else
{
lean_dec(v_value_3754_);
v___y_3700_ = v_a_3574_;
v___y_3701_ = v_a_3575_;
v___y_3702_ = v_a_3576_;
v___y_3703_ = v_a_3577_;
v___y_3704_ = v_a_3578_;
goto v___jp_3699_;
}
v___jp_3699_:
{
lean_object* v___x_3705_; 
lean_inc_ref(v_decl_3697_);
v___x_3705_ = l_Lean_Compiler_LCNF_LetDecl_toMono(v_decl_3697_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; lean_object* v___x_3707_; 
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_a_3706_);
lean_dec_ref_known(v___x_3705_, 1);
lean_inc_ref(v_k_3698_);
v___x_3707_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3698_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3745_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3710_ = v___x_3707_;
v_isShared_3711_ = v_isSharedCheck_3745_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3707_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3745_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
size_t v___x_3712_; size_t v___x_3713_; uint8_t v___x_3714_; 
v___x_3712_ = lean_ptr_addr(v_k_3698_);
v___x_3713_ = lean_ptr_addr(v_a_3708_);
v___x_3714_ = lean_usize_dec_eq(v___x_3712_, v___x_3713_);
if (v___x_3714_ == 0)
{
lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3724_; 
v_isSharedCheck_3724_ = !lean_is_exclusive(v_code_3573_);
if (v_isSharedCheck_3724_ == 0)
{
lean_object* v_unused_3725_; lean_object* v_unused_3726_; 
v_unused_3725_ = lean_ctor_get(v_code_3573_, 1);
lean_dec(v_unused_3725_);
v_unused_3726_ = lean_ctor_get(v_code_3573_, 0);
lean_dec(v_unused_3726_);
v___x_3716_ = v_code_3573_;
v_isShared_3717_ = v_isSharedCheck_3724_;
goto v_resetjp_3715_;
}
else
{
lean_dec(v_code_3573_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3724_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3719_; 
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 1, v_a_3708_);
lean_ctor_set(v___x_3716_, 0, v_a_3706_);
v___x_3719_ = v___x_3716_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3706_);
lean_ctor_set(v_reuseFailAlloc_3723_, 1, v_a_3708_);
v___x_3719_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
lean_object* v___x_3721_; 
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 0, v___x_3719_);
v___x_3721_ = v___x_3710_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3719_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
else
{
size_t v___x_3727_; size_t v___x_3728_; uint8_t v___x_3729_; 
v___x_3727_ = lean_ptr_addr(v_decl_3697_);
v___x_3728_ = lean_ptr_addr(v_a_3706_);
v___x_3729_ = lean_usize_dec_eq(v___x_3727_, v___x_3728_);
if (v___x_3729_ == 0)
{
lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3739_; 
v_isSharedCheck_3739_ = !lean_is_exclusive(v_code_3573_);
if (v_isSharedCheck_3739_ == 0)
{
lean_object* v_unused_3740_; lean_object* v_unused_3741_; 
v_unused_3740_ = lean_ctor_get(v_code_3573_, 1);
lean_dec(v_unused_3740_);
v_unused_3741_ = lean_ctor_get(v_code_3573_, 0);
lean_dec(v_unused_3741_);
v___x_3731_ = v_code_3573_;
v_isShared_3732_ = v_isSharedCheck_3739_;
goto v_resetjp_3730_;
}
else
{
lean_dec(v_code_3573_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3739_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
if (v_isShared_3732_ == 0)
{
lean_ctor_set(v___x_3731_, 1, v_a_3708_);
lean_ctor_set(v___x_3731_, 0, v_a_3706_);
v___x_3734_ = v___x_3731_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3706_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v_a_3708_);
v___x_3734_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
lean_object* v___x_3736_; 
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 0, v___x_3734_);
v___x_3736_ = v___x_3710_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3734_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
else
{
lean_object* v___x_3743_; 
lean_dec(v_a_3708_);
lean_dec(v_a_3706_);
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 0, v_code_3573_);
v___x_3743_ = v___x_3710_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_code_3573_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
}
else
{
lean_dec(v_a_3706_);
lean_dec_ref_known(v_code_3573_, 2);
return v___x_3707_;
}
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_dec_ref_known(v_code_3573_, 2);
v_a_3746_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3705_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3705_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_3832_; lean_object* v_args_3833_; size_t v_sz_3834_; size_t v___x_3835_; lean_object* v___x_3836_; 
v_fvarId_3832_ = lean_ctor_get(v_code_3573_, 0);
v_args_3833_ = lean_ctor_get(v_code_3573_, 1);
v_sz_3834_ = lean_array_size(v_args_3833_);
v___x_3835_ = ((size_t)0ULL);
lean_inc_ref(v_args_3833_);
v___x_3836_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_3834_, v___x_3835_, v_args_3833_, v_a_3574_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3862_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3839_ = v___x_3836_;
v_isShared_3840_ = v_isSharedCheck_3862_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3836_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3862_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
uint8_t v___y_3842_; uint8_t v___x_3858_; 
v___x_3858_ = l_Lean_instBEqFVarId_beq(v_fvarId_3832_, v_fvarId_3832_);
if (v___x_3858_ == 0)
{
v___y_3842_ = v___x_3858_;
goto v___jp_3841_;
}
else
{
size_t v___x_3859_; size_t v___x_3860_; uint8_t v___x_3861_; 
v___x_3859_ = lean_ptr_addr(v_args_3833_);
v___x_3860_ = lean_ptr_addr(v_a_3837_);
v___x_3861_ = lean_usize_dec_eq(v___x_3859_, v___x_3860_);
v___y_3842_ = v___x_3861_;
goto v___jp_3841_;
}
v___jp_3841_:
{
if (v___y_3842_ == 0)
{
lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3852_; 
lean_inc(v_fvarId_3832_);
v_isSharedCheck_3852_ = !lean_is_exclusive(v_code_3573_);
if (v_isSharedCheck_3852_ == 0)
{
lean_object* v_unused_3853_; lean_object* v_unused_3854_; 
v_unused_3853_ = lean_ctor_get(v_code_3573_, 1);
lean_dec(v_unused_3853_);
v_unused_3854_ = lean_ctor_get(v_code_3573_, 0);
lean_dec(v_unused_3854_);
v___x_3844_ = v_code_3573_;
v_isShared_3845_ = v_isSharedCheck_3852_;
goto v_resetjp_3843_;
}
else
{
lean_dec(v_code_3573_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3852_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
lean_ctor_set(v___x_3844_, 1, v_a_3837_);
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_fvarId_3832_);
lean_ctor_set(v_reuseFailAlloc_3851_, 1, v_a_3837_);
v___x_3847_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
lean_object* v___x_3849_; 
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v___x_3847_);
v___x_3849_ = v___x_3839_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3847_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
else
{
lean_object* v___x_3856_; 
lean_dec(v_a_3837_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v_code_3573_);
v___x_3856_ = v___x_3839_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_code_3573_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
}
}
else
{
lean_object* v_a_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3870_; 
lean_dec_ref_known(v_code_3573_, 2);
v_a_3863_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3865_ = v___x_3836_;
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_a_3863_);
lean_dec(v___x_3836_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
case 4:
{
lean_object* v_cases_3871_; lean_object* v_typeName_3872_; lean_object* v_resultType_3873_; lean_object* v_discr_3874_; lean_object* v_alts_3875_; lean_object* v___x_3876_; uint8_t v___x_3877_; 
v_cases_3871_ = lean_ctor_get(v_code_3573_, 0);
lean_inc_ref(v_cases_3871_);
v_typeName_3872_ = lean_ctor_get(v_cases_3871_, 0);
v_resultType_3873_ = lean_ctor_get(v_cases_3871_, 1);
v_discr_3874_ = lean_ctor_get(v_cases_3871_, 2);
v_alts_3875_ = lean_ctor_get(v_cases_3871_, 3);
v___x_3876_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0));
v___x_3877_ = lean_name_eq(v_typeName_3872_, v___x_3876_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; uint8_t v___x_3879_; 
v___x_3878_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3));
v___x_3879_ = lean_name_eq(v_typeName_3872_, v___x_3878_);
if (v___x_3879_ == 0)
{
lean_object* v___x_3880_; uint8_t v___x_3881_; 
v___x_3880_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__9));
v___x_3881_ = lean_name_eq(v_typeName_3872_, v___x_3880_);
if (v___x_3881_ == 0)
{
lean_object* v___x_3882_; uint8_t v___x_3883_; 
v___x_3882_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__11));
v___x_3883_ = lean_name_eq(v_typeName_3872_, v___x_3882_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3884_; uint8_t v___x_3885_; 
v___x_3884_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__13));
v___x_3885_ = lean_name_eq(v_typeName_3872_, v___x_3884_);
if (v___x_3885_ == 0)
{
lean_object* v___x_3886_; uint8_t v___x_3887_; 
v___x_3886_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__15));
v___x_3887_ = lean_name_eq(v_typeName_3872_, v___x_3886_);
if (v___x_3887_ == 0)
{
lean_object* v___x_3888_; uint8_t v___x_3889_; 
v___x_3888_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__16));
v___x_3889_ = lean_name_eq(v_typeName_3872_, v___x_3888_);
if (v___x_3889_ == 0)
{
lean_object* v___x_3890_; uint8_t v___x_3891_; 
v___x_3890_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__17));
v___x_3891_ = lean_name_eq(v_typeName_3872_, v___x_3890_);
if (v___x_3891_ == 0)
{
lean_object* v___x_3892_; uint8_t v___x_3893_; 
v___x_3892_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__18));
v___x_3893_ = lean_name_eq(v_typeName_3872_, v___x_3892_);
if (v___x_3893_ == 0)
{
lean_object* v___x_3894_; uint8_t v___x_3895_; 
v___x_3894_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__19));
v___x_3895_ = lean_name_eq(v_typeName_3872_, v___x_3894_);
if (v___x_3895_ == 0)
{
lean_object* v___x_3896_; uint8_t v___x_3897_; 
v___x_3896_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__20));
v___x_3897_ = lean_name_eq(v_typeName_3872_, v___x_3896_);
if (v___x_3897_ == 0)
{
lean_object* v___x_3898_; uint8_t v___x_3899_; 
v___x_3898_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__21));
v___x_3899_ = lean_name_eq(v_typeName_3872_, v___x_3898_);
if (v___x_3899_ == 0)
{
lean_object* v___x_3900_; uint8_t v___x_3901_; 
v___x_3900_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__22));
v___x_3901_ = lean_name_eq(v_typeName_3872_, v___x_3900_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; uint8_t v___x_3903_; 
v___x_3902_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__23));
v___x_3903_ = lean_name_eq(v_typeName_3872_, v___x_3902_);
if (v___x_3903_ == 0)
{
lean_object* v___x_3904_; 
lean_inc(v_typeName_3872_);
v___x_3904_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_typeName_3872_, v_a_3577_, v_a_3578_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_a_3905_);
lean_dec_ref_known(v___x_3904_, 1);
if (lean_obj_tag(v_a_3905_) == 1)
{
lean_object* v_val_3906_; lean_object* v___x_3907_; 
lean_dec_ref_known(v_code_3573_, 1);
v_val_3906_ = lean_ctor_get(v_a_3905_, 0);
lean_inc(v_val_3906_);
lean_dec_ref_known(v_a_3905_, 1);
v___x_3907_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_val_3906_, v_cases_3871_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
lean_dec(v_val_3906_);
return v___x_3907_;
}
else
{
lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3998_; 
lean_inc_ref(v_alts_3875_);
lean_inc(v_discr_3874_);
lean_inc_ref(v_resultType_3873_);
lean_inc(v_typeName_3872_);
lean_dec(v_a_3905_);
v_isSharedCheck_3998_ = !lean_is_exclusive(v_cases_3871_);
if (v_isSharedCheck_3998_ == 0)
{
lean_object* v_unused_3999_; lean_object* v_unused_4000_; lean_object* v_unused_4001_; lean_object* v_unused_4002_; 
v_unused_3999_ = lean_ctor_get(v_cases_3871_, 3);
lean_dec(v_unused_3999_);
v_unused_4000_ = lean_ctor_get(v_cases_3871_, 2);
lean_dec(v_unused_4000_);
v_unused_4001_ = lean_ctor_get(v_cases_3871_, 1);
lean_dec(v_unused_4001_);
v_unused_4002_ = lean_ctor_get(v_cases_3871_, 0);
lean_dec(v_unused_4002_);
v___x_3909_ = v_cases_3871_;
v_isShared_3910_ = v_isSharedCheck_3998_;
goto v_resetjp_3908_;
}
else
{
lean_dec(v_cases_3871_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3998_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3911_; 
lean_inc_ref(v_resultType_3873_);
v___x_3911_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3873_, v_a_3577_, v_a_3578_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3989_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3914_ = v___x_3911_;
v_isShared_3915_ = v_isSharedCheck_3989_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3911_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3989_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3916_; lean_object* v_env_3917_; lean_object* v___x_3944_; 
v___x_3916_ = lean_st_ref_get(v_a_3578_);
v_env_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc_ref_n(v_env_3917_, 2);
lean_dec(v___x_3916_);
lean_inc(v_typeName_3872_);
v___x_3944_ = l_Lean_Environment_find_x3f(v_env_3917_, v_typeName_3872_, v___x_3903_);
if (lean_obj_tag(v___x_3944_) == 1)
{
lean_object* v_val_3945_; 
v_val_3945_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_val_3945_);
lean_dec_ref_known(v___x_3944_, 1);
if (lean_obj_tag(v_val_3945_) == 5)
{
lean_object* v_val_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3988_; 
v_val_3946_ = lean_ctor_get(v_val_3945_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v_val_3945_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3948_ = v_val_3945_;
v_isShared_3949_ = v_isSharedCheck_3988_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_val_3946_);
lean_dec(v_val_3945_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3988_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v_toConstantVal_3950_; lean_object* v_name_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v_toConstantVal_3950_ = lean_ctor_get(v_val_3946_, 0);
lean_inc_ref(v_toConstantVal_3950_);
lean_dec_ref(v_val_3946_);
v_name_3951_ = lean_ctor_get(v_toConstantVal_3950_, 0);
lean_inc(v_name_3951_);
lean_dec_ref(v_toConstantVal_3950_);
v___x_3952_ = l_Lean_mkCasesOnName(v_name_3951_);
lean_inc_ref(v_env_3917_);
v___x_3953_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_3917_, v___x_3952_);
if (lean_obj_tag(v___x_3953_) == 0)
{
if (v___x_3903_ == 0)
{
size_t v_sz_3954_; size_t v___x_3955_; lean_object* v___x_3956_; 
lean_dec_ref(v_env_3917_);
lean_del_object(v___x_3909_);
v_sz_3954_ = lean_array_size(v_alts_3875_);
v___x_3955_ = ((size_t)0ULL);
lean_inc_ref(v_alts_3875_);
v___x_3956_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v_sz_3954_, v___x_3955_, v_alts_3875_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3979_; 
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3959_ = v___x_3956_;
v_isShared_3960_ = v_isSharedCheck_3979_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3956_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3979_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
size_t v___x_3969_; size_t v___x_3970_; uint8_t v___x_3971_; 
v___x_3969_ = lean_ptr_addr(v_alts_3875_);
lean_dec_ref(v_alts_3875_);
v___x_3970_ = lean_ptr_addr(v_a_3957_);
v___x_3971_ = lean_usize_dec_eq(v___x_3969_, v___x_3970_);
if (v___x_3971_ == 0)
{
lean_del_object(v___x_3914_);
lean_dec_ref(v_resultType_3873_);
lean_dec_ref_known(v_code_3573_, 1);
goto v___jp_3961_;
}
else
{
size_t v___x_3972_; size_t v___x_3973_; uint8_t v___x_3974_; 
v___x_3972_ = lean_ptr_addr(v_resultType_3873_);
lean_dec_ref(v_resultType_3873_);
v___x_3973_ = lean_ptr_addr(v_a_3912_);
v___x_3974_ = lean_usize_dec_eq(v___x_3972_, v___x_3973_);
if (v___x_3974_ == 0)
{
lean_del_object(v___x_3914_);
lean_dec_ref_known(v_code_3573_, 1);
goto v___jp_3961_;
}
else
{
uint8_t v___x_3975_; 
v___x_3975_ = l_Lean_instBEqFVarId_beq(v_discr_3874_, v_discr_3874_);
if (v___x_3975_ == 0)
{
lean_del_object(v___x_3914_);
lean_dec_ref_known(v_code_3573_, 1);
goto v___jp_3961_;
}
else
{
lean_object* v___x_3977_; 
lean_del_object(v___x_3959_);
lean_dec(v_a_3957_);
lean_del_object(v___x_3948_);
lean_dec(v_a_3912_);
lean_dec(v_discr_3874_);
lean_dec(v_typeName_3872_);
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 0, v_code_3573_);
v___x_3977_ = v___x_3914_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_code_3573_);
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
v___jp_3961_:
{
lean_object* v___x_3962_; lean_object* v___x_3964_; 
v___x_3962_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3962_, 0, v_typeName_3872_);
lean_ctor_set(v___x_3962_, 1, v_a_3912_);
lean_ctor_set(v___x_3962_, 2, v_discr_3874_);
lean_ctor_set(v___x_3962_, 3, v_a_3957_);
if (v_isShared_3949_ == 0)
{
lean_ctor_set_tag(v___x_3948_, 4);
lean_ctor_set(v___x_3948_, 0, v___x_3962_);
v___x_3964_ = v___x_3948_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v___x_3962_);
v___x_3964_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
lean_object* v___x_3966_; 
if (v_isShared_3960_ == 0)
{
lean_ctor_set(v___x_3959_, 0, v___x_3964_);
v___x_3966_ = v___x_3959_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v___x_3964_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
}
}
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_del_object(v___x_3948_);
lean_del_object(v___x_3914_);
lean_dec(v_a_3912_);
lean_dec_ref(v_alts_3875_);
lean_dec(v_discr_3874_);
lean_dec_ref(v_resultType_3873_);
lean_dec(v_typeName_3872_);
lean_dec_ref_known(v_code_3573_, 1);
v_a_3980_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3956_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3956_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
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
lean_del_object(v___x_3948_);
lean_del_object(v___x_3914_);
lean_dec_ref(v_resultType_3873_);
lean_dec_ref_known(v_code_3573_, 1);
goto v___jp_3918_;
}
}
else
{
lean_dec_ref_known(v___x_3953_, 1);
lean_del_object(v___x_3948_);
lean_del_object(v___x_3914_);
lean_dec_ref(v_resultType_3873_);
lean_dec_ref_known(v_code_3573_, 1);
goto v___jp_3918_;
}
}
}
else
{
lean_dec(v_val_3945_);
lean_dec_ref(v_env_3917_);
lean_del_object(v___x_3914_);
lean_dec(v_a_3912_);
lean_del_object(v___x_3909_);
lean_dec_ref(v_alts_3875_);
lean_dec(v_discr_3874_);
lean_dec_ref(v_resultType_3873_);
lean_dec(v_typeName_3872_);
lean_dec_ref_known(v_code_3573_, 1);
v___y_3690_ = v_a_3574_;
v___y_3691_ = v_a_3575_;
v___y_3692_ = v_a_3576_;
v___y_3693_ = v_a_3577_;
v___y_3694_ = v_a_3578_;
goto v___jp_3689_;
}
}
else
{
lean_dec(v___x_3944_);
lean_dec_ref(v_env_3917_);
lean_del_object(v___x_3914_);
lean_dec(v_a_3912_);
lean_del_object(v___x_3909_);
lean_dec_ref(v_alts_3875_);
lean_dec(v_discr_3874_);
lean_dec_ref(v_resultType_3873_);
lean_dec(v_typeName_3872_);
lean_dec_ref_known(v_code_3573_, 1);
v___y_3690_ = v_a_3574_;
v___y_3691_ = v_a_3575_;
v___y_3692_ = v_a_3576_;
v___y_3693_ = v_a_3577_;
v___y_3694_ = v_a_3578_;
goto v___jp_3689_;
}
v___jp_3918_:
{
size_t v_sz_3919_; size_t v___x_3920_; lean_object* v___x_3921_; 
v_sz_3919_ = lean_array_size(v_alts_3875_);
v___x_3920_ = ((size_t)0ULL);
v___x_3921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(v_env_3917_, v___x_3903_, v_sz_3919_, v___x_3920_, v_alts_3875_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3935_; 
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3924_ = v___x_3921_;
v_isShared_3925_ = v_isSharedCheck_3935_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3921_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3935_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3929_; 
v___x_3926_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4));
v___x_3927_ = l_Lean_Name_append(v_typeName_3872_, v___x_3926_);
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 3, v_a_3922_);
lean_ctor_set(v___x_3909_, 1, v_a_3912_);
lean_ctor_set(v___x_3909_, 0, v___x_3927_);
v___x_3929_ = v___x_3909_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3927_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v_a_3912_);
lean_ctor_set(v_reuseFailAlloc_3934_, 2, v_discr_3874_);
lean_ctor_set(v_reuseFailAlloc_3934_, 3, v_a_3922_);
v___x_3929_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
lean_object* v___x_3930_; lean_object* v___x_3932_; 
v___x_3930_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3929_);
if (v_isShared_3925_ == 0)
{
lean_ctor_set(v___x_3924_, 0, v___x_3930_);
v___x_3932_ = v___x_3924_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v___x_3930_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
else
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
lean_dec(v_a_3912_);
lean_del_object(v___x_3909_);
lean_dec(v_discr_3874_);
lean_dec(v_typeName_3872_);
v_a_3936_ = lean_ctor_get(v___x_3921_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___x_3921_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3921_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
}
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_del_object(v___x_3909_);
lean_dec_ref(v_alts_3875_);
lean_dec(v_discr_3874_);
lean_dec_ref(v_resultType_3873_);
lean_dec(v_typeName_3872_);
lean_dec_ref_known(v_code_3573_, 1);
v_a_3990_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3911_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3911_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
}
}
else
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4010_; 
lean_dec_ref_known(v_code_3573_, 1);
lean_dec_ref(v_cases_3871_);
v_a_4003_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4005_ = v___x_3904_;
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___x_3904_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4008_; 
if (v_isShared_4006_ == 0)
{
v___x_4008_ = v___x_4005_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
}
else
{
lean_object* v___x_4011_; 
lean_dec_ref_known(v_code_3573_, 1);
v___x_4011_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_cases_3871_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
return v___x_4011_;
}
}
else
{
lean_object* v___x_4012_; 
lean_dec_ref_known(v_code_3573_, 1);
v___x_4012_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_cases_3871_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
lean_dec_ref(v_cases_3871_);
return v___x_4012_;
}
}
else
{
lean_object* v___x_4013_; 
lean_dec_ref_known(v_code_3573_, 1);
v___x_4013_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_cases_3871_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
return v___x_4013_;
}
}
else
{
lean_object* v___x_4014_; 
lean_dec_ref_known(v_code_3573_, 1);
v___x_4014_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_cases_3871_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
return v___x_4014_;
}
}
else
{
lean_object* v___x_4015_; 
lean_dec_ref_known(v_code_3573_, 1);
v___x_4015_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_cases_3871_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
return v___x_4015_;
}
}
else
{
lean_object* v___x_4016_; 
lean_dec_ref_known(v_code_3573_, 1);
v___x_4016_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_cases_3871_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
return v___x_4016_;
}
}
else
{
lean_object* v___x_4017_; 
lean_dec_ref_known(v_code_3573_, 1);
v___x_4017_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_cases_3871_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
return v___x_4017_;
}
}
else
{
lean_object* v___x_4018_; 
lean_dec_ref_known(v_code_3573_, 1);
v___x_4018_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_cases_3871_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
return v___x_4018_;
}
}
else
{
lean_object* v___x_4019_; 
lean_dec_ref_known(v_code_3573_, 1);
v___x_4019_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3871_, v___x_3886_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
return v___x_4019_;
}
}
else
{
lean_object* v___x_4020_; 
lean_dec_ref_known(v_code_3573_, 1);
v___x_4020_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3871_, v___x_3884_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
return v___x_4020_;
}
}
else
{
lean_object* v___x_4021_; 
lean_dec_ref_known(v_code_3573_, 1);
v___x_4021_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3871_, v___x_3882_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
return v___x_4021_;
}
}
else
{
lean_object* v___x_4022_; 
lean_dec_ref_known(v_code_3573_, 1);
v___x_4022_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3871_, v___x_3880_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
return v___x_4022_;
}
}
else
{
lean_object* v___x_4023_; 
lean_dec_ref_known(v_code_3573_, 1);
v___x_4023_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_cases_3871_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
return v___x_4023_;
}
}
else
{
lean_object* v___x_4024_; 
lean_dec_ref_known(v_code_3573_, 1);
v___x_4024_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_cases_3871_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
return v___x_4024_;
}
}
case 5:
{
lean_object* v___x_4025_; 
v___x_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4025_, 0, v_code_3573_);
return v___x_4025_;
}
case 6:
{
lean_object* v_type_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4050_; 
v_type_4026_ = lean_ctor_get(v_code_3573_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v_code_3573_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4028_ = v_code_3573_;
v_isShared_4029_ = v_isSharedCheck_4050_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_type_4026_);
lean_dec(v_code_3573_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4050_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4030_; 
v___x_4030_ = l_Lean_Compiler_LCNF_toMonoType(v_type_4026_, v_a_3577_, v_a_3578_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4041_; 
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4033_ = v___x_4030_;
v_isShared_4034_ = v_isSharedCheck_4041_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_4030_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4041_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4036_; 
if (v_isShared_4029_ == 0)
{
lean_ctor_set(v___x_4028_, 0, v_a_4031_);
v___x_4036_ = v___x_4028_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4031_);
v___x_4036_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
lean_object* v___x_4038_; 
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 0, v___x_4036_);
v___x_4038_ = v___x_4033_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v___x_4036_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
else
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
lean_del_object(v___x_4028_);
v_a_4042_ = lean_ctor_get(v___x_4030_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_4030_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4030_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
}
default: 
{
lean_object* v_decl_4051_; lean_object* v_k_4052_; 
v_decl_4051_ = lean_ctor_get(v_code_3573_, 0);
v_k_4052_ = lean_ctor_get(v_code_3573_, 1);
lean_inc_ref(v_k_4052_);
lean_inc_ref(v_decl_4051_);
v_decl_3581_ = v_decl_4051_;
v_k_3582_ = v_k_4052_;
v___y_3583_ = v_a_3574_;
v___y_3584_ = v_a_3575_;
v___y_3585_ = v_a_3576_;
v___y_3586_ = v_a_3577_;
v___y_3587_ = v_a_3578_;
goto v___jp_3580_;
}
}
v___jp_3580_:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_3581_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3590_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref_known(v___x_3588_, 1);
v___x_3590_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
if (lean_obj_tag(v___x_3590_) == 0)
{
switch(lean_obj_tag(v_code_3573_))
{
case 1:
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3630_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3593_ = v___x_3590_;
v_isShared_3594_ = v_isSharedCheck_3630_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3590_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3630_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v_decl_3595_; lean_object* v_k_3596_; size_t v___x_3597_; size_t v___x_3598_; uint8_t v___x_3599_; 
v_decl_3595_ = lean_ctor_get(v_code_3573_, 0);
v_k_3596_ = lean_ctor_get(v_code_3573_, 1);
v___x_3597_ = lean_ptr_addr(v_k_3596_);
v___x_3598_ = lean_ptr_addr(v_a_3591_);
v___x_3599_ = lean_usize_dec_eq(v___x_3597_, v___x_3598_);
if (v___x_3599_ == 0)
{
lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3609_; 
v_isSharedCheck_3609_ = !lean_is_exclusive(v_code_3573_);
if (v_isSharedCheck_3609_ == 0)
{
lean_object* v_unused_3610_; lean_object* v_unused_3611_; 
v_unused_3610_ = lean_ctor_get(v_code_3573_, 1);
lean_dec(v_unused_3610_);
v_unused_3611_ = lean_ctor_get(v_code_3573_, 0);
lean_dec(v_unused_3611_);
v___x_3601_ = v_code_3573_;
v_isShared_3602_ = v_isSharedCheck_3609_;
goto v_resetjp_3600_;
}
else
{
lean_dec(v_code_3573_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3609_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
lean_ctor_set(v___x_3601_, 1, v_a_3591_);
lean_ctor_set(v___x_3601_, 0, v_a_3589_);
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3589_);
lean_ctor_set(v_reuseFailAlloc_3608_, 1, v_a_3591_);
v___x_3604_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
lean_object* v___x_3606_; 
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 0, v___x_3604_);
v___x_3606_ = v___x_3593_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3604_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
else
{
size_t v___x_3612_; size_t v___x_3613_; uint8_t v___x_3614_; 
v___x_3612_ = lean_ptr_addr(v_decl_3595_);
v___x_3613_ = lean_ptr_addr(v_a_3589_);
v___x_3614_ = lean_usize_dec_eq(v___x_3612_, v___x_3613_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3624_; 
v_isSharedCheck_3624_ = !lean_is_exclusive(v_code_3573_);
if (v_isSharedCheck_3624_ == 0)
{
lean_object* v_unused_3625_; lean_object* v_unused_3626_; 
v_unused_3625_ = lean_ctor_get(v_code_3573_, 1);
lean_dec(v_unused_3625_);
v_unused_3626_ = lean_ctor_get(v_code_3573_, 0);
lean_dec(v_unused_3626_);
v___x_3616_ = v_code_3573_;
v_isShared_3617_ = v_isSharedCheck_3624_;
goto v_resetjp_3615_;
}
else
{
lean_dec(v_code_3573_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3624_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 1, v_a_3591_);
lean_ctor_set(v___x_3616_, 0, v_a_3589_);
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3589_);
lean_ctor_set(v_reuseFailAlloc_3623_, 1, v_a_3591_);
v___x_3619_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
lean_object* v___x_3621_; 
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 0, v___x_3619_);
v___x_3621_ = v___x_3593_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3619_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
else
{
lean_object* v___x_3628_; 
lean_dec(v_a_3591_);
lean_dec(v_a_3589_);
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 0, v_code_3573_);
v___x_3628_ = v___x_3593_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_code_3573_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
}
case 2:
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3670_; 
v_a_3631_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3633_ = v___x_3590_;
v_isShared_3634_ = v_isSharedCheck_3670_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3590_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3670_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v_decl_3635_; lean_object* v_k_3636_; size_t v___x_3637_; size_t v___x_3638_; uint8_t v___x_3639_; 
v_decl_3635_ = lean_ctor_get(v_code_3573_, 0);
v_k_3636_ = lean_ctor_get(v_code_3573_, 1);
v___x_3637_ = lean_ptr_addr(v_k_3636_);
v___x_3638_ = lean_ptr_addr(v_a_3631_);
v___x_3639_ = lean_usize_dec_eq(v___x_3637_, v___x_3638_);
if (v___x_3639_ == 0)
{
lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3649_; 
v_isSharedCheck_3649_ = !lean_is_exclusive(v_code_3573_);
if (v_isSharedCheck_3649_ == 0)
{
lean_object* v_unused_3650_; lean_object* v_unused_3651_; 
v_unused_3650_ = lean_ctor_get(v_code_3573_, 1);
lean_dec(v_unused_3650_);
v_unused_3651_ = lean_ctor_get(v_code_3573_, 0);
lean_dec(v_unused_3651_);
v___x_3641_ = v_code_3573_;
v_isShared_3642_ = v_isSharedCheck_3649_;
goto v_resetjp_3640_;
}
else
{
lean_dec(v_code_3573_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3649_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3644_; 
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 1, v_a_3631_);
lean_ctor_set(v___x_3641_, 0, v_a_3589_);
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3589_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v_a_3631_);
v___x_3644_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
lean_object* v___x_3646_; 
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 0, v___x_3644_);
v___x_3646_ = v___x_3633_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3644_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
else
{
size_t v___x_3652_; size_t v___x_3653_; uint8_t v___x_3654_; 
v___x_3652_ = lean_ptr_addr(v_decl_3635_);
v___x_3653_ = lean_ptr_addr(v_a_3589_);
v___x_3654_ = lean_usize_dec_eq(v___x_3652_, v___x_3653_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3664_; 
v_isSharedCheck_3664_ = !lean_is_exclusive(v_code_3573_);
if (v_isSharedCheck_3664_ == 0)
{
lean_object* v_unused_3665_; lean_object* v_unused_3666_; 
v_unused_3665_ = lean_ctor_get(v_code_3573_, 1);
lean_dec(v_unused_3665_);
v_unused_3666_ = lean_ctor_get(v_code_3573_, 0);
lean_dec(v_unused_3666_);
v___x_3656_ = v_code_3573_;
v_isShared_3657_ = v_isSharedCheck_3664_;
goto v_resetjp_3655_;
}
else
{
lean_dec(v_code_3573_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3664_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3659_; 
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 1, v_a_3631_);
lean_ctor_set(v___x_3656_, 0, v_a_3589_);
v___x_3659_ = v___x_3656_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3589_);
lean_ctor_set(v_reuseFailAlloc_3663_, 1, v_a_3631_);
v___x_3659_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
lean_object* v___x_3661_; 
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 0, v___x_3659_);
v___x_3661_ = v___x_3633_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
}
else
{
lean_object* v___x_3668_; 
lean_dec(v_a_3631_);
lean_dec(v_a_3589_);
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 0, v_code_3573_);
v___x_3668_ = v___x_3633_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_code_3573_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
}
default: 
{
lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3679_; 
lean_dec(v_a_3589_);
lean_dec_ref(v_code_3573_);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3679_ == 0)
{
lean_object* v_unused_3680_; 
v_unused_3680_ = lean_ctor_get(v___x_3590_, 0);
lean_dec(v_unused_3680_);
v___x_3672_ = v___x_3590_;
v_isShared_3673_ = v_isSharedCheck_3679_;
goto v_resetjp_3671_;
}
else
{
lean_dec(v___x_3590_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3679_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3677_; 
v___x_3674_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__2, &l_Lean_Compiler_LCNF_Code_toMono___closed__2_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__2);
v___x_3675_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__2(v___x_3674_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v___x_3675_);
v___x_3677_ = v___x_3672_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3675_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
}
else
{
lean_dec(v_a_3589_);
lean_dec_ref(v_code_3573_);
return v___x_3590_;
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_dec_ref(v_k_3582_);
lean_dec_ref(v_code_3573_);
v_a_3681_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3588_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3588_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
v___jp_3689_:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3695_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__4, &l_Lean_Compiler_LCNF_Code_toMono___closed__4_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__4);
v___x_3696_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3695_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
return v___x_3696_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono(lean_object* v_decl_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_){
_start:
{
lean_object* v_params_4060_; lean_object* v_type_4061_; lean_object* v_value_4062_; lean_object* v___x_4063_; 
v_params_4060_ = lean_ctor_get(v_decl_4053_, 2);
v_type_4061_ = lean_ctor_get(v_decl_4053_, 3);
v_value_4062_ = lean_ctor_get(v_decl_4053_, 4);
lean_inc_ref(v_type_4061_);
v___x_4063_ = l_Lean_Compiler_LCNF_toMonoType(v_type_4061_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; size_t v_sz_4065_; size_t v___x_4066_; lean_object* v___x_4067_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
lean_inc(v_a_4064_);
lean_dec_ref_known(v___x_4063_, 1);
v_sz_4065_ = lean_array_size(v_params_4060_);
v___x_4066_ = ((size_t)0ULL);
lean_inc_ref(v_params_4060_);
v___x_4067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_4065_, v___x_4066_, v_params_4060_, v_a_4054_, v_a_4056_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v_a_4068_; lean_object* v___x_4069_; 
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
lean_inc(v_a_4068_);
lean_dec_ref_known(v___x_4067_, 1);
lean_inc_ref(v_value_4062_);
v___x_4069_ = l_Lean_Compiler_LCNF_Code_toMono(v_value_4062_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_a_4070_; uint8_t v___x_4071_; lean_object* v___x_4072_; 
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc(v_a_4070_);
lean_dec_ref_known(v___x_4069_, 1);
v___x_4071_ = 0;
v___x_4072_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_4071_, v_decl_4053_, v_a_4064_, v_a_4068_, v_a_4070_, v_a_4056_);
return v___x_4072_;
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_dec(v_a_4068_);
lean_dec(v_a_4064_);
lean_dec_ref(v_decl_4053_);
v_a_4073_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4069_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4069_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_dec(v_a_4064_);
lean_dec_ref(v_decl_4053_);
v_a_4081_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4067_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4067_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
lean_dec_ref(v_decl_4053_);
v_a_4089_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4063_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4063_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono___boxed(lean_object* v_decl_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_){
_start:
{
lean_object* v_res_4104_; 
v_res_4104_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
lean_dec(v_a_4102_);
lean_dec_ref(v_a_4101_);
lean_dec(v_a_4100_);
lean_dec_ref(v_a_4099_);
lean_dec(v_a_4098_);
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___boxed(lean_object* v_sz_4105_, lean_object* v_i_4106_, lean_object* v_bs_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
size_t v_sz_boxed_4114_; size_t v_i_boxed_4115_; lean_object* v_res_4116_; 
v_sz_boxed_4114_ = lean_unbox_usize(v_sz_4105_);
lean_dec(v_sz_4105_);
v_i_boxed_4115_ = lean_unbox_usize(v_i_4106_);
lean_dec(v_i_4106_);
v_res_4116_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v_sz_boxed_4114_, v_i_boxed_4115_, v_bs_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___boxed(lean_object* v_c_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_){
_start:
{
lean_object* v_res_4124_; 
v_res_4124_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_);
lean_dec(v_a_4122_);
lean_dec_ref(v_a_4121_);
lean_dec(v_a_4120_);
lean_dec_ref(v_a_4119_);
lean_dec(v_a_4118_);
return v_res_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___boxed(lean_object* v_c_4125_, lean_object* v_uintName_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_){
_start:
{
lean_object* v_res_4133_; 
v_res_4133_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_4125_, v_uintName_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_);
lean_dec(v_a_4131_);
lean_dec_ref(v_a_4130_);
lean_dec(v_a_4129_);
lean_dec_ref(v_a_4128_);
lean_dec(v_a_4127_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___boxed(lean_object* v_c_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_){
_start:
{
lean_object* v_res_4141_; 
v_res_4141_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_);
lean_dec(v_a_4139_);
lean_dec_ref(v_a_4138_);
lean_dec(v_a_4137_);
lean_dec_ref(v_a_4136_);
lean_dec(v_a_4135_);
return v_res_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___boxed(lean_object* v_c_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_){
_start:
{
lean_object* v_res_4149_; 
v_res_4149_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_c_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_);
lean_dec(v_a_4147_);
lean_dec_ref(v_a_4146_);
lean_dec(v_a_4145_);
lean_dec_ref(v_a_4144_);
lean_dec(v_a_4143_);
return v_res_4149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___boxed(lean_object* v_c_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_4150_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_);
lean_dec(v_a_4155_);
lean_dec_ref(v_a_4154_);
lean_dec(v_a_4153_);
lean_dec_ref(v_a_4152_);
lean_dec(v_a_4151_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg___boxed(lean_object* v_c_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_){
_start:
{
lean_object* v_res_4165_; 
v_res_4165_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_c_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
lean_dec(v_a_4163_);
lean_dec_ref(v_a_4162_);
lean_dec(v_a_4161_);
lean_dec_ref(v_a_4160_);
lean_dec(v_a_4159_);
return v_res_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___boxed(lean_object* v_c_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_){
_start:
{
lean_object* v_res_4173_; 
v_res_4173_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_);
lean_dec(v_a_4171_);
lean_dec_ref(v_a_4170_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
return v_res_4173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___boxed(lean_object* v___x_4174_, lean_object* v___x_4175_, lean_object* v_sz_4176_, lean_object* v_i_4177_, lean_object* v_bs_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
uint8_t v___x_33922__boxed_4185_; size_t v_sz_boxed_4186_; size_t v_i_boxed_4187_; lean_object* v_res_4188_; 
v___x_33922__boxed_4185_ = lean_unbox(v___x_4175_);
v_sz_boxed_4186_ = lean_unbox_usize(v_sz_4176_);
lean_dec(v_sz_4176_);
v_i_boxed_4187_ = lean_unbox_usize(v_i_4177_);
lean_dec(v_i_4177_);
v_res_4188_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(v___x_4174_, v___x_33922__boxed_4185_, v_sz_boxed_4186_, v_i_boxed_4187_, v_bs_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec(v___y_4179_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___boxed(lean_object* v_c_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_){
_start:
{
lean_object* v_res_4196_; 
v_res_4196_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_);
lean_dec(v_a_4194_);
lean_dec_ref(v_a_4193_);
lean_dec(v_a_4192_);
lean_dec_ref(v_a_4191_);
lean_dec(v_a_4190_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___boxed(lean_object* v_c_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_){
_start:
{
lean_object* v_res_4204_; 
v_res_4204_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_);
lean_dec(v_a_4202_);
lean_dec_ref(v_a_4201_);
lean_dec(v_a_4200_);
lean_dec_ref(v_a_4199_);
lean_dec(v_a_4198_);
return v_res_4204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___boxed(lean_object* v_c_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_){
_start:
{
lean_object* v_res_4212_; 
v_res_4212_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_);
lean_dec(v_a_4210_);
lean_dec_ref(v_a_4209_);
lean_dec(v_a_4208_);
lean_dec_ref(v_a_4207_);
lean_dec(v_a_4206_);
return v_res_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___boxed(lean_object* v_info_4213_, lean_object* v_c_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_info_4213_, v_c_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
lean_dec(v_a_4219_);
lean_dec_ref(v_a_4218_);
lean_dec(v_a_4217_);
lean_dec_ref(v_a_4216_);
lean_dec(v_a_4215_);
lean_dec_ref(v_info_4213_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___boxed(lean_object* v___x_4222_, lean_object* v_sz_4223_, lean_object* v_i_4224_, lean_object* v_bs_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_){
_start:
{
size_t v_sz_boxed_4232_; size_t v_i_boxed_4233_; lean_object* v_res_4234_; 
v_sz_boxed_4232_ = lean_unbox_usize(v_sz_4223_);
lean_dec(v_sz_4223_);
v_i_boxed_4233_ = lean_unbox_usize(v_i_4224_);
lean_dec(v_i_4224_);
v_res_4234_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(v___x_4222_, v_sz_boxed_4232_, v_i_boxed_4233_, v_bs_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_);
lean_dec(v___y_4230_);
lean_dec_ref(v___y_4229_);
lean_dec(v___y_4228_);
lean_dec_ref(v___y_4227_);
lean_dec(v___y_4226_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___boxed(lean_object* v_c_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_);
lean_dec(v_a_4240_);
lean_dec_ref(v_a_4239_);
lean_dec(v_a_4238_);
lean_dec_ref(v_a_4237_);
lean_dec(v_a_4236_);
lean_dec_ref(v_c_4235_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___boxed(lean_object* v___x_4243_, lean_object* v_sz_4244_, lean_object* v_i_4245_, lean_object* v_bs_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_){
_start:
{
size_t v_sz_boxed_4253_; size_t v_i_boxed_4254_; lean_object* v_res_4255_; 
v_sz_boxed_4253_ = lean_unbox_usize(v_sz_4244_);
lean_dec(v_sz_4244_);
v_i_boxed_4254_ = lean_unbox_usize(v_i_4245_);
lean_dec(v_i_4245_);
v_res_4255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(v___x_4243_, v_sz_boxed_4253_, v_i_boxed_4254_, v_bs_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
lean_dec(v___y_4247_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono___boxed(lean_object* v_code_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_){
_start:
{
lean_object* v_res_4263_; 
v_res_4263_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_4256_, v_a_4257_, v_a_4258_, v_a_4259_, v_a_4260_, v_a_4261_);
lean_dec(v_a_4261_);
lean_dec_ref(v_a_4260_);
lean_dec(v_a_4259_);
lean_dec_ref(v_a_4258_);
lean_dec(v_a_4257_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono(lean_object* v_c_4264_, lean_object* v_x_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_){
_start:
{
lean_object* v___x_4272_; 
v___x_4272_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_4264_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___boxed(lean_object* v_c_4273_, lean_object* v_x_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l_Lean_Compiler_LCNF_casesTaskToMono(v_c_4273_, v_x_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_);
lean_dec(v_a_4279_);
lean_dec_ref(v_a_4278_);
lean_dec(v_a_4277_);
lean_dec_ref(v_a_4276_);
lean_dec(v_a_4275_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono(lean_object* v_c_4282_, lean_object* v_x_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_){
_start:
{
lean_object* v___x_4290_; 
v___x_4290_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_4282_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_);
return v___x_4290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___boxed(lean_object* v_c_4291_, lean_object* v_x_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_){
_start:
{
lean_object* v_res_4299_; 
v_res_4299_ = l_Lean_Compiler_LCNF_casesThunkToMono(v_c_4291_, v_x_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_);
lean_dec(v_a_4297_);
lean_dec_ref(v_a_4296_);
lean_dec(v_a_4295_);
lean_dec_ref(v_a_4294_);
lean_dec(v_a_4293_);
lean_dec_ref(v_c_4291_);
return v_res_4299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono(lean_object* v_c_4300_, lean_object* v_x_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_){
_start:
{
lean_object* v___x_4308_; 
v___x_4308_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_c_4300_, v_a_4302_, v_a_4303_, v_a_4304_, v_a_4305_, v_a_4306_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___boxed(lean_object* v_c_4309_, lean_object* v_x_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_){
_start:
{
lean_object* v_res_4317_; 
v_res_4317_ = l_Lean_Compiler_LCNF_casesFloat32ToMono(v_c_4309_, v_x_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_);
lean_dec(v_a_4315_);
lean_dec_ref(v_a_4314_);
lean_dec(v_a_4313_);
lean_dec_ref(v_a_4312_);
lean_dec(v_a_4311_);
return v_res_4317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono(lean_object* v_c_4318_, lean_object* v_x_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_){
_start:
{
lean_object* v___x_4326_; 
v___x_4326_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_c_4318_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_);
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___boxed(lean_object* v_c_4327_, lean_object* v_x_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l_Lean_Compiler_LCNF_casesFloatToMono(v_c_4327_, v_x_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_);
lean_dec(v_a_4333_);
lean_dec_ref(v_a_4332_);
lean_dec(v_a_4331_);
lean_dec_ref(v_a_4330_);
lean_dec(v_a_4329_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono(lean_object* v_c_4336_, lean_object* v_x_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_){
_start:
{
lean_object* v___x_4344_; 
v___x_4344_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_4336_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_);
return v___x_4344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___boxed(lean_object* v_c_4345_, lean_object* v_x_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_){
_start:
{
lean_object* v_res_4353_; 
v_res_4353_ = l_Lean_Compiler_LCNF_casesStringToMono(v_c_4345_, v_x_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
lean_dec(v_a_4351_);
lean_dec_ref(v_a_4350_);
lean_dec(v_a_4349_);
lean_dec_ref(v_a_4348_);
lean_dec(v_a_4347_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono(lean_object* v_c_4354_, lean_object* v_x_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_){
_start:
{
lean_object* v___x_4362_; 
v___x_4362_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_4354_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_);
return v___x_4362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___boxed(lean_object* v_c_4363_, lean_object* v_x_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono(v_c_4363_, v_x_4364_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_);
lean_dec(v_a_4369_);
lean_dec_ref(v_a_4368_);
lean_dec(v_a_4367_);
lean_dec_ref(v_a_4366_);
lean_dec(v_a_4365_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono(lean_object* v_c_4372_, lean_object* v_x_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_){
_start:
{
lean_object* v___x_4380_; 
v___x_4380_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_4372_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___boxed(lean_object* v_c_4381_, lean_object* v_x_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_){
_start:
{
lean_object* v_res_4389_; 
v_res_4389_ = l_Lean_Compiler_LCNF_casesByteArrayToMono(v_c_4381_, v_x_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_);
lean_dec(v_a_4387_);
lean_dec_ref(v_a_4386_);
lean_dec(v_a_4385_);
lean_dec_ref(v_a_4384_);
lean_dec(v_a_4383_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono(lean_object* v_c_4390_, lean_object* v_x_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_){
_start:
{
lean_object* v___x_4398_; 
v___x_4398_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_4390_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___boxed(lean_object* v_c_4399_, lean_object* v_x_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_){
_start:
{
lean_object* v_res_4407_; 
v_res_4407_ = l_Lean_Compiler_LCNF_casesArrayToMono(v_c_4399_, v_x_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_);
lean_dec(v_a_4405_);
lean_dec_ref(v_a_4404_);
lean_dec(v_a_4403_);
lean_dec_ref(v_a_4402_);
lean_dec(v_a_4401_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono(lean_object* v_c_4408_, lean_object* v_uintName_4409_, lean_object* v_x_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_){
_start:
{
lean_object* v___x_4417_; 
v___x_4417_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_4408_, v_uintName_4409_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_, v_a_4415_);
return v___x_4417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___boxed(lean_object* v_c_4418_, lean_object* v_uintName_4419_, lean_object* v_x_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l_Lean_Compiler_LCNF_casesUIntToMono(v_c_4418_, v_uintName_4419_, v_x_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_);
lean_dec(v_a_4425_);
lean_dec_ref(v_a_4424_);
lean_dec(v_a_4423_);
lean_dec_ref(v_a_4422_);
lean_dec(v_a_4421_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono(lean_object* v_c_4428_, lean_object* v_x_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_){
_start:
{
lean_object* v___x_4436_; 
v___x_4436_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_4428_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_, v_a_4434_);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___boxed(lean_object* v_c_4437_, lean_object* v_x_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l_Lean_Compiler_LCNF_casesIntToMono(v_c_4437_, v_x_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_);
lean_dec(v_a_4443_);
lean_dec_ref(v_a_4442_);
lean_dec(v_a_4441_);
lean_dec_ref(v_a_4440_);
lean_dec(v_a_4439_);
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono(lean_object* v_c_4446_, lean_object* v_x_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_){
_start:
{
lean_object* v___x_4454_; 
v___x_4454_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_4446_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_);
return v___x_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___boxed(lean_object* v_c_4455_, lean_object* v_x_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l_Lean_Compiler_LCNF_casesNatToMono(v_c_4455_, v_x_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
lean_dec(v_a_4461_);
lean_dec_ref(v_a_4460_);
lean_dec(v_a_4459_);
lean_dec_ref(v_a_4458_);
lean_dec(v_a_4457_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(size_t v_sz_4464_, size_t v_i_4465_, lean_object* v_bs_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_){
_start:
{
lean_object* v___x_4473_; 
v___x_4473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_4464_, v_i_4465_, v_bs_4466_, v___y_4467_, v___y_4469_, v___y_4470_, v___y_4471_);
return v___x_4473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___boxed(lean_object* v_sz_4474_, lean_object* v_i_4475_, lean_object* v_bs_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
size_t v_sz_boxed_4483_; size_t v_i_boxed_4484_; lean_object* v_res_4485_; 
v_sz_boxed_4483_ = lean_unbox_usize(v_sz_4474_);
lean_dec(v_sz_4474_);
v_i_boxed_4484_ = lean_unbox_usize(v_i_4475_);
lean_dec(v_i_4475_);
v_res_4485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(v_sz_boxed_4483_, v_i_boxed_4484_, v_bs_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v___y_4479_);
lean_dec_ref(v___y_4478_);
lean_dec(v___y_4477_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(lean_object* v_f_4486_, lean_object* v_v_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
if (lean_obj_tag(v_v_4487_) == 0)
{
lean_object* v_code_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4518_; 
v_code_4494_ = lean_ctor_get(v_v_4487_, 0);
v_isSharedCheck_4518_ = !lean_is_exclusive(v_v_4487_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4496_ = v_v_4487_;
v_isShared_4497_ = v_isSharedCheck_4518_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_code_4494_);
lean_dec(v_v_4487_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4518_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4498_; 
lean_inc(v___y_4492_);
lean_inc_ref(v___y_4491_);
lean_inc(v___y_4490_);
lean_inc_ref(v___y_4489_);
lean_inc(v___y_4488_);
v___x_4498_ = lean_apply_7(v_f_4486_, v_code_4494_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, lean_box(0));
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v_a_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4509_; 
v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4501_ = v___x_4498_;
v_isShared_4502_ = v_isSharedCheck_4509_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_a_4499_);
lean_dec(v___x_4498_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4509_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4504_; 
if (v_isShared_4497_ == 0)
{
lean_ctor_set(v___x_4496_, 0, v_a_4499_);
v___x_4504_ = v___x_4496_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4499_);
v___x_4504_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
lean_object* v___x_4506_; 
if (v_isShared_4502_ == 0)
{
lean_ctor_set(v___x_4501_, 0, v___x_4504_);
v___x_4506_ = v___x_4501_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v___x_4504_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
}
else
{
lean_object* v_a_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4517_; 
lean_del_object(v___x_4496_);
v_a_4510_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4512_ = v___x_4498_;
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_a_4510_);
lean_dec(v___x_4498_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
lean_object* v___x_4515_; 
if (v_isShared_4513_ == 0)
{
v___x_4515_ = v___x_4512_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v_a_4510_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
}
}
else
{
lean_object* v___x_4519_; 
lean_dec_ref(v_f_4486_);
v___x_4519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4519_, 0, v_v_4487_);
return v___x_4519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg___boxed(lean_object* v_f_4520_, lean_object* v_v_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_4520_, v_v_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v___y_4522_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(uint8_t v_pu_4529_, lean_object* v_f_4530_, lean_object* v_v_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_){
_start:
{
lean_object* v___x_4538_; 
v___x_4538_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_4530_, v_v_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_);
return v___x_4538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___boxed(lean_object* v_pu_4539_, lean_object* v_f_4540_, lean_object* v_v_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_){
_start:
{
uint8_t v_pu_boxed_4548_; lean_object* v_res_4549_; 
v_pu_boxed_4548_ = lean_unbox(v_pu_4539_);
v_res_4549_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(v_pu_boxed_4548_, v_f_4540_, v_v_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
lean_dec(v___y_4542_);
return v_res_4549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(lean_object* v_decl_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_){
_start:
{
lean_object* v_toSignature_4558_; lean_object* v_value_4559_; uint8_t v_recursive_4560_; lean_object* v_inlineAttr_x3f_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4631_; 
v_toSignature_4558_ = lean_ctor_get(v_decl_4551_, 0);
v_value_4559_ = lean_ctor_get(v_decl_4551_, 1);
v_recursive_4560_ = lean_ctor_get_uint8(v_decl_4551_, sizeof(void*)*3);
v_inlineAttr_x3f_4561_ = lean_ctor_get(v_decl_4551_, 2);
v_isSharedCheck_4631_ = !lean_is_exclusive(v_decl_4551_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4563_ = v_decl_4551_;
v_isShared_4564_ = v_isSharedCheck_4631_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_inlineAttr_x3f_4561_);
lean_inc(v_value_4559_);
lean_inc(v_toSignature_4558_);
lean_dec(v_decl_4551_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4631_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v_name_4565_; lean_object* v_type_4566_; lean_object* v_params_4567_; uint8_t v_safe_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4629_; 
v_name_4565_ = lean_ctor_get(v_toSignature_4558_, 0);
v_type_4566_ = lean_ctor_get(v_toSignature_4558_, 2);
v_params_4567_ = lean_ctor_get(v_toSignature_4558_, 3);
v_safe_4568_ = lean_ctor_get_uint8(v_toSignature_4558_, sizeof(void*)*4);
v_isSharedCheck_4629_ = !lean_is_exclusive(v_toSignature_4558_);
if (v_isSharedCheck_4629_ == 0)
{
lean_object* v_unused_4630_; 
v_unused_4630_ = lean_ctor_get(v_toSignature_4558_, 1);
lean_dec(v_unused_4630_);
v___x_4570_ = v_toSignature_4558_;
v_isShared_4571_ = v_isSharedCheck_4629_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_params_4567_);
lean_inc(v_type_4566_);
lean_inc(v_name_4565_);
lean_dec(v_toSignature_4558_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4629_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4572_; 
v___x_4572_ = l_Lean_Compiler_LCNF_toMonoType(v_type_4566_, v_a_4555_, v_a_4556_);
if (lean_obj_tag(v___x_4572_) == 0)
{
lean_object* v_a_4573_; size_t v_sz_4574_; size_t v___x_4575_; lean_object* v___x_4576_; 
v_a_4573_ = lean_ctor_get(v___x_4572_, 0);
lean_inc(v_a_4573_);
lean_dec_ref_known(v___x_4572_, 1);
v_sz_4574_ = lean_array_size(v_params_4567_);
v___x_4575_ = ((size_t)0ULL);
v___x_4576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_4574_, v___x_4575_, v_params_4567_, v_a_4552_, v_a_4554_, v_a_4555_, v_a_4556_);
if (lean_obj_tag(v___x_4576_) == 0)
{
lean_object* v_a_4577_; lean_object* v___f_4578_; lean_object* v___x_4579_; 
v_a_4577_ = lean_ctor_get(v___x_4576_, 0);
lean_inc(v_a_4577_);
lean_dec_ref_known(v___x_4576_, 1);
v___f_4578_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___closed__0));
v___x_4579_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v___f_4578_, v_value_4559_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_);
if (lean_obj_tag(v___x_4579_) == 0)
{
lean_object* v_a_4580_; lean_object* v___x_4581_; lean_object* v___x_4583_; 
v_a_4580_ = lean_ctor_get(v___x_4579_, 0);
lean_inc(v_a_4580_);
lean_dec_ref_known(v___x_4579_, 1);
v___x_4581_ = lean_box(0);
if (v_isShared_4571_ == 0)
{
lean_ctor_set(v___x_4570_, 3, v_a_4577_);
lean_ctor_set(v___x_4570_, 2, v_a_4573_);
lean_ctor_set(v___x_4570_, 1, v___x_4581_);
v___x_4583_ = v___x_4570_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v_name_4565_);
lean_ctor_set(v_reuseFailAlloc_4604_, 1, v___x_4581_);
lean_ctor_set(v_reuseFailAlloc_4604_, 2, v_a_4573_);
lean_ctor_set(v_reuseFailAlloc_4604_, 3, v_a_4577_);
lean_ctor_set_uint8(v_reuseFailAlloc_4604_, sizeof(void*)*4, v_safe_4568_);
v___x_4583_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
lean_object* v___x_4585_; 
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 1, v_a_4580_);
lean_ctor_set(v___x_4563_, 0, v___x_4583_);
v___x_4585_ = v___x_4563_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v___x_4583_);
lean_ctor_set(v_reuseFailAlloc_4603_, 1, v_a_4580_);
lean_ctor_set(v_reuseFailAlloc_4603_, 2, v_inlineAttr_x3f_4561_);
lean_ctor_set_uint8(v_reuseFailAlloc_4603_, sizeof(void*)*3, v_recursive_4560_);
v___x_4585_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
lean_object* v___x_4586_; 
lean_inc_ref(v___x_4585_);
v___x_4586_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_4585_, v_a_4556_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4593_; 
v_isSharedCheck_4593_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4593_ == 0)
{
lean_object* v_unused_4594_; 
v_unused_4594_ = lean_ctor_get(v___x_4586_, 0);
lean_dec(v_unused_4594_);
v___x_4588_ = v___x_4586_;
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
else
{
lean_dec(v___x_4586_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v___x_4591_; 
if (v_isShared_4589_ == 0)
{
lean_ctor_set(v___x_4588_, 0, v___x_4585_);
v___x_4591_ = v___x_4588_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v___x_4585_);
v___x_4591_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
return v___x_4591_;
}
}
}
else
{
lean_object* v_a_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4602_; 
lean_dec_ref(v___x_4585_);
v_a_4595_ = lean_ctor_get(v___x_4586_, 0);
v_isSharedCheck_4602_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4602_ == 0)
{
v___x_4597_ = v___x_4586_;
v_isShared_4598_ = v_isSharedCheck_4602_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_a_4595_);
lean_dec(v___x_4586_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4602_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
lean_object* v___x_4600_; 
if (v_isShared_4598_ == 0)
{
v___x_4600_ = v___x_4597_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_a_4595_);
v___x_4600_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
return v___x_4600_;
}
}
}
}
}
}
else
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4612_; 
lean_dec(v_a_4577_);
lean_dec(v_a_4573_);
lean_del_object(v___x_4570_);
lean_dec(v_name_4565_);
lean_del_object(v___x_4563_);
lean_dec(v_inlineAttr_x3f_4561_);
v_a_4605_ = lean_ctor_get(v___x_4579_, 0);
v_isSharedCheck_4612_ = !lean_is_exclusive(v___x_4579_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4607_ = v___x_4579_;
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v___x_4579_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4610_; 
if (v_isShared_4608_ == 0)
{
v___x_4610_ = v___x_4607_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4605_);
v___x_4610_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
return v___x_4610_;
}
}
}
}
else
{
lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4620_; 
lean_dec(v_a_4573_);
lean_del_object(v___x_4570_);
lean_dec(v_name_4565_);
lean_del_object(v___x_4563_);
lean_dec(v_inlineAttr_x3f_4561_);
lean_dec_ref(v_value_4559_);
v_a_4613_ = lean_ctor_get(v___x_4576_, 0);
v_isSharedCheck_4620_ = !lean_is_exclusive(v___x_4576_);
if (v_isSharedCheck_4620_ == 0)
{
v___x_4615_ = v___x_4576_;
v_isShared_4616_ = v_isSharedCheck_4620_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v___x_4576_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4620_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4618_; 
if (v_isShared_4616_ == 0)
{
v___x_4618_ = v___x_4615_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_a_4613_);
v___x_4618_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
return v___x_4618_;
}
}
}
}
else
{
lean_object* v_a_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4628_; 
lean_del_object(v___x_4570_);
lean_dec_ref(v_params_4567_);
lean_dec(v_name_4565_);
lean_del_object(v___x_4563_);
lean_dec(v_inlineAttr_x3f_4561_);
lean_dec_ref(v_value_4559_);
v_a_4621_ = lean_ctor_get(v___x_4572_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4623_ = v___x_4572_;
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_a_4621_);
lean_dec(v___x_4572_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v___x_4626_; 
if (v_isShared_4624_ == 0)
{
v___x_4626_ = v___x_4623_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_a_4621_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
return v___x_4626_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___boxed(lean_object* v_decl_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_){
_start:
{
lean_object* v_res_4639_; 
v_res_4639_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_4632_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_);
lean_dec(v_a_4637_);
lean_dec_ref(v_a_4636_);
lean_dec(v_a_4635_);
lean_dec_ref(v_a_4634_);
lean_dec(v_a_4633_);
return v_res_4639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono(lean_object* v_decl_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_){
_start:
{
lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4646_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_4647_ = lean_st_mk_ref(v___x_4646_);
v___x_4648_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_4640_, v___x_4647_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_);
if (lean_obj_tag(v___x_4648_) == 0)
{
lean_object* v_a_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4657_; 
v_a_4649_ = lean_ctor_get(v___x_4648_, 0);
v_isSharedCheck_4657_ = !lean_is_exclusive(v___x_4648_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4651_ = v___x_4648_;
v_isShared_4652_ = v_isSharedCheck_4657_;
goto v_resetjp_4650_;
}
else
{
lean_inc(v_a_4649_);
lean_dec(v___x_4648_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4657_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
lean_object* v___x_4653_; lean_object* v___x_4655_; 
v___x_4653_ = lean_st_ref_get(v___x_4647_);
lean_dec(v___x_4647_);
lean_dec(v___x_4653_);
if (v_isShared_4652_ == 0)
{
v___x_4655_ = v___x_4651_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4649_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
return v___x_4655_;
}
}
}
else
{
lean_dec(v___x_4647_);
return v___x_4648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono___boxed(lean_object* v_decl_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l_Lean_Compiler_LCNF_Decl_toMono(v_decl_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_);
lean_dec(v_a_4662_);
lean_dec_ref(v_a_4661_);
lean_dec(v_a_4660_);
lean_dec_ref(v_a_4659_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(size_t v_sz_4665_, size_t v_i_4666_, lean_object* v_bs_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
uint8_t v___x_4673_; 
v___x_4673_ = lean_usize_dec_lt(v_i_4666_, v_sz_4665_);
if (v___x_4673_ == 0)
{
lean_object* v___x_4674_; 
v___x_4674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4674_, 0, v_bs_4667_);
return v___x_4674_;
}
else
{
lean_object* v_v_4675_; lean_object* v___x_4676_; 
v_v_4675_ = lean_array_uget_borrowed(v_bs_4667_, v_i_4666_);
lean_inc(v_v_4675_);
v___x_4676_ = l_Lean_Compiler_LCNF_Decl_toMono(v_v_4675_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_object* v_a_4677_; lean_object* v___x_4678_; lean_object* v_bs_x27_4679_; size_t v___x_4680_; size_t v___x_4681_; lean_object* v___x_4682_; 
v_a_4677_ = lean_ctor_get(v___x_4676_, 0);
lean_inc(v_a_4677_);
lean_dec_ref_known(v___x_4676_, 1);
v___x_4678_ = lean_unsigned_to_nat(0u);
v_bs_x27_4679_ = lean_array_uset(v_bs_4667_, v_i_4666_, v___x_4678_);
v___x_4680_ = ((size_t)1ULL);
v___x_4681_ = lean_usize_add(v_i_4666_, v___x_4680_);
v___x_4682_ = lean_array_uset(v_bs_x27_4679_, v_i_4666_, v_a_4677_);
v_i_4666_ = v___x_4681_;
v_bs_4667_ = v___x_4682_;
goto _start;
}
else
{
lean_object* v_a_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4691_; 
lean_dec_ref(v_bs_4667_);
v_a_4684_ = lean_ctor_get(v___x_4676_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4686_ = v___x_4676_;
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_a_4684_);
lean_dec(v___x_4676_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
lean_object* v___x_4689_; 
if (v_isShared_4687_ == 0)
{
v___x_4689_ = v___x_4686_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_a_4684_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0___boxed(lean_object* v_sz_4692_, lean_object* v_i_4693_, lean_object* v_bs_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_){
_start:
{
size_t v_sz_boxed_4700_; size_t v_i_boxed_4701_; lean_object* v_res_4702_; 
v_sz_boxed_4700_ = lean_unbox_usize(v_sz_4692_);
lean_dec(v_sz_4692_);
v_i_boxed_4701_ = lean_unbox_usize(v_i_4693_);
lean_dec(v_i_4693_);
v_res_4702_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_boxed_4700_, v_i_boxed_4701_, v_bs_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
lean_dec(v___y_4698_);
lean_dec_ref(v___y_4697_);
lean_dec(v___y_4696_);
lean_dec_ref(v___y_4695_);
return v_res_4702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0(lean_object* v_x_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_){
_start:
{
size_t v_sz_4709_; size_t v___x_4710_; lean_object* v___x_4711_; 
v_sz_4709_ = lean_array_size(v_x_4703_);
v___x_4710_ = ((size_t)0ULL);
v___x_4711_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_4709_, v___x_4710_, v_x_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0___boxed(lean_object* v_x_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_){
_start:
{
lean_object* v_res_4718_; 
v_res_4718_ = l_Lean_Compiler_LCNF_toMono___lam__0(v_x_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_);
lean_dec(v___y_4716_);
lean_dec_ref(v___y_4715_);
lean_dec(v___y_4714_);
lean_dec_ref(v___y_4713_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4801_; uint8_t v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; 
v___x_4801_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_));
v___x_4802_ = 1;
v___x_4803_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_));
v___x_4804_ = l_Lean_registerTraceClass(v___x_4801_, v___x_4802_, v___x_4803_);
return v___x_4804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2____boxed(lean_object* v_a_4805_){
_start:
{
lean_object* v_res_4806_; 
v_res_4806_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_();
return v_res_4806_;
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
